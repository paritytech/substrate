// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Off-chain logic for creating a proof based data provided by on-chain logic.
//!
//! Validator-set extracting an iterator from an off-chain worker stored list containing
//! historical validator-sets.
//! Based on the logic of historical slashing, but the validation is done off-chain.
//! Use [`fn store_current_session_validator_set_to_offchain()`](super::onchain) to store the
//! required data to the offchain validator set.
//! This is used in conjunction with [`ProvingTrie`](super::ProvingTrie) and
//! the off-chain indexing API.

use sp_runtime::{
	offchain::storage::{MutateStorageError, StorageRetrievalError, StorageValueRef},
	KeyTypeId,
};
use sp_session::MembershipProof;
use sp_std::prelude::*;

use super::{shared, Config, IdentificationTuple, ProvingTrie};
use crate::{Pallet as SessionModule, SessionIndex};

/// A set of validators, which was used for a fixed session index.
struct ValidatorSet<T: Config> {
	validator_set: Vec<IdentificationTuple<T>>,
}

impl<T: Config> ValidatorSet<T> {
	/// Load the set of validators for a particular session index from the off-chain storage.
	///
	/// If none is found or decodable given `prefix` and `session`, it will return `None`.
	/// Empty validator sets should only ever exist for genesis blocks.
	pub fn load_from_offchain_db(session_index: SessionIndex) -> Option<Self> {
		let derived_key = shared::derive_key(shared::PREFIX, session_index);
		StorageValueRef::persistent(derived_key.as_ref())
			.get::<Vec<(T::ValidatorId, T::FullIdentification)>>()
			.ok()
			.flatten()
			.map(|validator_set| Self { validator_set })
	}

	#[inline]
	fn len(&self) -> usize {
		self.validator_set.len()
	}
}

/// Implement conversion into iterator for usage
/// with [ProvingTrie](super::ProvingTrie::generate_for).
impl<T: Config> sp_std::iter::IntoIterator for ValidatorSet<T> {
	type Item = (T::ValidatorId, T::FullIdentification);
	type IntoIter = sp_std::vec::IntoIter<Self::Item>;
	fn into_iter(self) -> Self::IntoIter {
		self.validator_set.into_iter()
	}
}

/// Create a proof based on the data available in the off-chain database.
///
/// Based on the yielded `MembershipProof` the implementer may decide what
/// to do, i.e. in case of a failed proof, enqueue a transaction back on
/// chain reflecting that, with all its consequences such as i.e. slashing.
pub fn prove_session_membership<T: Config, D: AsRef<[u8]>>(
	session_index: SessionIndex,
	session_key: (KeyTypeId, D),
) -> Option<MembershipProof> {
	let validators = ValidatorSet::<T>::load_from_offchain_db(session_index)?;
	let count = validators.len() as u32;
	let trie = ProvingTrie::<T>::generate_for(validators.into_iter()).ok()?;

	let (id, data) = session_key;
	trie.prove(id, data.as_ref()).map(|trie_nodes| MembershipProof {
		session: session_index,
		trie_nodes,
		validator_count: count,
	})
}

/// Attempt to prune anything that is older than `first_to_keep` session index.
///
/// Due to re-organisation it could be that the `first_to_keep` might be less
/// than the stored one, in which case the conservative choice is made to keep records
/// up to the one that is the lesser.
pub fn prune_older_than<T: Config>(first_to_keep: SessionIndex) {
	let derived_key = shared::LAST_PRUNE.to_vec();
	let entry = StorageValueRef::persistent(derived_key.as_ref());
	match entry.mutate(
		|current: Result<Option<SessionIndex>, StorageRetrievalError>| -> Result<_, ()> {
			match current {
				Ok(Some(current)) if current < first_to_keep => Ok(first_to_keep),
				// do not move the cursor, if the new one would be behind ours
				Ok(Some(current)) => Ok(current),
				Ok(None) => Ok(first_to_keep),
				// if the storage contains undecodable data, overwrite with current anyways
				// which might leak some entries being never purged, but that is acceptable
				// in this context
				Err(_) => Ok(first_to_keep),
			}
		},
	) {
		Ok(new_value) => {
			// on a re-org this is not necessarily true, with the above they might be equal
			if new_value < first_to_keep {
				for session_index in new_value..first_to_keep {
					let derived_key = shared::derive_key(shared::PREFIX, session_index);
					let _ = StorageValueRef::persistent(derived_key.as_ref()).clear();
				}
			}
		},
		Err(MutateStorageError::ConcurrentModification(_)) => {},
		Err(MutateStorageError::ValueFunctionFailed(_)) => {},
	}
}

/// Keep the newest `n` items, and prune all items older than that.
pub fn keep_newest<T: Config>(n_to_keep: usize) {
	let session_index = <SessionModule<T>>::current_index();
	let n_to_keep = n_to_keep as SessionIndex;
	if n_to_keep < session_index {
		prune_older_than::<T>(session_index - n_to_keep)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		historical::{onchain, Pallet},
		mock::{force_new_session, set_next_validators, NextValidators, Session, System, Test},
	};

	use codec::Encode;
	use sp_core::{
		crypto::key_types::DUMMY,
		offchain::{testing::TestOffchainExt, OffchainDbExt, OffchainWorkerExt, StorageKind},
	};
	use sp_runtime::testing::UintAuthorityId;

	use frame_support::{
		traits::{GenesisBuild, KeyOwnerProofSystem, OnInitialize},
		BasicExternalities,
	};

	type Historical = Pallet<Test>;

	pub fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default()
			.build_storage::<Test>()
			.expect("Failed to create test externalities.");

		let keys: Vec<_> = NextValidators::get()
			.iter()
			.cloned()
			.map(|i| (i, i, UintAuthorityId(i).into()))
			.collect();

		BasicExternalities::execute_with_storage(&mut t, || {
			for (ref k, ..) in &keys {
				frame_system::Pallet::<Test>::inc_providers(k);
			}
		});

		crate::GenesisConfig::<Test> { keys }.assimilate_storage(&mut t).unwrap();

		let mut ext = sp_io::TestExternalities::new(t);

		let (offchain, offchain_state) = TestOffchainExt::with_offchain_db(ext.offchain_db());

		const ITERATIONS: u32 = 5u32;
		let mut seed = [0u8; 32];
		seed[0..4].copy_from_slice(&ITERATIONS.to_le_bytes());
		offchain_state.write().seed = seed;

		ext.register_extension(OffchainDbExt::new(offchain.clone()));
		ext.register_extension(OffchainWorkerExt::new(offchain));
		ext
	}

	#[test]
	fn encode_decode_roundtrip() {
		use super::super::{super::Config as SessionConfig, Config as HistoricalConfig};
		use codec::{Decode, Encode};

		let sample = (
			22u32 as <Test as SessionConfig>::ValidatorId,
			7_777_777 as <Test as HistoricalConfig>::FullIdentification,
		);

		let encoded = sample.encode();
		let decoded = Decode::decode(&mut encoded.as_slice()).expect("Must decode");
		assert_eq!(sample, decoded);
	}

	#[test]
	fn onchain_to_offchain() {
		let mut ext = new_test_ext();

		const DATA: &[u8] = &[7, 8, 9, 10, 11];
		ext.execute_with(|| {
			b"alphaomega"[..].using_encoded(|key| sp_io::offchain_index::set(key, DATA));
		});

		ext.persist_offchain_overlay();

		ext.execute_with(|| {
			let data = b"alphaomega"[..].using_encoded(|key| {
				sp_io::offchain::local_storage_get(StorageKind::PERSISTENT, key)
			});
			assert_eq!(data, Some(DATA.to_vec()));
		});
	}

	#[test]
	fn historical_proof_offchain() {
		let mut ext = new_test_ext();
		let encoded_key_1 = UintAuthorityId(1).encode();

		ext.execute_with(|| {
			set_next_validators(vec![1, 2]);
			force_new_session();

			System::set_block_number(1);
			Session::on_initialize(1);

			// "on-chain"
			onchain::store_current_session_validator_set_to_offchain::<Test>();
			assert_eq!(<SessionModule<Test>>::current_index(), 1);

			set_next_validators(vec![7, 8]);

			force_new_session();
		});

		ext.persist_offchain_overlay();

		ext.execute_with(|| {
			System::set_block_number(2);
			Session::on_initialize(2);
			assert_eq!(<SessionModule<Test>>::current_index(), 2);

			// "off-chain"
			let proof = prove_session_membership::<Test, _>(1, (DUMMY, &encoded_key_1));
			assert!(proof.is_some());
			let proof = proof.expect("Must be Some(Proof)");

			assert!(Historical::check_proof((DUMMY, &encoded_key_1[..]), proof.clone()).is_some());
		});
	}
}
