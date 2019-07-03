// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! An opt-in utility for tracking historical sessions in SRML-session.
//!
//! This is generally useful when implementing blockchains that require accountable
//! safety where validators from some amount f prior sessions must remain slashable.
//!
//! Rather than store the full session data for any given session, we instead commit
//! to the roots of merkle tries containing the session data.

use rstd::{prelude::*, marker::PhantomData, ops::Rem};
#[cfg(not(feature = "std"))]
use rstd::alloc::borrow::ToOwned;
use parity_codec::{Encode, Decode};
use primitives::KeyTypeId;
use primitives::traits::{Convert, Zero, Saturating, Member, OpaqueKeys, Header as HeaderT, Hash as HashT};
use srml_support::{
	ConsensusEngineId, StorageValue, StorageMap, for_each_tuple, decl_module,
	decl_event, decl_storage,
};
use srml_support::{ensure, traits::{OnFreeBalanceZero, Get, FindAuthor}, Parameter, print};
use system::ensure_signed;
use substrate_trie::{MemoryDB, Trie, TrieMut, TrieDBMut, TrieDB, Recorder};

use super::{SessionIndex, OnSessionEnding, Module as SessionModule};

/// Trait necessary for the historical module.
pub trait Trait: super::Trait {
	/// Full identification of the validator.
	type FullIdentification: Member + Parameter;

	/// A conversion from validator ID to full identification.
	///
	/// This should contain any references to economic actors associated with the
	/// validator, since they may be outdated by the time this is queried from a
	/// historical trie.
	type FullIdentificationOf: Convert<Self::ValidatorId, Option<Self::FullIdentification>>;
}

decl_storage! {
	trait Store for Module<T: Trait> as Session {
		/// Mapping from historical session indices to session-data root hash.
		HistoricalSessions get(historical_root): map SessionIndex => Option<T::Hash>;
		/// The range of historical sessions we store. [first, last)
		StoredRange: Option<(SessionIndex, SessionIndex)>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin { }
}

impl<T: Trait> Module<T> {
	/// Prune historical stored session roots up to (but not including)
	/// `up_to`.
	pub fn prune_up_to(up_to: SessionIndex) {
		<Self as Store>::StoredRange::mutate(|range| {
			let (start, end) = match *range {
				Some(range) => range,
				None => return, // nothing to prune.
			};

			let up_to = rstd::cmp::min(up_to, end);

			if up_to < start {
				return // out of bounds. harmless.
			}

			for i in start..up_to {
				<Self as Store>::HistoricalSessions::take(i);
			}

			let new_start = up_to;
			*range = if new_start == end {
				None // nothing is stored.
			} else {
				Some((new_start, end))
			}
		})
	}

	/// Generate a session-trie for the current session. This is used for proving
	/// membership of voters.
	///
	/// In general, this should not be used on-chain and instead only in runtime APIs
	/// that need to prove membership of a validator in the current set.
	pub fn generate_proving_trie() -> Result<ProvingTrie<T>, &'static str> {
		ProvingTrie::generate()
	}
}

impl<T: Trait> OnSessionEnding<T::AccountId> for Module<T> {
	fn on_session_ending(i: SessionIndex) -> Option<Vec<T::AccountId>> {
		<Self as Store>::StoredRange::mutate(|range| {
			range.get_or_insert_with(|| (i, i)).1 = i + 1;
		});

		match ProvingTrie::<T>::generate() {
			Ok(trie) => <HistoricalSessions<T>>::insert(i, &trie.root),
			Err(reason) => {
				print("Failed to generate historical ancestry-inclusion proof.");
				print(reason);
			}
		}

		None
	}
}

type HasherOf<T> = <<T as system::Trait>::Hashing as HashT>::Hasher;

/// a trie instance for checking and generating proofs.
pub struct ProvingTrie<T: Trait> {
	db: MemoryDB<HasherOf<T>>,
	root: T::Hash,
}

impl<T: Trait> ProvingTrie<T> {
	fn generate() -> Result<Self, &'static str> {
		let validators = <SessionModule<T>>::validators();
		let n = validators.len();
		ensure!(n <= u32::max_value() as usize, "2^32 or more validators is unsupported");

		let n = n as u32;

		let mut db = MemoryDB::default();
		let mut root = Default::default();

		{
			let mut trie = TrieDBMut::new(&mut db, &mut root);

			for validator in validators.into_iter() {
				let keys = match <SessionModule<T>>::load_keys(&validator) {
					None => continue,
					Some(k) => k,
				};

				let full_id = match T::FullIdentificationOf::convert(validator) {
					None => return Err("no full identification for a current validator"),
					Some(full) => full,
				};

				for key_id in T::Keys::key_ids() {
					let key = keys.get_raw(key_id);
					let res = (key_id, key).using_encoded(|k|
						full_id.using_encoded(|v|
							trie.insert(k, v)
						)
					);

					let _ = res.map_err(|_| "failed to insert into trie")?;
				}
			}
		}

		Ok(ProvingTrie {
			db,
			root,
		})
	}

	/// Prove the full verification data for a given key and key ID.
	pub fn prove(&self, key_id: KeyTypeId, key_data: &[u8]) -> Option<Vec<Vec<u8>>> {
		let trie = TrieDB::new(&self.db, &self.root).ok()?;
		let mut recorder = Recorder::new();
		(key_id, key_data).using_encoded(|s| {
			trie.get_with(s, &mut recorder)
				.ok()?
				.and_then(|raw| T::FullIdentification::decode(&mut &*raw))
				.map(move|_| recorder.drain().into_iter().map(|r| r.data).collect())
		})
	}

	/// Access the underlying trie root.
	pub fn root(&self) -> &T::Hash {
		&self.root
	}

	// Check a proof contained within the current memory-db. Returns `None` if the
	// nodes within the current `MemoryDB` are insufficient to query the item.
	fn query(&self, key_id: KeyTypeId, key_data: &[u8]) -> Option<T::FullIdentification> {
		let trie = TrieDB::new(&self.db, &self.root).ok()?;
		(key_id, key_data).using_encoded(|s| trie.get(s))
			.ok()?
			.and_then(|raw| T::FullIdentification::decode(&mut &*raw))
	}

}

#[derive(Encode, Decode)]
struct Proof {
	session: SessionIndex,
	nodes: Vec<Vec<u8>>,
}

// impl<T: Trait> srml_support::traits:::ValidatorMembershipProofSystem<u32> for Module<T> {
// 	type Proof = Proof;
// 	type FullIdentification = T::FullIdentification;

// 	fn prove(&self, id: u32) -> Option<Self::Proof> {
// 		let validators = <super::Module<T>>::validators();
// 		if (id as usize) >= session
// 	}
// }
