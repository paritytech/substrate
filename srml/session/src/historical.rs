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

use rstd::prelude::*;
use parity_codec::{Encode, Decode};
use primitives::KeyTypeId;
use primitives::traits::{Convert, OpaqueKeys, Hash as HashT};
use srml_support::{
	StorageValue, StorageMap, decl_module, decl_storage,
};
use srml_support::{Parameter, print};
use substrate_trie::{MemoryDB, Trie, TrieMut, TrieDBMut, TrieDB, Recorder};

use super::{SessionIndex, OnSessionEnding, Module as SessionModule};

/// Trait necessary for the historical module.
pub trait Trait: super::Trait {
	/// Full identification of the validator.
	type FullIdentification: Parameter;

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
}

/// An `OnSessionEnding` implementation that wraps an inner `I` and also
/// sets the historical trie root of the ending session.
pub struct NoteHistoricalRoot<T, I>(rstd::marker::PhantomData<(T, I)>);

impl<T: Trait, I> OnSessionEnding<T::AccountId> for NoteHistoricalRoot<T, I>
	where I: OnSessionEnding<T::AccountId>
{
	fn on_session_ending(i: SessionIndex) -> Option<Vec<T::AccountId>> {
		StoredRange::mutate(|range| {
			range.get_or_insert_with(|| (i, i)).1 = i + 1;
		});

		match ProvingTrie::<T>::generate_now() {
			Ok(trie) => <HistoricalSessions<T>>::insert(i, &trie.root),
			Err(reason) => {
				print("Failed to generate historical ancestry-inclusion proof.");
				print(reason);
			}
		}

		I::on_session_ending(i)
	}
}

type HasherOf<T> = <<T as system::Trait>::Hashing as HashT>::Hasher;

/// a trie instance for checking and generating proofs.
pub struct ProvingTrie<T: Trait> {
	db: MemoryDB<HasherOf<T>>,
	root: T::Hash,
}

impl<T: Trait> ProvingTrie<T> {
	fn generate_now() -> Result<Self, &'static str> {
		let validators = <SessionModule<T>>::validators();
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

	fn from_nodes(root: T::Hash, nodes: &[Vec<u8>]) -> Self {
		use substrate_trie::HashDBT;

		let mut memory_db = MemoryDB::default();
		for node in nodes {
			HashDBT::insert(&mut memory_db, &[], &node[..]);
		}

		ProvingTrie {
			db: memory_db,
			root,
		}
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

/// Proof of ownership of a specific key.
#[derive(Encode, Decode, Clone)]
pub struct Proof {
	session: SessionIndex,
	trie_nodes: Vec<Vec<u8>>,
}

impl<T: Trait, D: AsRef<[u8]>> srml_support::traits::KeyOwnerProofSystem<(KeyTypeId, D)>
	for Module<T>
{
	type Proof = Proof;
	type FullIdentification = T::FullIdentification;

	fn prove(key: (KeyTypeId, D)) -> Option<Self::Proof> {
		let trie = ProvingTrie::<T>::generate_now().ok()?;
		let session = <SessionModule<T>>::current_index();

		let (id, data) = key;

		trie.prove(id, data.as_ref()).map(|trie_nodes| Proof {
			session,
			trie_nodes,
		})
	}

	fn check_proof(key: (KeyTypeId, D), proof: Proof) -> Option<T::FullIdentification> {
		let (id, data) = key;

		if proof.session == <SessionModule<T>>::current_index() {
			<SessionModule<T>>::key_owner(id, data.as_ref()).and_then(T::FullIdentificationOf::convert)
		} else {
			let root = <HistoricalSessions<T>>::get(&proof.session)?;
			let trie = ProvingTrie::<T>::from_nodes(root, &proof.trie_nodes);

			trie.query(id, data.as_ref())
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::with_externalities;
	use substrate_primitives::Blake2Hasher;
	use primitives::{
		traits::OnInitialize,
		testing::{UintAuthorityId, UINT_DUMMY_KEY},
	};
	use crate::mock::{
		NEXT_VALIDATORS, force_new_session, next_validators,
		set_next_validators, Test, System, Session,
	};
	use srml_support::traits::KeyOwnerProofSystem;

	type Historical = Module<Test>;

	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap().0;
		t.extend(timestamp::GenesisConfig::<Test> {
			minimum_period: 5,
		}.build_storage().unwrap().0);
		let (storage, _child_storage) = crate::GenesisConfig::<Test> {
			validators: next_validators(),
			keys: NEXT_VALIDATORS.with(|l|
				l.borrow().iter().cloned().map(|i| (i, UintAuthorityId(i))).collect()
			),
		}.build_storage().unwrap();
		t.extend(storage);
		runtime_io::TestExternalities::new(t)
	}

	#[test]
	fn generated_proof_is_good() {
		with_externalities(&mut new_test_ext(), || {
			set_next_validators(vec![1, 2]);
			force_new_session();

			System::set_block_number(1);
			Session::on_initialize(1);

			let encoded_key_1 = UintAuthorityId(1).encode();
			let proof = Historical::prove((UINT_DUMMY_KEY, &encoded_key_1[..])).unwrap();

			// proof-checking in the same session is OK.
			assert!(
				Historical::check_proof(
					(UINT_DUMMY_KEY, &encoded_key_1[..]),
					proof.clone(),
				).is_some()
			);

			set_next_validators(vec![1, 2, 4]);
			force_new_session();

			System::set_block_number(2);
			Session::on_initialize(2);

			assert!(Historical::historical_root(proof.session).is_some());
			assert!(Session::current_index() > proof.session);

			// proof-checking in the next session is also OK.
			assert!(
				Historical::check_proof(
					(UINT_DUMMY_KEY, &encoded_key_1[..]),
					proof.clone(),
				).is_some()
			);
		});
	}

	#[test]
	fn prune_up_to_works() {
		with_externalities(&mut new_test_ext(), || {
			for i in 1..101u64 {
				set_next_validators(vec![i]);
				force_new_session();

				System::set_block_number(i);
				Session::on_initialize(i);

			}

			assert_eq!(StoredRange::get(), Some((0, 100)));

			for i in 1..100 {
				assert!(Historical::historical_root(i).is_some())
			}

			Historical::prune_up_to(10);
			assert_eq!(StoredRange::get(), Some((10, 100)));

			Historical::prune_up_to(9);
			assert_eq!(StoredRange::get(), Some((10, 100)));

			for i in 10..100 {
				assert!(Historical::historical_root(i).is_some())
			}

			Historical::prune_up_to(99);
			assert_eq!(StoredRange::get(), Some((99, 100)));

			Historical::prune_up_to(100);
			assert_eq!(StoredRange::get(), None);

			for i in 101..201u64 {
				set_next_validators(vec![i]);
				force_new_session();

				System::set_block_number(i);
				Session::on_initialize(i);

			}

			assert_eq!(StoredRange::get(), Some((100, 200)));

			for i in 101..200 {
				assert!(Historical::historical_root(i).is_some())
			}

			Historical::prune_up_to(9999);
			assert_eq!(StoredRange::get(), None);

			for i in 101..200 {
				assert!(Historical::historical_root(i).is_none())
			}
		});
	}
}
