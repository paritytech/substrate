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
//! safety where validators from some amount of prior sessions must remain slashable.
//!
//! Rather than store the full session data for any given session, we instead commit
//! to the roots of merkle tries containing the session data.
//!
//! These roots and proofs of inclusion can be generated at any time during the current session.
//! Afterwards, the proofs can be fed to a consensus module when reporting misbehavior.

use rstd::prelude::*;
use codec::{Encode, Decode};
#[cfg(feature = "std")]
use serde::Serialize;
use sr_primitives::KeyTypeId;
use sr_primitives::traits::{Convert, OpaqueKeys, Hash as HashT};
use srml_support::{
	StorageValue, StorageMap, decl_module, decl_storage,
};
use srml_support::{Parameter, print};
use substrate_trie::{MemoryDB, Trie, TrieMut, Recorder, EMPTY_PREFIX};
use substrate_trie::trie_types::{TrieDBMut, TrieDB};
use super::{SessionIndex, Module as SessionModule};

type ValidatorCount = u32;

/// Trait necessary for the historical module.
pub trait Trait: super::Trait {
	/// Full identification of the validator.
	type FullIdentification: Parameter;

	/// A conversion from validator ID to full identification.
	///
	/// This should contain any references to economic actors associated with the
	/// validator, since they may be outdated by the time this is queried from a
	/// historical trie.
	///
	/// This mapping is expected to remain stable in between calls to
	/// `Self::OnSessionEnding::on_session_ending` which return new validators.
	type FullIdentificationOf: Convert<Self::ValidatorId, Option<Self::FullIdentification>>;
}

decl_storage! {
	trait Store for Module<T: Trait> as Session {
		/// Mapping from historical session indices to session-data root hash and validator count.
		HistoricalSessions get(historical_root): map SessionIndex => Option<(T::Hash, ValidatorCount)>;
		/// Queued full identifications for queued sessions whose validators have become obsolete.
		CachedObsolete get(cached_obsolete): map SessionIndex
			=> Option<Vec<(T::ValidatorId, T::FullIdentification)>>;
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

			(start..up_to).for_each(<Self as Store>::HistoricalSessions::remove);

			let new_start = up_to;
			*range = if new_start == end {
				None // nothing is stored.
			} else {
				Some((new_start, end))
			}
		})
	}
}

/// Specialization of the crate-level `OnSessionEnding` which returns the old
/// set of full identification when changing the validator set.
pub trait OnSessionEnding<ValidatorId, FullIdentification>: crate::OnSessionEnding<ValidatorId> {
	/// If there was a validator set change, its returns the set of new validators along with the
	/// old validators and their full identifications.
	fn on_session_ending(ending: SessionIndex, will_apply_at: SessionIndex)
		-> Option<(Vec<ValidatorId>, Vec<(ValidatorId, FullIdentification)>)>;
}

/// An `OnSessionEnding` implementation that wraps an inner `I` and also
/// sets the historical trie root of the ending session.
pub struct NoteHistoricalRoot<T, I>(rstd::marker::PhantomData<(T, I)>);

impl<T: Trait, I> crate::OnSessionEnding<T::ValidatorId> for NoteHistoricalRoot<T, I>
	where I: OnSessionEnding<T::ValidatorId, T::FullIdentification>
{
	fn on_session_ending(ending: SessionIndex, applied_at: SessionIndex) -> Option<Vec<T::ValidatorId>> {
		StoredRange::mutate(|range| {
			range.get_or_insert_with(|| (ending, ending)).1 = ending + 1;
		});

		// do all of this _before_ calling the other `on_session_ending` impl
		// so that we have e.g. correct exposures from the _current_.

		let count = <SessionModule<T>>::validators().len() as u32;
		match ProvingTrie::<T>::generate_for(ending) {
			Ok(trie) => <HistoricalSessions<T>>::insert(ending, &(trie.root, count)),
			Err(reason) => {
				print("Failed to generate historical ancestry-inclusion proof.");
				print(reason);
			}
		};

		// trie has been generated for this session, so it's no longer queued.
		<CachedObsolete<T>>::remove(&ending);

		let (new_validators, old_exposures) = <I as OnSessionEnding<_, _>>::on_session_ending(ending, applied_at)?;

		// every session from `ending+1 .. applied_at` now has obsolete `FullIdentification`
		// now that a new validator election has occurred.
		// we cache these in the trie until those sessions themselves end.
		for obsolete in (ending + 1) .. applied_at {
			<CachedObsolete<T>>::insert(obsolete, &old_exposures);
		}

		Some(new_validators)
	}
}

type HasherOf<T> = <<T as system::Trait>::Hashing as HashT>::Hasher;

/// A tuple of the validator's ID and their full identification.
pub type IdentificationTuple<T> = (<T as crate::Trait>::ValidatorId, <T as Trait>::FullIdentification);

/// a trie instance for checking and generating proofs.
pub struct ProvingTrie<T: Trait> {
	db: MemoryDB<HasherOf<T>>,
	root: T::Hash,
}

impl<T: Trait> ProvingTrie<T> {
	fn generate_for(now: SessionIndex) -> Result<Self, &'static str> {
		let mut db = MemoryDB::default();
		let mut root = Default::default();

		fn build<T: Trait, I>(root: &mut T::Hash, db: &mut MemoryDB<HasherOf<T>>, validators: I)
			-> Result<(), &'static str>
			where I: IntoIterator<Item=(T::ValidatorId, Option<T::FullIdentification>)>
		{
			let mut trie = TrieDBMut::new(db, root);
			for (i, (validator, full_id)) in validators.into_iter().enumerate() {
				let i = i as u32;
				let keys = match <SessionModule<T>>::load_keys(&validator) {
					None => continue,
					Some(k) => k,
				};

				let full_id = full_id.or_else(|| T::FullIdentificationOf::convert(validator.clone()));
				let full_id = match full_id {
					None => return Err("no full identification for a current validator"),
					Some(full) => (validator, full),
				};

				// map each key to the owner index.
				for key_id in T::Keys::key_ids() {
					let key = keys.get_raw(key_id);
					let res = (key_id, key).using_encoded(|k|
						i.using_encoded(|v|
							trie.insert(k, v)
						)
					);

					let _ = res.map_err(|_| "failed to insert into trie")?;
				}

				// map each owner index to the full identification.
				let _ = i.using_encoded(|k| full_id.using_encoded(|v| trie.insert(k, v)))
					.map_err(|_| "failed to insert into trie")?;
			}

			Ok(())
		}

		// if the current session's full identifications are obsolete but cached,
		// use those.
		if let Some(obsolete) = <CachedObsolete<T>>::get(&now) {
			build::<T, _>(&mut root, &mut db, obsolete.into_iter().map(|(v, f)| (v, Some(f))))?
		} else {
			let validators = <SessionModule<T>>::validators();
			build::<T, _>(&mut root, &mut db, validators.into_iter().map(|v| (v, None)))?
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
			HashDBT::insert(&mut memory_db, EMPTY_PREFIX, &node[..]);
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
		let val_idx = (key_id, key_data).using_encoded(|s| {
			trie.get_with(s, &mut recorder)
				.ok()?
				.and_then(|raw| u32::decode(&mut &*raw).ok())
		})?;

		val_idx.using_encoded(|s| {
			trie.get_with(s, &mut recorder)
				.ok()?
				.and_then(|raw| <IdentificationTuple<T>>::decode(&mut &*raw).ok())
		})?;

		Some(recorder.drain().into_iter().map(|r| r.data).collect())
	}

	/// Access the underlying trie root.
	pub fn root(&self) -> &T::Hash {
		&self.root
	}

	// Check a proof contained within the current memory-db. Returns `None` if the
	// nodes within the current `MemoryDB` are insufficient to query the item.
	fn query(&self, key_id: KeyTypeId, key_data: &[u8]) -> Option<IdentificationTuple<T>> {
		let trie = TrieDB::new(&self.db, &self.root).ok()?;
		let val_idx = (key_id, key_data).using_encoded(|s| trie.get(s))
			.ok()?
			.and_then(|raw| u32::decode(&mut &*raw).ok())?;

		val_idx.using_encoded(|s| trie.get(s))
			.ok()?
			.and_then(|raw| <IdentificationTuple<T>>::decode(&mut &*raw).ok())
	}

}

/// Proof of ownership of a specific key.
#[cfg_attr(feature = "std", derive(Serialize, Debug))]
#[derive(Encode, Decode, Clone, PartialEq, Eq, Default)]
pub struct Proof {
	session: SessionIndex,
	trie_nodes: Vec<Vec<u8>>,
}

impl<T: Trait, D: AsRef<[u8]>> srml_support::traits::KeyOwnerProofSystem<(KeyTypeId, D)>
	for Module<T>
{
	type Proof = Proof;
	type IdentificationTuple = IdentificationTuple<T>;

	fn prove(key: (KeyTypeId, D)) -> Option<Self::Proof> {
		let session = <SessionModule<T>>::current_index();
		let trie = ProvingTrie::<T>::generate_for(session).ok()?;

		let (id, data) = key;

		trie.prove(id, data.as_ref()).map(|trie_nodes| Proof {
			session,
			trie_nodes,
		})
	}

	fn check_proof(key: (KeyTypeId, D), proof: Proof) -> Option<IdentificationTuple<T>> {
		let (id, data) = key;

		if proof.session == <SessionModule<T>>::current_index() {
			<SessionModule<T>>::key_owner(id, data.as_ref()).and_then(|owner|
				T::FullIdentificationOf::convert(owner.clone()).map(move |id| (owner, id))
			)
		} else {
			let (root, _) = <HistoricalSessions<T>>::get(&proof.session)?;
			let trie = ProvingTrie::<T>::from_nodes(root, &proof.trie_nodes);

			trie.query(id, data.as_ref())
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::with_externalities;
	use primitives::{Blake2Hasher, crypto::key_types::DUMMY};
	use sr_primitives::{traits::OnInitialize, testing::UintAuthorityId};
	use crate::mock::{
		NEXT_VALIDATORS, force_new_session,
		set_next_validators, Test, System, Session,
	};
	use srml_support::traits::KeyOwnerProofSystem;

	type Historical = Module<Test>;

	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		crate::GenesisConfig::<Test> {
			keys: NEXT_VALIDATORS.with(|l|
				l.borrow().iter().cloned().map(|i| (i, UintAuthorityId(i).into())).collect()
			),
		}.assimilate_storage(&mut t).unwrap();
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
			let proof = Historical::prove((DUMMY, &encoded_key_1[..])).unwrap();

			// proof-checking in the same session is OK.
			assert!(Historical::check_proof((DUMMY, &encoded_key_1[..]), proof.clone()).is_some());

			set_next_validators(vec![1, 2, 4]);
			force_new_session();

			assert!(Historical::cached_obsolete(&(proof.session + 1)).is_none());

			System::set_block_number(2);
			Session::on_initialize(2);

			assert!(Historical::cached_obsolete(&(proof.session + 1)).is_some());

			assert!(Historical::historical_root(proof.session).is_some());
			assert!(Session::current_index() > proof.session);

			// proof-checking in the next session is also OK.
			assert!(Historical::check_proof((DUMMY, &encoded_key_1[..]), proof.clone()).is_some());

			set_next_validators(vec![1, 2, 5]);

			force_new_session();
			System::set_block_number(3);
			Session::on_initialize(3);

			assert!(Historical::cached_obsolete(&(proof.session + 1)).is_none());
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
