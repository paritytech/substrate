// Copyright 2020 Parity Technologies (UK) Ltd.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// ! Trie storage proofs that are only verifying state for a given
// key value query plan.

use super::*;
use super::compact::{ProofCompacted};
use codec::{Encode, Decode};
use crate::{TrieConfiguration, TrieHash};
use sp_std::marker::PhantomData;


/// Proof for a known key value content.
///
/// This skips encoding of hashes in a similar way as `crate::storage_proof::compact`.
/// This also skips values in the proof, and can therefore only be
/// use to check if there was a change of content.
/// This needs to be check for every children proofs, and needs to keep
/// trace of every child trie origin.
#[derive(Encode, Decode)]
pub struct KnownQueryPlanAndValues<T>(pub(crate) ChildrenProofMap<ProofCompacted>, PhantomData<T>);

impl<T> sp_std::fmt::Debug for KnownQueryPlanAndValues<T> {
	fn fmt(&self, f: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		write!(f, "Known values compact proof: {:?}", &self.0)
	}
}

impl<T> PartialEq<KnownQueryPlanAndValues<T>> for KnownQueryPlanAndValues<T> {
	fn eq(&self, other: &KnownQueryPlanAndValues<T>) -> bool {
		self.0.eq(&other.0)
	}
}

impl<T> Eq for KnownQueryPlanAndValues<T> { }

impl<T> Clone for KnownQueryPlanAndValues<T> {
	fn clone(&self) -> Self {
		KnownQueryPlanAndValues(self.0.clone(), PhantomData)
	}
}

impl<T: 'static> StorageProof for KnownQueryPlanAndValues<T> {
	fn empty() -> Self {
		KnownQueryPlanAndValues(Default::default(), PhantomData)
	}

	fn is_empty(&self) -> bool {
		self.0.is_empty()
	}
}

#[cfg(feature = "std")]
impl<T> RegStorageProof<TrieHash<T>> for KnownQueryPlanAndValues<T>
	where
		T: 'static + TrieConfiguration,
		TrieHash<T>: Decode,
{
	const INPUT_KIND: InputKind = InputKind::QueryPlan;

	type RecordBackend = super::FullSyncRecorder<TrieHash<T>>;

	fn extract_proof(recorder: &Self::RecordBackend, input: Input) -> Result<Self> {
		if let Input::QueryPlan(input_children) = input {
			let mut result = ChildrenProofMap::default();
			let mut root_hash = TrieHash::<T>::default();
			for (child_info, set) in recorder.0.read().iter() {
				let child_info_proof = child_info.proof_info();
				if let Some((root, keys)) = input_children.get(&child_info_proof) {
					// Layout h is the only supported one at the time being
					if root.len() != root_hash.as_ref().len() {
						return Err(missing_pack_input());
					}
					root_hash.as_mut().copy_from_slice(&root[..]);
					let trie = trie_db::TrieDB::<T>::new(set, &root_hash)?;
					let compacted = trie_db::proof::generate_proof(&trie, keys)?;
					result.insert(child_info_proof, compacted);
				} else {
					return Err(missing_pack_input());
				}
			}
			Ok(KnownQueryPlanAndValues(result, PhantomData))
		} else {
			Err(missing_pack_input())
		}
	}
}

impl<T> CheckableStorageProof for KnownQueryPlanAndValues<T>
	where
		T: 'static + TrieConfiguration,
		TrieHash<T>: Decode,
{
	fn verify(self, input: &Input) -> Result<bool> {
		if let Input::QueryPlanWithValues(input_children) = input {
			let mut root_hash = TrieHash::<T>::default();
			for (child_info, nodes) in self.0.iter() {
				if let Some((root, input)) = input_children.get(child_info) {
					// Layout h is the only supported one at the time being
					if root.len() != root_hash.as_ref().len() {
						return Ok(false);
					}
					root_hash.as_mut().copy_from_slice(&root[..]);
					if let Err(_) = trie_db::proof::verify_proof::<T, _, _, _>(
						&root_hash,
						&nodes[..],
						input.iter(),
					) {
						return Ok(false);
					}
				} else {
					return Err(missing_verify_input());
				}
			}
			Ok(true)
		} else {
			Err(missing_pack_input())
		}
	}
}
