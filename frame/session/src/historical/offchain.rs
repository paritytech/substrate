// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Validator Set Extracting an iterator from an off-chain worker stored list containing historical validatorsets.
//!
//! This is used in conjunction with [`ProvingTrie`](super::ProvingTrie) and
//! the off-chain indexing API.

use sp_runtime::{offchain::storage::StorageValueRef, KeyTypeId};
use sp_session::MembershipProof;

use super::super::{Module as SessionModule, SessionIndex};
use super::{IdentificationTuple, ProvingTrie, Trait};

use super::shared::*;

pub struct ValidatorSet<T: Trait> {
    validator_set: Vec<IdentificationTuple<T>>,
}

impl<T: Trait> ValidatorSet<T> {
    /// Load the set of validators for a paritcular session index from the off-chain storage.
    ///
    /// If none is found or decodable given `prefix` and `session`, it will return `None`.
    /// Empty validator sets should only ever exist for genesis blocks.
    pub fn load_from_offchain_db(session_index: SessionIndex) -> Option<Self> {
        let derived_key = derive_key(PREFIX, session_index);
        let validator_set = StorageValueRef::persistent(derived_key.as_ref())
            .get::<Vec<(T::ValidatorId, T::FullIdentification)>>()
            .flatten();
        validator_set.map(|validator_set| Self { validator_set })
    }

    /// Access the underlying `ValidatorId` and `FullIdentification` tuples as slice.
    pub fn as_slice(&self) -> &[(T::ValidatorId, T::FullIdentification)] {
        self.validator_set.as_slice()
    }

    /// Convert `self` into a vector and consume `self`.
    pub fn into_vec(self) -> Vec<(T::ValidatorId, T::FullIdentification)> {
        self.validator_set
    }

    /// Attempt to prune anything that is older than `first_to_keep` session index.
    ///
    /// Due to re-ogranisation it could be that the `first_to_keep` might be less
    /// than the stored one, in which case the conservative choice is made to keep records
    /// up to the one that is the lesser.
    pub fn prune_older_than(first_to_keep: SessionIndex) {
        let derived_key = LAST_PRUNE.to_vec();
        let entry = StorageValueRef::persistent(derived_key.as_ref());
        match entry.mutate(|current: Option<Option<SessionIndex>>| -> Result<_, ()> {
            match current {
                Some(Some(current)) if current < first_to_keep => Ok(first_to_keep),
                // do not move the cursor, if the new one would be behind ours
                Some(Some(current)) => Ok(current),
                None => Ok(first_to_keep),
                // if the storage contains undecodable data, overwrite with current anyways
                // which might leak some entries being never purged, but that is acceptable
                // in this context
                Some(None) => Ok(first_to_keep),
            }
        }) {
            Ok(Ok(new_value)) => {
                // on a re-org this is not necessarily true, with the above they might be equal
                if new_value < first_to_keep {
                    for session_index in new_value..first_to_keep {
                        let derived_key = derive_key(PREFIX, session_index);
                        let _ = StorageValueRef::persistent(derived_key.as_ref()).clear();
                    }
                }
            }
            Ok(Err(_)) => {} // failed to store the value calculated with the given closure
            Err(_) => {}     // failed to calculate the value to store with the given closure
        }
    }

    /// Keep the newest `n` items, and prune all items odler than that.
    pub fn keep_newest(n_to_keep: usize) {
        let session_index = <SessionModule<T>>::current_index();
        let n_to_keep = n_to_keep as SessionIndex;
        if n_to_keep < session_index {
            Self::prune_older_than(session_index - n_to_keep)
        }
    }

    #[inline]
    fn len(&self) -> usize {
        self.validator_set.len()
    }
}

/// Implement conversion into iterator for usage
/// with [ProvingTrie](super::ProvingTrie::generate_for).
impl<T: Trait> core::iter::IntoIterator for ValidatorSet<T> {
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
pub fn prove_session_membership<T: Trait, D: AsRef<[u8]>>(
    session_index: SessionIndex,
    session_key: (KeyTypeId, D),
) -> Option<MembershipProof> {
    let validators = ValidatorSet::<T>::load_from_offchain_db(session_index)?;
    let count = validators.len() as u32;
    let trie = ProvingTrie::<T>::generate_for(validators.into_iter()).ok()?;

    let (id, data) = session_key;
    trie.prove(id, data.as_ref())
        .map(|trie_nodes| MembershipProof {
            session: session_index,
            trie_nodes,
            validator_count: count,
        })
}

#[cfg(test)]
mod tests {
    use super::super::tests::new_test_ext;
    use super::*;

    #[test]
    fn justone() {
        new_test_ext().execute_with(|| {
            // @todo think of a way to test this properly, not sure yet if we can just call
            // on-chain and off-chain all at once from here and get meaningful results
        })
    }
}
