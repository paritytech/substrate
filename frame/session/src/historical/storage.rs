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

//! Validator Set Extracting an iterator from an offchain worker stored list containing historical validatorsets.
//!
//! This is used in conjunction with [`ProvingTrie`](super::ProvingTrie) and
//! the offchain indexing API.

use sp_io::offchain_index;
use sp_std::prelude::*;

use super::super::{Module as SessionModule, SessionIndex};
use super::Trait;

const PREFIX: &[u8] = b"historical";
const LAST_PRUNE: &[u8] = b"historical_last_prune";
const HEAD: &[u8] = b"historical_head";

pub struct ValidatorSet<T: Trait> {
    validator_set: Vec<(T::ValidatorId, T::FullIdentification)>,
}

/// Derive the key used to store the list of validators
fn derive_key<P: AsRef<[u8]>, T: Trait>(prefix: P, session_index: Vec<u8>) -> Vec<u8> {
    assert!(session_index.len() > 0);
    let prefix = prefix.as_ref();
    let mut concatenated = Vec::with_capacity(prefix.len() + 1 + session_index.len());
    concatenated.extend_from_slice(prefix);
    concatenated.push('/');
    (&mut concatenated[(prefix.len() + 1)..]).extend_from_slice(session_index.as_slice());
    concatenated
}

impl<T: Trait> ValidatorSet<T> {
    /// Load the set of validators for a paritcular session index from the offchain storage.
    ///
    /// If none is found or decodable given `prefix` and `session`, it will return `None`.
    /// Empty validator sets should only ever exist for genesis blocks.
    fn load_from_offchain(session_index: SessionIndex) -> Option<Self> {
        let derived_key = derive_key(STATIC_PREFIX, session_index.encode());
        let validator_set = StorageValueRef::persistent(derived_key.as_ref())
            .get::<Vec<(T::ValidatorId, T::FullIdentification)>>()
            .flatten();
        validator_set
    }

    /// Access the underlying `ValidatorId` and `FullIdentification` tuples as slice.
    fn as_slice(&self) -> &[(T::ValidatorId, T::FullIdentification)] {
        self.validator_set.as_slice()
    }

    /// Convert `self` to a vector and consume `self`.
    fn to_vec(self) -> Vec<(T::ValidatorId, T::FullIdentification)> {
        self.validator_set
    }

    /// Prune anything older than the current session index.
    ///
    /// For behaviour details refer to [`fn prune_older_than`](Self::prune_older_than).
    ///
    /// **Must** be called from the offchain worker.
    fn prune() {
        let move_pruning_marker = SessionModule::current_index();
        Self::prune_older_than(move_pruning_marker);
    }

    /// Attempt to prune anything that is older than `first_to_keep` session index.
    ///
    /// Due to re-ogranisation it could be that the `first_to_keep` might be less
    /// than the stored one, in which case the conservative choice is made to keep records
    /// up to the one that is the lesser.
    ///
    /// **Must** be called from the offchain worker.
    fn prune_older_than(first_to_keep: SessionIndex) {
        let pruning_marker_key = derive_key(STATIC_LAST_PRUNE);
        let mut entry = StorageValueRef::persistent(derived_key.as_ref());
        match entry.mutate(|current: Option<Option<SessionIndex>>| {
            match current {
                Some(Some(current)) if current < first_to_keep => Ok(first_to_keep),
                // do not move the cursor, if the new one would be behind ours
                Some(Some(current)) => Ok(current),
                None => Ok(first_to_keep),
                // if the storage contains undecodable data, overwrite with current anyways
                // which might leak some entries being never purged
                Some(None) => Ok(first_to_keep),
            }
        }) {
            Ok(Ok(new_value)) => {
                // on a re-org this is not necessarily true, with the above they might be equal
                if previous < first_to_keep {
                    for session_index in previous..first_to_keep {
                        let derived_key = derive_key(STATIC_PREFIX, session_index.encode());
                        let _ = StorageValueRef::persistent(derived_key.as_ref()).clear();
                    }
                }
            }
            Ok(Err(e)) => {} // failed to store the value calculated with the given closure
            Err(e) => {}     // failed to calculate the value to store with the given closure
        }
    }

    /// **Must** be called from on chain.
    fn store_to_offchain(session: SessionIndex) {
        let session_index = <SessionModule<T>>::current_index();
        let derived_key = derive_key(prefix.as_ref(), session.encode());
        //let value = SessionModule::historical_root(session_index);
        let value = <SessionModule<T>>::validators().encode();
        offchain_index::set(value.as_slice())
    }

    /// **Must** be called from on chain, i.e. `on_import`
    fn store_current_to_offchain() {
        Self::store_to_offchain(SessionModule::current_index());
    }
}

/// Implement conversion into iterator for usage
/// with [ProvingTrie](super::ProvingTrie::generate_for).
impl<T: Trait> IntoIter for ValidatorSet<T> {
    type Item = (T::ValidatorId, T::FullIdentification);
    fn into_iter(self) -> impl Iterator<Item = Self::Item> {
        self.validator_set.into_iter()
    }
}
