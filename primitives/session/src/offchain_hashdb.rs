// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Database storage based on the offchain index db for historical
//! slashing behaviour.
//!
//! For being able to erase per session data, there exist per
//! `session_index` keyd index
//! which tracks all entries which are associated with the `session_index`.
//!
//! The mapping is as follows
//! ```markdown
//! session -> [(derived_key,tree_prefix),(derived_key,tree_prefix),..]
//! ```
//! where `derived_key` is a unique identifier derived from the `digest`
//! of the associated data stored, `tree_prefix` as well as `session_index`.
//! This allows direct re-use for pruning individual values.
//!
//! The implementation contains two (2) different key deriving functions,
//! one for the index and one for the actual key value pairs in order
//! to disambiguate values in the underlying key value storage layer.
//!
//! Encoding and decoding is achieved by [`codec`](self::codec::Codec).

use trie_db::TrieLayout;

use hash_db::{AsHashDB, HashDB, Hasher, Prefix};

use codec::{Decode, Encode};
use sp_core::offchain::{Duration, StorageKind, Timestamp};

use sp_runtime::offchain::storage::StorageValueRef;

use sp_io::offchain;
use sp_std::collections::btree_set::BTreeSet;
use sp_std::prelude::*;


const STORAGE_TRACKING_GUARD_FALLBACK_DURATION: u64 = 30_000;


/// A persisted guard state.
///
/// An in DB persistent mutex for multi access items which are modified
/// i.e. vecs or sets.
pub struct StorageTrackingGuard<'a> {
    key: &'a [u8],
    locked_until: Option<Timestamp>,
}

impl<'a> StorageTrackingGuard<'a> {
    pub fn lock<'b>(key: &'b [u8]) -> Self
    where
        'b: 'a,
    {
        // @todo lock this scope I guess
        let value_ref = StorageValueRef::persistent(key);
        loop {
            let now = offchain::timestamp();
            let valid_until_unix_timestamp = match value_ref.get::<Timestamp>() {
                None => break,       // no data at all
                Some(None) => break, // garbage data could not be decoded
                Some(Some(valid_until_unix_timestamp)) => {
                    if valid_until_unix_timestamp < now {
                        break;
                    }
                    valid_until_unix_timestamp
                }
            };
            // do not snooze the full duration, but instead snooze 100ms
            // @todo add some additive jitter
            let remainder = valid_until_unix_timestamp.diff(&now);
            let snooze = offchain::timestamp().add(Duration::from_millis(core::cmp::min(
                remainder.millis(),
                100,
            )));
            offchain::sleep_until(snooze);
        }
        let locked_at_most_until = offchain::timestamp().add(Duration::from_millis(STORAGE_TRACKING_GUARD_FALLBACK_DURATION));
        value_ref.set(&locked_at_most_until);
        // @todo unlock
        Self {
            key,
            locked_until: Some(locked_at_most_until),
        }
    }
}

impl<'a> core::ops::Drop for StorageTrackingGuard<'a> {
    fn drop(&mut self) {
        let Self { key, locked_until } = self;

        if let Some(_locked_until) = locked_until {
            let value_ref = StorageValueRef::persistent(key);
            value_ref.remove();
        }
    }
}

/// Implementation of a key value store with pruning.
#[derive(Default)]
pub struct AlternativeDB<L>
where
    L: TrieLayout + Send,
{
    session_index: Vec<u8>,
    _phantom: core::marker::PhantomData<L>,
}

// @todo requires some internal mutability concept to work properly
// @todo which is yet to be hashed out
unsafe impl<L> core::marker::Sync for AlternativeDB<L> where L: TrieLayout + Send {}




const INDEX_DB_LOCK_KEY: &'static [u8] = b"alternate_db::tracking::lock";


/// Session aware, Offchain DB based HashDB.
///
/// Creates two indices:
/// index: session -> [(key,tree_prefix),(key,tree_prefix),..]
impl<L> AlternativeDB<L>
where
    L: TrieLayout + Send,
    <L as TrieLayout>::Hash: Default,
    <L as trie_db::TrieLayout>::Hash: core::default::Default + core::hash::BuildHasher,
    <<L as trie_db::TrieLayout>::Hash as Hasher>::Out: AsRef<[u8]> + Default,
{
    /// Additional prefix to distinguish data used.
    const PREFIX: &'static [u8] = b"__TO_BE_DEFINED__";

    /// Addition tracking prefix to separate index tracking data from
    /// actual key value data being tracked.
    const TRACKING_PREFIX: &'static [u8] = b"__TRACKING__";

    /// prune all data associated to a particular `session_index`.
    ///
    /// If `prefix` is set, only items having a particular tree prefix
    /// will be pruned.
    pub fn prune_session(&mut self, session_index: &[u8], prefix: Option<Prefix>) {
        let _lock = StorageTrackingGuard::lock(INDEX_DB_LOCK_KEY);
        let index = if let Some(prefix) = prefix {
            let tree_prefix = prefix.encode();
            let tree_prefix = tree_prefix.as_slice();

            self.get_index(session_index)
                .into_iter()
                .filter_map(move |(derived_key, prefix)| {
                    if tree_prefix == prefix.as_slice() {
                        StorageValueRef::persistent(derived_key.as_slice()).remove();
                        None
                    } else {
                        Some((derived_key, prefix))
                    }
                })
                .collect::<BTreeSet<_>>()
        } else {
            let index = self.get_index(session_index);
            index.into_iter().for_each(move |(derived_key, _prefix)| {
                StorageValueRef::persistent(derived_key.as_ref()).remove();
            });
            BTreeSet::new()
        };
        self.set_index(session_index, index);
    }

    /// Set the current session index.
    ///
    /// Utilized by the implementation of `HashDB` for `Self`.
    pub fn set_session<E: Encode>(&mut self, session_index: E) {
        self.session_index = session_index.encode();
    }

    /// Make `key` known to the persistent tracking index.
    fn add_to_index(&self, derived_key: &[u8], tree_prefix: &[u8], session_index: &[u8]) {
        let per_session_key: Vec<u8> = Self::derive_tracking_index_key(session_index);
        let mut mapping: BTreeSet<(Vec<u8>, Vec<u8>)> =
            StorageValueRef::persistent(derived_key.as_ref())
                .get::<BTreeSet<(Vec<u8>, Vec<u8>)>>()
                .flatten()
                .unwrap_or_else(|| BTreeSet::new());

        mapping.insert((derived_key.to_vec(), tree_prefix.to_vec()));
        StorageValueRef::persistent(per_session_key.as_ref()).set(&mapping);
    }

    /// Forget `key` from the persistent index.
    fn remove_from_index(&self, derived_key: &[u8], tree_prefix: &[u8], session_index: &[u8]) {
        let index = self.get_index(session_index);
        let index = index
            .into_iter()
            .filter(|(derived_key2, tree_prefix2)| {
                tree_prefix2.as_slice() != tree_prefix || derived_key2.as_slice() != derived_key
            })
            .collect();
        self.set_index(session_index, index);
    }

    /// Get the key tracking index.
    fn get_index(&self, session_index: &[u8]) -> BTreeSet<(Vec<u8>, Vec<u8>)> {
        let tracking_key: Vec<u8> = Self::derive_tracking_index_key(session_index);
        let mapping: BTreeSet<(Vec<u8>, Vec<u8>)> =
            StorageValueRef::persistent(tracking_key.as_ref())
                .get::<BTreeSet<(Vec<u8>, Vec<u8>)>>()
                .flatten()
                .unwrap_or_else(|| BTreeSet::new());
        mapping
    }

    /// Set the (modified) key tracking index.
    fn set_index(&self, session_index: &[u8], val: BTreeSet<(Vec<u8>, Vec<u8>)>) {
        let tracking_key: Vec<u8> = Self::derive_tracking_index_key(session_index);
        StorageValueRef::persistent(tracking_key.as_ref()).set(&val);
    }

    fn derive_tracking_index_key(session_index: &[u8]) -> Vec<u8> {
        //@todo probably waaaaay to slow
        // _ + _ + _ + _
        let total_len = Self::TRACKING_PREFIX.len() + 1 + session_index.len() + 1 + 2;
        let mut final_key = Vec::with_capacity(total_len);
        final_key.extend_from_slice(Self::TRACKING_PREFIX);
        final_key.push(b'+');
        final_key.extend_from_slice(session_index);
        final_key.push(b'+');
        final_key
    }

    /// Concatenate the static prefix with a tree prefix.
    fn derive_key(key: &[u8], tree_prefix: &[u8], session_index: &[u8]) -> Vec<u8> {
        //@todo probably waaaaay to slow
        // _ + _ + _ + _
        let total_len = Self::PREFIX.len() + 1 + session_index.len() + 1 + key.len() + 1 + 2;
        let mut final_key = Vec::with_capacity(total_len);
        final_key.extend_from_slice(Self::PREFIX);
        final_key.push(b'+');
        final_key.extend_from_slice(session_index);
        final_key.push(b'+');
        final_key.extend_from_slice(key);
        final_key.push(b'+');
        final_key.extend_from_slice(tree_prefix);
        final_key.push(b'+');
        final_key
    }
}

impl<L, T> HashDB<L::Hash, T> for AlternativeDB<L>
where
    L: TrieLayout + Send,
    T: Encode + Decode + Send + Default,
    <L as TrieLayout>::Hash: Default,
    <L as trie_db::TrieLayout>::Hash: core::default::Default + core::hash::BuildHasher,
    <<L as trie_db::TrieLayout>::Hash as Hasher>::Out: AsRef<[u8]> + Default,
{
    fn get(
        &self,
        key: &<<L as trie_db::TrieLayout>::Hash as Hasher>::Out,
        prefix: Prefix,
    ) -> Option<T> {
        let key = AsRef::<[u8]>::as_ref(key);
        let derived_key: Vec<u8> = Self::derive_key(
            key,
            prefix.encode().as_slice(),
            self.session_index.as_slice(),
        );
        StorageValueRef::persistent(derived_key.as_ref())
            .get::<T>()
            .flatten()
    }

    fn contains(
        &self,
        key: &<<L as trie_db::TrieLayout>::Hash as Hasher>::Out,
        prefix: Prefix,
    ) -> bool {
        // locking is not necessary since it is really just a read
        // and that MUST be locked at the DB level already
        // and the index is not involved here
        let key: &[u8] = AsRef::<[u8]>::as_ref(key);
        let derived_key: Vec<u8> = Self::derive_key(
            key,
            prefix.encode().as_slice(),
            self.session_index.as_slice(),
        );
        StorageValueRef::persistent(derived_key.as_ref())
            .get::<Vec<u8>>()
            .is_some()
    }

    fn insert(
        &mut self,
        prefix: Prefix,
        value: &[u8],
    ) -> <<L as trie_db::TrieLayout>::Hash as Hasher>::Out {
        let digest = <<L as trie_db::TrieLayout>::Hash as Hasher>::hash(value);
        let prefix = prefix.encode();
        let prefix = prefix.as_slice();
        let derived_key: Vec<u8> =
        Self::derive_key(digest.as_ref(), prefix, self.session_index.as_slice());

        let _lock = StorageTrackingGuard::lock(INDEX_DB_LOCK_KEY);
        StorageValueRef::persistent(derived_key.as_ref()).set(&value);
        self.add_to_index(derived_key.as_ref(), prefix, self.session_index.as_slice());
        digest
    }

    fn emplace(
        &mut self,
        key: <<L as trie_db::TrieLayout>::Hash as Hasher>::Out,
        prefix: Prefix,
        value: T,
    ) {
        let prefix = prefix.encode();
        let prefix = prefix.as_slice();
        let derived_key: Vec<u8> =
            Self::derive_key(key.as_ref(), prefix, self.session_index.as_slice());

        let _lock = StorageTrackingGuard::lock(INDEX_DB_LOCK_KEY);
        StorageValueRef::persistent(derived_key.as_ref()).set(&value);
        self.add_to_index(derived_key.as_ref(), prefix, self.session_index.as_slice());
    }

    fn remove(&mut self, key: &<<L as trie_db::TrieLayout>::Hash as Hasher>::Out, prefix: Prefix) {
        let prefix = prefix.encode();
        let prefix = prefix.as_slice();
        let derived_key: Vec<u8> =
            Self::derive_key(key.as_ref(), prefix, self.session_index.as_slice());

        let _lock = StorageTrackingGuard::lock(INDEX_DB_LOCK_KEY);
        self.remove_from_index(derived_key.as_ref(), prefix, self.session_index.as_slice());
        StorageValueRef::persistent(derived_key.as_ref()).remove();
    }
}

impl<L, T> AsHashDB<L::Hash, T> for AlternativeDB<L>
where
    L: TrieLayout + Send,
    T: Encode + Decode + Send + Default,
    <L as trie_db::TrieLayout>::Hash: core::default::Default + core::hash::BuildHasher,
    <<L as trie_db::TrieLayout>::Hash as Hasher>::Out: AsRef<[u8]> + Default,
{
    /// Perform upcast to HashDB for anything that derives from HashDB.
    fn as_hash_db(&self) -> &dyn HashDB<<L as trie_db::TrieLayout>::Hash, T> {
        self
    }
    /// Perform mutable upcast to HashDB for anything that derives from HashDB.
    fn as_hash_db_mut<'a>(
        &'a mut self,
    ) -> &'a mut (dyn HashDB<<L as trie_db::TrieLayout>::Hash, T> + 'a) {
        self
    }
}
