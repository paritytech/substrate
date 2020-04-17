// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Trie-based state machine backend.

use crate::{
    trie_backend_essence::{Ephemeral, TrieBackendEssence, TrieBackendStorage},
    Backend, StorageKey, StorageValue,
};
use codec::{Codec, Decode};
use hash_db::Hasher;
use log::{debug, warn};
use sp_core::storage::ChildInfo;
use sp_trie::trie_types::{Layout, TrieDB, TrieError};
use sp_trie::{child_delta_trie_root, default_child_trie_root, delta_trie_root, Trie};

/// Patricia trie-based backend. Transaction type is an overlay of changes to commit.
pub struct TrieBackend<S: TrieBackendStorage<H>, H: Hasher> {
    essence: TrieBackendEssence<S, H>,
}

impl<S: TrieBackendStorage<H>, H: Hasher> TrieBackend<S, H>
where
    H::Out: Codec,
{
    /// Create new trie-based backend.
    pub fn new(storage: S, root: H::Out) -> Self {
        TrieBackend {
            essence: TrieBackendEssence::new(storage, root),
        }
    }

    /// Get backend essence reference.
    pub fn essence(&self) -> &TrieBackendEssence<S, H> {
        &self.essence
    }

    /// Get backend storage reference.
    pub fn backend_storage(&self) -> &S {
        self.essence.backend_storage()
    }

    /// Get trie root.
    pub fn root(&self) -> &H::Out {
        self.essence.root()
    }

    /// Consumes self and returns underlying storage.
    pub fn into_storage(self) -> S {
        self.essence.into_storage()
    }
}

impl<S: TrieBackendStorage<H>, H: Hasher> std::fmt::Debug for TrieBackend<S, H> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "TrieBackend")
    }
}

impl<S: TrieBackendStorage<H>, H: Hasher> Backend<H> for TrieBackend<S, H>
where
    H::Out: Ord + Codec,
{
    type Error = String;
    type Transaction = S::Overlay;
    type TrieBackendStorage = S;

    fn storage(&self, key: &[u8]) -> Result<Option<StorageValue>, Self::Error> {
        self.essence.storage(key)
    }

    fn child_storage(
        &self,
        storage_key: &[u8],
        child_info: ChildInfo,
        key: &[u8],
    ) -> Result<Option<StorageValue>, Self::Error> {
        self.essence.child_storage(storage_key, child_info, key)
    }

    fn next_storage_key(&self, key: &[u8]) -> Result<Option<StorageKey>, Self::Error> {
        self.essence.next_storage_key(key)
    }

    fn next_child_storage_key(
        &self,
        storage_key: &[u8],
        child_info: ChildInfo,
        key: &[u8],
    ) -> Result<Option<StorageKey>, Self::Error> {
        self.essence
            .next_child_storage_key(storage_key, child_info, key)
    }

    fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
        self.essence.for_keys_with_prefix(prefix, f)
    }

    fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
        self.essence.for_key_values_with_prefix(prefix, f)
    }

    fn for_keys_in_child_storage<F: FnMut(&[u8])>(
        &self,
        storage_key: &[u8],
        child_info: ChildInfo,
        f: F,
    ) {
        self.essence
            .for_keys_in_child_storage(storage_key, child_info, f)
    }

    fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
        &self,
        storage_key: &[u8],
        child_info: ChildInfo,
        prefix: &[u8],
        f: F,
    ) {
        self.essence
            .for_child_keys_with_prefix(storage_key, child_info, prefix, f)
    }

    fn pairs(&self) -> Vec<(StorageKey, StorageValue)> {
        let mut read_overlay = S::Overlay::default();
        let eph = Ephemeral::new(self.essence.backend_storage(), &mut read_overlay);

        let collect_all = || -> Result<_, Box<TrieError<H::Out>>> {
            let trie = TrieDB::<H>::new(&eph, self.essence.root())?;
            let mut v = Vec::new();
            for x in trie.iter()? {
                let (key, value) = x?;
                v.push((key.to_vec(), value.to_vec()));
            }

            Ok(v)
        };

        match collect_all() {
            Ok(v) => v,
            Err(e) => {
                debug!(target: "trie", "Error extracting trie values: {}", e);
                Vec::new()
            }
        }
    }

    fn keys(&self, prefix: &[u8]) -> Vec<StorageKey> {
        let mut read_overlay = S::Overlay::default();
        let eph = Ephemeral::new(self.essence.backend_storage(), &mut read_overlay);

        let collect_all = || -> Result<_, Box<TrieError<H::Out>>> {
            let trie = TrieDB::<H>::new(&eph, self.essence.root())?;
            let mut v = Vec::new();
            for x in trie.iter()? {
                let (key, _) = x?;
                if key.starts_with(prefix) {
                    v.push(key.to_vec());
                }
            }

            Ok(v)
        };

        collect_all()
            .map_err(|e| debug!(target: "trie", "Error extracting trie keys: {}", e))
            .unwrap_or_default()
    }

    fn storage_root<I>(&self, delta: I) -> (H::Out, S::Overlay)
    where
        I: IntoIterator<Item = (StorageKey, Option<StorageValue>)>,
    {
        let mut write_overlay = S::Overlay::default();
        let mut root = *self.essence.root();

        {
            let mut eph = Ephemeral::new(self.essence.backend_storage(), &mut write_overlay);

            match delta_trie_root::<Layout<H>, _, _, _, _>(&mut eph, root, delta) {
                Ok(ret) => root = ret,
                Err(e) => warn!(target: "trie", "Failed to write to trie: {}", e),
            }
        }

        (root, write_overlay)
    }

    fn child_storage_root<I>(
        &self,
        storage_key: &[u8],
        child_info: ChildInfo,
        delta: I,
    ) -> (H::Out, bool, Self::Transaction)
    where
        I: IntoIterator<Item = (StorageKey, Option<StorageValue>)>,
        H::Out: Ord,
    {
        let default_root = default_child_trie_root::<Layout<H>>(storage_key);

        let mut write_overlay = S::Overlay::default();
        let mut root = match self.storage(storage_key) {
            Ok(value) => value
                .and_then(|r| Decode::decode(&mut &r[..]).ok())
                .unwrap_or(default_root.clone()),
            Err(e) => {
                warn!(target: "trie", "Failed to read child storage root: {}", e);
                default_root.clone()
            }
        };

        {
            let mut eph = Ephemeral::new(self.essence.backend_storage(), &mut write_overlay);

            match child_delta_trie_root::<Layout<H>, _, _, _, _, _>(
                storage_key,
                child_info.keyspace(),
                &mut eph,
                root,
                delta,
            ) {
                Ok(ret) => root = ret,
                Err(e) => warn!(target: "trie", "Failed to write to trie: {}", e),
            }
        }

        let is_default = root == default_root;

        (root, is_default, write_overlay)
    }

    fn as_trie_backend(&mut self) -> Option<&TrieBackend<Self::TrieBackendStorage, H>> {
        Some(self)
    }

    fn register_overlay_stats(&mut self, _stats: &crate::stats::StateMachineStats) {}

    fn usage_info(&self) -> crate::UsageInfo {
        crate::UsageInfo::empty()
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use codec::Encode;
    use sp_core::H256;
    use sp_runtime::traits::BlakeTwo256;
    use sp_trie::{trie_types::TrieDBMut, KeySpacedDBMut, PrefixedMemoryDB, TrieMut};
    use std::collections::HashSet;

    const CHILD_KEY_1: &[u8] = b":child_storage:default:sub1";

    const CHILD_UUID_1: &[u8] = b"unique_id_1";
    const CHILD_INFO_1: ChildInfo<'static> = ChildInfo::new_default(CHILD_UUID_1);

    fn test_db() -> (PrefixedMemoryDB<BlakeTwo256>, H256) {
        let mut root = H256::default();
        let mut mdb = PrefixedMemoryDB::<BlakeTwo256>::default();
        {
            let mut mdb = KeySpacedDBMut::new(&mut mdb, CHILD_UUID_1);
            let mut trie = TrieDBMut::new(&mut mdb, &mut root);
            trie.insert(b"value3", &[142]).expect("insert failed");
            trie.insert(b"value4", &[124]).expect("insert failed");
        };

        {
            let mut sub_root = Vec::new();
            root.encode_to(&mut sub_root);
            let mut trie = TrieDBMut::new(&mut mdb, &mut root);
            trie.insert(CHILD_KEY_1, &sub_root[..])
                .expect("insert failed");
            trie.insert(b"key", b"value").expect("insert failed");
            trie.insert(b"value1", &[42]).expect("insert failed");
            trie.insert(b"value2", &[24]).expect("insert failed");
            trie.insert(b":code", b"return 42").expect("insert failed");
            for i in 128u8..255u8 {
                trie.insert(&[i], &[i]).unwrap();
            }
        }
        (mdb, root)
    }

    pub(crate) fn test_trie() -> TrieBackend<PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256> {
        let (mdb, root) = test_db();
        TrieBackend::new(mdb, root)
    }

    #[test]
    fn read_from_storage_returns_some() {
        assert_eq!(
            test_trie().storage(b"key").unwrap(),
            Some(b"value".to_vec())
        );
    }

    #[test]
    fn read_from_child_storage_returns_some() {
        let test_trie = test_trie();
        assert_eq!(
            test_trie
                .child_storage(CHILD_KEY_1, CHILD_INFO_1, b"value3")
                .unwrap(),
            Some(vec![142u8]),
        );
    }

    #[test]
    fn read_from_storage_returns_none() {
        assert_eq!(test_trie().storage(b"non-existing-key").unwrap(), None);
    }

    #[test]
    fn pairs_are_not_empty_on_non_empty_storage() {
        assert!(!test_trie().pairs().is_empty());
    }

    #[test]
    fn pairs_are_empty_on_empty_storage() {
        assert!(
            TrieBackend::<PrefixedMemoryDB<BlakeTwo256>, BlakeTwo256>::new(
                PrefixedMemoryDB::default(),
                Default::default(),
            )
            .pairs()
            .is_empty()
        );
    }

    #[test]
    fn storage_root_is_non_default() {
        assert!(test_trie().storage_root(::std::iter::empty()).0 != H256::repeat_byte(0));
    }

    #[test]
    fn storage_root_transaction_is_empty() {
        assert!(test_trie()
            .storage_root(::std::iter::empty())
            .1
            .drain()
            .is_empty());
    }

    #[test]
    fn storage_root_transaction_is_non_empty() {
        let (new_root, mut tx) =
            test_trie().storage_root(vec![(b"new-key".to_vec(), Some(b"new-value".to_vec()))]);
        assert!(!tx.drain().is_empty());
        assert!(new_root != test_trie().storage_root(::std::iter::empty()).0);
    }

    #[test]
    fn prefix_walking_works() {
        let trie = test_trie();

        let mut seen = HashSet::new();
        trie.for_keys_with_prefix(b"value", |key| {
            let for_first_time = seen.insert(key.to_vec());
            assert!(for_first_time, "Seen key '{:?}' more than once", key);
        });

        let mut expected = HashSet::new();
        expected.insert(b"value1".to_vec());
        expected.insert(b"value2".to_vec());
        assert_eq!(seen, expected);
    }
}
