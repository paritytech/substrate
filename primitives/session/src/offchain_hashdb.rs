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

use trie_db::node::{decode_hash, Node as EncodedNode, NodeHandle as EncodedNodeHandle};
use trie_db::Lookup;
use trie_db::{node::NodeKey, DBValue};
use trie_db::{CError, Result, TrieError, TrieHash, TrieLayout, TrieMut};

use core::marker::Sync;
use hash_db::{AsHashDB, HashDB, Hasher, Prefix, EMPTY_PREFIX};

use codec::{Decode, Encode};
use sp_core::offchain::{OffchainStorage, StorageKind};
use sp_io::offchain;
use sp_std::prelude::*;

#[derive(Default)]
pub struct AlternativeDB<L,T>
where
    L: TrieLayout + Send,
    T: Encode + Decode + Send,
{
    session_index: Vec<u8>,
    _phantom: core::marker::PhantomData<(T,L)>,
}


// @todo currently not true, just so it compiles
// @todo requires some internal mutability concept to work properly
unsafe impl<L,T> core::marker::Send for AlternativeDB<L,T> where
L: TrieLayout + Send,
T: Encode + Decode + Send,{}
unsafe impl<L,T> core::marker::Sync for AlternativeDB<L,T> where
L: TrieLayout + Send,
T: Encode + Decode + Send,{}

/// Session aware, Offchain DB based HashDB.
///
/// Creates two indices:
/// session -> [(key,tree_prefix),(key,tree_prefix),..]
/// session, tree_prefix -> [key,key,key,..]
impl<L,T> AlternativeDB<L,T>
where
L: TrieLayout + Send,
T: Encode + Decode + Send,
<L as TrieLayout>::Hash: Default,
<L as trie_db::TrieLayout>::Hash: core::default::Default + core::hash::BuildHasher,
<<L as trie_db::TrieLayout>::Hash as Hasher>::Out: AsRef<[u8]> + Default, //@todo verify this is true for all sane hashes such as H256
{
    pub fn prune(&self, key: &[u8]) {}

    /// set the session index for which to query the DB
    pub fn set_session<E: Encode>(&mut self, session_index: E) {
        self.session_index = session_index.encode();
    }

    fn add_to_indices(&self, key: &[u8], tree_prefix: &[u8]) {
        let mut mapping: Vec<(Vec<u8>, Vec<u8>)> =
            offchain::local_storage_get(StorageKind::PERSISTENT, key)
                .map(|mut bytes| {
                    <Vec<(Vec<u8>, Vec<u8>)> as Decode>::decode(&mut &bytes[..]).unwrap()
                })
                .unwrap_or_else(|| Vec::with_capacity(1));

        mapping.push((key.to_vec(), tree_prefix.to_vec()));

        let encoded = mapping.encode();
        offchain::local_storage_set(StorageKind::PERSISTENT, key, encoded.as_slice());
    }

    fn get_index_with_session(&self, session_index: &[u8]) -> Vec<(Vec<u8>, Vec<u8>)> {
        let key: Vec<u8> = tracking_index(session_index);
        let mapping: Vec<(Vec<u8>, Vec<u8>)> =
            offchain::local_storage_get(StorageKind::PERSISTENT, key.as_ref())
                .map(|mut bytes| {
                    <Vec<(Vec<u8>, Vec<u8>)> as Decode>::decode(&mut  &bytes[..]).unwrap()
                })
                .unwrap_or_else(|| Vec::with_capacity(8));
        mapping
    }

    /// Returns a vector of keys (which are vectors of bytes)
    fn get_index_with_session_and_prefix(
        &self,
        session_index: &[u8],
        tree_prefix: &[u8],
    ) -> Vec<Vec<u8>> {
        let key: Vec<u8> = tracking_index_with_prefix(tree_prefix, session_index);
        let mapping: Vec<Vec<u8>> =
            offchain::local_storage_get(StorageKind::PERSISTENT, key.as_ref())
                .map(|bytes| <Vec<Vec<u8>> as Decode>::decode(&mut &bytes[..]).unwrap())
                .unwrap_or_else(|| Vec::with_capacity(8));
        mapping
    }

    fn set_index_with_session(&self, session_index: &[u8], val: Vec<(Vec<u8>, Vec<u8>)>) {
        let key: Vec<u8> = tracking_index(session_index);
        let val = val.encode();
        offchain::local_storage_set(StorageKind::PERSISTENT, key.as_ref(), val.as_slice());
    }

    /// Returns a vector of keys (which are vectors of bytes)
    fn set_index_with_session_and_prefix(
        &self,
        session_index: &[u8],
        tree_prefix: &[u8],
        val: Vec<Vec<u8>>,
    ) {
        let key: Vec<u8> = tracking_index_with_prefix(tree_prefix, session_index);
        let val = val.encode();
        offchain::local_storage_set(StorageKind::PERSISTENT, key.as_ref(), val.as_slice());
    }

    fn remove_from_indices(&self, key: &[u8], tree_prefix: &[u8], session_index: &[u8]) {
        let mut index0 = self.get_index_with_session_and_prefix(session_index, tree_prefix);
        let index0 = index0
            .into_iter()
            .filter(|key2| key2.as_slice() != key)
            .collect();
        self.set_index_with_session_and_prefix(session_index, tree_prefix, index0);

        let mut index1 = self.get_index_with_session(session_index);
        let index1 = index1
            .into_iter()
            .filter(|(key2, tree_prefix2)| {
                tree_prefix2.as_slice() != tree_prefix || key2.as_slice() != key
            })
            .collect();
        self.set_index_with_session(session_index, index1);
    }
}

const TRACKING_PREFIX: &'static [u8] = b"__TRACKING__";

fn tracking_index_with_prefix(tree_prefix: &[u8], session_index: &[u8]) -> Vec<u8> {
    //@todo probably waaaaay to slow
    // _ + _ + _ + _
    let total_len = TRACKING_PREFIX.len() + 1 + session_index.len() + 1 + tree_prefix.len() + 1 + 2;
    let mut final_key = Vec::with_capacity(total_len);
    final_key.extend_from_slice(TRACKING_PREFIX);
    final_key.push(b'+');
    final_key.extend_from_slice(session_index);
    final_key.push(b'+');
    final_key.extend_from_slice(tree_prefix);
    final_key.push(b'+');
    final_key.extend_from_slice(tree_prefix);
    final_key.push(b'+');
    final_key
}

fn tracking_index(session_index: &[u8]) -> Vec<u8> {
    //@todo probably waaaaay to slow
    // _ + _ + _ + _
    let total_len = TRACKING_PREFIX.len() + 1 + session_index.len() + 1 + 2;
    let mut final_key = Vec::with_capacity(total_len);
    final_key.extend_from_slice(TRACKING_PREFIX);
    final_key.push(b'+');
    final_key.extend_from_slice(session_index);
    final_key.push(b'+');
    final_key
}

//@todo define the extra prefix
const PREFIX: &[u8] = b"TO_BE_DEFINED";

/// Concatenate the static prefix with a tree prefix.
fn prefix_glue(key: &[u8], tree_prefix: &[u8], session_index: &[u8]) -> Vec<u8> {
    //@todo probably waaaaay to slow
    // _ + _ + _ + _
    let total_len = PREFIX.len() + 1 + session_index.len() + 1 + key.len() + 1 + 2;
    let mut final_key = Vec::with_capacity(total_len);
    final_key.extend_from_slice(PREFIX);
    final_key.push(b'+');
    final_key.extend_from_slice(session_index);
    final_key.push(b'+');
    final_key.extend_from_slice(key);
    final_key.push(b'+');
    final_key.extend_from_slice(tree_prefix);
    final_key.push(b'+');
    final_key
}

impl<L, T> HashDB<L::Hash, T> for AlternativeDB<L,T>
where
    L: TrieLayout + Send,
    T: Encode + Decode + Send,
    <L as TrieLayout>::Hash: Default,
    <L as trie_db::TrieLayout>::Hash: core::default::Default + core::hash::BuildHasher,
    <<L as trie_db::TrieLayout>::Hash as Hasher>::Out: AsRef<[u8]> + Default, //@todo verify this is true for all sane hashes such as H256
{
    fn get(
        &self,
        key: &<<L as trie_db::TrieLayout>::Hash as Hasher>::Out,
        prefix: Prefix,
    ) -> Option<T> {
        let key = AsRef::<[u8]>::as_ref(key);
        let key: Vec<u8> = prefix_glue(
            key,
            prefix.encode().as_slice(),
            self.session_index.as_slice(),
        );
        offchain::local_storage_get(StorageKind::PERSISTENT, key.as_slice())
            .map(|mut v| Decode::decode(&mut &v[..]).unwrap())
    }

    fn contains(
        &self,
        key: &<<L as trie_db::TrieLayout>::Hash as Hasher>::Out,
        prefix: Prefix,
    ) -> bool {
        let key: &[u8] = AsRef::<[u8]>::as_ref(&*key);
        let key: Vec<u8> = prefix_glue(
            key,
            prefix.encode().as_slice(),
            self.session_index.as_slice(),
        );
        offchain::local_storage_get(StorageKind::PERSISTENT, key.as_slice()).is_some()
    }

    fn insert(
        &mut self,
        prefix: Prefix,
        value: &[u8],
    ) -> <<L as trie_db::TrieLayout>::Hash as Hasher>::Out {
        let digest = <<L as trie_db::TrieLayout>::Hash as Hasher>::hash(value);
        let key: Vec<u8> = prefix_glue(
            digest.as_ref(),
            prefix.encode().as_slice(),
            self.session_index.as_slice(),
        );
        offchain::local_storage_set(StorageKind::PERSISTENT, key.as_ref(), value);
        digest
    }

    fn emplace(
        &mut self,
        key: <<L as trie_db::TrieLayout>::Hash as Hasher>::Out,
        prefix: Prefix,
        value: T,
    ) {
        let key: Vec<u8> = prefix_glue(
            AsRef::<[u8]>::as_ref(&key),
            prefix.encode().as_slice(),
            self.session_index.as_slice(),
        );
        let value: Vec<u8> = <T as Encode>::encode(&value);
        Self::insert(self, (key.as_slice(), None), value.as_slice());
    }

    fn remove(&mut self, key: &<<L as trie_db::TrieLayout>::Hash as Hasher>::Out, prefix: Prefix) {
        //@todo no API for that just yet
        unimplemented!("can;t remove just yet")
    }
}

impl<L, T> AsHashDB<L::Hash, T> for AlternativeDB<L,T>
where
    L: TrieLayout + Send,
    T: Encode + Decode + Send,
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
