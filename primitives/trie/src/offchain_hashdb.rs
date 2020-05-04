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

use trie_db::Lookup;
use trie_db::node::{decode_hash, Node as EncodedNode, NodeHandle as EncodedNodeHandle};
use trie_db::{node::NodeKey, DBValue};
use trie_db::{CError, Result, TrieError, TrieHash, TrieLayout, TrieMut};

use hash_db::{HashDB, Hasher, Prefix, EMPTY_PREFIX};
use hashbrown::HashSet;

use crate::nibble::{nibble_ops, BackingByteVec, NibbleSlice, NibbleVec};
use crate::node_codec::NodeCodec;
use crate::rstd::{
    boxed::Box, convert::TryFrom, hash::Hash, mem, ops::Index, result, vec::Vec, VecDeque,
};

use sp_core::offchain;

use sp_staking::SessionIndex;
use sp_offchain::storage::Offchain;
use sp_offchain::storage::StorageKind;
use sp_offchain::StoragePrefix;
use trie_db::DBValue;
use codec::{Encode, Decode};

#[cfg(feature = "std")]
use log::trace;

#[cfg(feature = "std")]
use crate::rstd::fmt::{self, Debug};


#[derive(Default)]
pub struct AlternativeDB<L>
where
    L: TrieLayout,
{
	session: SessionIndex,
	_phantom: std::marker::PhantomData<L>,
}


/// Session aware, Offchain DB based HashDB.
///
/// Creates two indices:
/// session -> [(key,tree_prefix),(key,tree_prefix),..]
/// session, tree_prefix -> [key,key,key,..]
impl<L> AlternativeDB<L>
where
    L: TrieLayout,
{
	pub fn prune(&self, key: &[u8]) {

	}

	/// set the session index for which to query the DB
	pub fn set_session(&mut self, session: SessionIndex) {
		self.session = session;
	}


	fn add_to_indices(&self, key: &[u8], tree_prefix: &[u8]) {
		let mut mapping : Vec<(Vec<u8>,Vec<u8>)> = offchain::local_storage_get(StorageKind::PERSISTENT, key).map(|bytes| {
			<Vec<(Vec<u8>,Vec<u8>)> as Decode>::decode().unwrap(bytes.as_slice())
		}).ok().unwrap_or_else(|| Vec::with_capacity(1));
		mapping.push((key.to_vec(),value.to_vec()));
		let encoded = mapping.encode();
		offchain::local_storage_set(StorageKind::PERSISTENT, key, encoded.as_slice());
	}

	fn get_index_with_session(&self, session_index: SessionIndex) -> Vec<(Vec<u8>,Vec<u8>)> {
		let key: Vec<u8> = tracking_index(self.session_index);
		let mut mapping : Vec<(Vec<u8>,Vec<u8>)> = offchain::local_storage_get(StorageKind::PERSISTENT, key).map(|bytes| {
			<Vec<(Vec<u8>,Vec<u8>)> as Decode>::decode(bytes.as_slice()).unwrap()
		}).ok().unwrap_or_else(|| { Vec::with_capacity(1)})
	}

	/// Returns a vector of keys (which are vectors of bytes)
	fn get_index_with_session_and_prefix(&self, session_index: SessionIndex, tree_prefix: &[u8]) -> Vec<Vec<u8>> {
		let key: Vec<u8> = tracking_tracking_index_with_prefix(prefix, self.session_index);
		let mut mapping : Vec<Vec<u8>> = offchain::local_storage_get(StorageKind::PERSISTENT, key).map(|bytes| {
			<Vec<Vec<u8>> as Decode>::decode(bytes.as_slice()).unwrap()
		}).ok().unwrap_or_else(|| Vec::with_capacity(1))
	}


	fn set_index_with_session(&self, session_index: SessionIndex, val: Vec<(Vec<u8>,Vec<u8>)> ) {
		let key: Vec<u8> = tracking_index(self.session_index);
		offchain::local_storage_set(StorageKind::PERSISTENT, key, val.encode());
	}

	/// Returns a vector of keys (which are vectors of bytes)
	fn set_index_with_session_and_prefix(&self, session_index: SessionIndex, tree_prefix: &[u8], val: Vec<Vec<u8>>) {
		let key: Vec<u8> = tracking_tracking_index_with_prefix(prefix, self.session_index);
		offchain::local_storage_set(StorageKind::PERSISTENT, key, val.encode());
	}

	fn remove_from_indices(&self, key: &[u8], tree_prefix: &[u8], session_index: SessionIndex) {
		let mut index0 = self.index_with_session_and_prefix(session_index, tree_prefix);
		let index0 = index0
			.into_iter()
			.filter(|key2,tree_prefix2| { tree_prefix2 != tree_prefix || key2 != key })
			.collect();
		self.set_index_with_session_and_prefix(session_index, tree_prefix, index0);

		let mut index1 = self.index_with_session(session_index);
		let index1 = index1
			.into_iter()
			.filter(|key2| { key2 != key })
			.collect();
		self.set_index_with_session(session_index, index1);
	}

}


const TRACKING_PREFIX : &'static [u8] = "__TRACKING__";

fn tracking_index_with_prefix(tree_prefix: Prefix, session_index: SessionIndex) -> Vec<u8> {
	let session_index = session_index.to_be_bytes().as_slice();
	//@todo probably waaaaay to slow
	// _ + _ + _ + _
	let total_len = TRACKING_PREFIX.len() + 1 + session_index.len() + 1 + tree_prefix.0.len() + 1 + tree_prefix.1.is_some() + 1 + 2;
	let mut final_key = Vec::with_capacity(total_len);
	final_key.extend_from_slice(TRACKING_PREFIX);
	final_key.push(b'+');
	final_key.extend_from_slice(session_index);
	final_key.push(b'+');
	final_key.extend_from_slice(tree_prefix);
	final_key.push(b'+');
	if let Some(nibble) = tree_prefix.1 {
		final_key.push(nibble);
	}
}

fn tracking_index(tree_prefix: Prefix, session_index: SessionIndex) -> Vec<u8> {
	let session_index = session_index.to_be_bytes().as_slice();
	//@todo probably waaaaay to slow
	// _ + _ + _ + _
	let total_len = TRACKING_PREFIX.len() + 1 + session_index.len() + 1 + tree_prefix.0.len() + 1 + tree_prefix.1.is_some() + 1 + 2;
	let mut final_key = Vec::with_capacity(total_len);
	final_key.extend_from_slice(TRACKING_PREFIX);
	final_key.push(b'+');
	final_key.extend_from_slice(session_index);
	final_key.push(b'+');
	if let Some(nibble) = tree_prefix.1 {
		final_key.push(nibble);
	}
}



//@todo define the extra prefix
const PREFIX: &'static [u8] = &b"TO_BE_DEFINED";

/// Concatenate the static prefix with a tree prefix.
fn prefix_glue(key: &[u8], tree_prefix: Prefix, session_index: SessionIndex) -> Vec<u8> {
	let session_index = session_index.to_be_bytes().as_slice();
	//@todo probably waaaaay to slow
	// _ + _ + _ + _
	let total_len = PREFIX.len() + 1 + session_index.len() + 1 + key.len() + 1 + tree_prefix.0.len() + 1 + tree_prefix.1.is_some() + 1 + 2;
	let mut final_key = Vec::with_capacity(total_len);
	final_key.extend_from_slice(PREFIX);
	final_key.push(b'+');
	final_key.extend_from_slice(session_index);
	final_key.push(b'+');
	final_key.extend_from_slice(key);
	final_key.push(b'+');
	final_key.extend_from_slice(tree_prefix);
	final_key.push(b'+');
	if let Some(nibble) = tree_prefix.1 {
		final_key.push(nibble);
	}
}

impl<L,T> HashDB<L::Hash, T> for AlternativeDB<L>
where
	L: TrieLayout,
	T: Encode,
	<<L as trie_db::TrieLayout>::Hash as Trait>::Out: AsRef<u8> + Default, //@todo verify this is true for all sane hashes such as H256
{

	fn get(&self, key: &<<L as trie_db::TrieLayout>::Hash as Trait>::Out, prefix: Prefix) -> Option<T> {
		let key: Vec<u8> = prefix_glue(key.as_ref(), prefix, self.session_index);
		offchain::local_storage_get(StorageKind::PERSISTENT, key).ok().flatten()
	}

	fn contains(&self, key: &<<L as trie_db::TrieLayout>::Hash as Trait>::Out, prefix: Prefix) -> bool {
		let key: Vec<u8> = prefix_glue(key.as_ref(), prefix, self.session_index);
		offchain::local_storage_set(StorageKind::PERSISTENT, key).ok().flatten().is_some()
	}

	fn insert(&mut self, prefix: Prefix, value: &[u8]) -> H::Out {
		let hasher = L::Hash::default();
		let digest = hasher.hash(value);
		let key: Vec<u8> = prefix_glue(digest.as_ref(), prefix, self.session_index);
		offchain::local_storage_set(StorageKind::PERSISTENT, key, value);
		digest
	}

	fn emplace(&mut self, key: <<L as trie_db::TrieLayout>::Hash as Trait>::Out, prefix: Prefix, value: T) {
		let key: Vec<u8> = prefix_glue(key.as_ref(), prefix);
		let value : Vec<u8> = value.encode();
		self.insert(prefix, value.as_slice());
	}

	fn remove(&mut self, key: &<<L as trie_db::TrieLayout>::Hash as Trait>::Out, prefix: Prefix) {
		//@todo no API for that just yet

	}
}
