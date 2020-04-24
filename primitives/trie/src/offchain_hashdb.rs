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

use super::lookup::Lookup;
use super::node::{decode_hash, Node as EncodedNode, NodeHandle as EncodedNodeHandle};
use super::{node::NodeKey, DBValue};
use super::{CError, Result, TrieError, TrieHash, TrieLayout, TrieMut};

use hash_db::{HashDB, Hasher, Prefix, EMPTY_PREFIX};
use hashbrown::HashSet;

use crate::nibble::{nibble_ops, BackingByteVec, NibbleSlice, NibbleVec};
use crate::node_codec::NodeCodec;
use crate::rstd::{
    boxed::Box, convert::TryFrom, hash::Hash, mem, ops::Index, result, vec::Vec, VecDeque,
};

use sp_core::offchain;

use sp_offchain::storage::Offchain;
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
    _phantom: std::marker::PhantomData<L>,
}


//@todo define the extra prefix
const PREFIX: &'static [u8] = &b"TO_BE_DEFINED";

/// Concatenate the static prefix with a tree prefix.
fn prefix_glue(key: &[u8], tree_prefix: Prefix) -> Vec<u8> {
	//@todo probably waaaaay to slow
	// _ + _ + _ + _
	let total_len = PREFIX.len() + key.len() + 1 + tree_prefix.0.len() + 1 + tree_prefix.1.is_some() + 1 + 2;
	let mut final_key = Vec::with_capacity(total_len);
	final_key.extend_from_slice(PREFIX);
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
	L::Hash::Out: AsRef<u8> + Default, //@todo verify this is true for all sane hashes such as H256
{
	fn get(&self, key: &L::Hash::Out, prefix: Prefix) -> Option<T> {
		offchain::local_storage_get(StorageKind::PERSISTENT, key).ok().flatten()
	}

	fn contains(&self, key: &L::Hash::Out, prefix: Prefix) -> bool {
		let key: Vec<u8> = prefix_glue(key.as_ref(), prefix);
		offchain::local_storage_set(StorageKind::PERSISTENT, key).ok().flatten().is_some()
	}

	fn insert(&mut self, prefix: Prefix, value: &[u8]) -> H::Out {
		let hasher = L::Hash::default();
		let digest = hasher.hash(value);
		let key: Vec<u8> = prefix_glue(digest.as_ref(), prefix);
		offchain::local_storage_set(StorageKind::PERSISTENT, key, value);
		digest
	}

	fn emplace(&mut self, key: L::Hash::Out, prefix: Prefix, value: T) {
		let key: Vec<u8> = prefix_glue(key.as_ref(), prefix);
		let value : Vec<u8> = value.encode();
		self.insert(prefix, value.as_slice());
	}

	fn remove(&mut self, key: &L::Hash::Out, prefix: Prefix) {
		//@todo no API for that just yet
		offchain::
	}
}
