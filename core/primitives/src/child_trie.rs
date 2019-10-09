// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Child trie related primitives 

use codec::{Encode, Decode, Compact};
use rstd::prelude::*;
use rstd::ptr;
use crate::storage::well_known_keys::CHILD_STORAGE_KEY_PREFIX;
#[cfg(feature = "std")]
pub use impl_serde::serialize as bytes;
use hash_db::Prefix;

/// `KeySpace` type contains a unique child trie identifier.
/// It is used to isolate a child trie in its backing database.
/// This is done by prefixing its key with this value.
///
/// A keyspace byte representation must not be the start of another
/// keyspace byte representation (otherwhise conflict may happen).
/// This guaranty is provided by the fact that keyspace is a scale
/// encoded representation.
///
/// From a `TrieDB` perspective, accessing a child trie content 
/// will requires both the child trie root, but also the `KeySpace`.
///
/// The `KeySpace` of a child trie must be unique for the canonical chain.
/// This unicity is currently guaranted by build from a simple counter.
///
/// If a child trie was to be moved between two chains, the underlying
/// key value would be all the keyvaluedb prefixed by this keyspace.
/// Moving those key will still need for every content to change keyspace
/// of the origin chain with a new keyspace of a destination chain.
/// Please notice that usage of keyspace on ALL data makes it possible,
/// 
/// The same thing is true for a child trie deletion, there is no need to
/// remove all historic of state child trie keypair from a multiple TrieDB
/// perspective, but simply all keyvaluedb content with a key starting with
/// this keyspace.
pub type KeySpace = Vec<u8>;


/// Keyspace to use for the parent trie key.
pub const NO_CHILD_KEYSPACE: [u8;1] = [0];


/// Produce a new keyspace from current state counter.
pub fn produce_keyspace(child_counter: u128) -> Vec<u8> {
	codec::Encode::encode(&Compact(child_counter))
}

/// Decode keyspace to original counter value.
pub fn reverse_keyspace(keyspace: &[u8]) -> Result<u128, codec::Error> {
	<Compact<u128>>::decode(&mut &keyspace[..]).map(|c| c.0)
}

// see FIXME #2741 for removal of this allocation on every operation.
// Simplest would be to put an additional optional field in prefix.
/// Utility function used for merging `KeySpace` data and `prefix` data
/// before calling key value database primitives.
pub fn keyspace_as_prefix_alloc(ks: Option<&KeySpace>, prefix: Prefix) -> (Vec<u8>, Option<u8>) {
	let ks = ks.map(|ks| ks.as_slice()).unwrap_or(&NO_CHILD_KEYSPACE[..]);
	let mut result = rstd::vec![0; ks.len() + prefix.0.len()];
	result[..ks.len()].copy_from_slice(ks);
	result[ks.len()..].copy_from_slice(prefix.0);
	(result, prefix.1)
}

#[test]
fn encode_empty_prefix() {
	let empty = produce_keyspace(0);

	assert_eq!(&NO_CHILD_KEYSPACE[..], &empty[..]);
}

#[test]
fn keyspace_codec() {
	let sample: [u128; 3] = [0, 1, 1_000_000];
	for s in sample.iter() {
		let keyspace = produce_keyspace(*s);
		let dec_keyspace = reverse_keyspace(keyspace.as_slice()).unwrap();
		assert_eq!(*s, dec_keyspace);
	}
}
