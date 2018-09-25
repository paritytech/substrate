// Copyright 2015-2018 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Parity is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Parity is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Parity.  If not, see <http://www.gnu.org/licenses/>.

//! `NodeCodec` implementation for Substrate's trie format.

use std::marker::PhantomData;
use codec::{Encode, Decode, Compact};
use hash_db::Hasher;
use trie_db::{self, DBValue, NibbleSlice, node::Node, ChildReference};
use error::Error;
use super::{EMPTY_TRIE, LEAF_NODE_OFFSET, LEAF_NODE_BIG, EXTENSION_NODE_OFFSET,
	EXTENSION_NODE_BIG, take, partial_to_key, node_header::NodeHeader, branch_node};

/// Concrete implementation of a `NodeCodec` with Parity Codec encoding, generic over the `Hasher`
#[derive(Default, Clone)]
pub struct NodeCodec<H: Hasher>(PhantomData<H>);

// NOTE: what we'd really like here is:
// `impl<H: Hasher> NodeCodec<H> for RlpNodeCodec<H> where H::Out: Decodable`
// but due to the current limitations of Rust const evaluation we can't
// do `const HASHED_NULL_NODE: H::Out = H::Out( … … )`. Perhaps one day soon?
impl<H: Hasher> trie_db::NodeCodec<H> for NodeCodec<H> {
	type Error = Error;

	fn hashed_null_node() -> H::Out {
		H::hash(&[0u8][..])
	}

	fn decode(data: &[u8]) -> ::std::result::Result<Node, Self::Error> {
		use Error::BadFormat;
		let input = &mut &*data;
		match NodeHeader::decode(input).ok_or(BadFormat)? {
			NodeHeader::Null => Ok(Node::Empty),
			NodeHeader::Branch(has_value) => {
				let bitmap = u16::decode(input).ok_or(BadFormat)?;
				let value = if has_value {
					let count = <Compact<u32>>::decode(input).ok_or(BadFormat)?.0 as usize;
					Some(take(input, count).ok_or(BadFormat)?)
				} else {
					None
				};
				let mut children = [None; 16];
				let mut pot_cursor = 1;
				for i in 0..16 {
					if bitmap & pot_cursor != 0 {
						let count = <Compact<u32>>::decode(input).ok_or(BadFormat)?.0 as usize;
						children[i] = Some(take(input, count).ok_or(BadFormat)?);
					}
					pot_cursor <<= 1;
				}
				Ok(Node::Branch(children, value))
			}
			NodeHeader::Extension(nibble_count) => {
				let nibble_data = take(input, (nibble_count + 1) / 2).ok_or(BadFormat)?;
				let nibble_slice = NibbleSlice::new_offset(nibble_data, nibble_count % 2);
				let count = <Compact<u32>>::decode(input).ok_or(BadFormat)?.0 as usize;
				Ok(Node::Extension(nibble_slice, take(input, count).ok_or(BadFormat)?))
			}
			NodeHeader::Leaf(nibble_count) => {
				let nibble_data = take(input, (nibble_count + 1) / 2).ok_or(BadFormat)?;
				let nibble_slice = NibbleSlice::new_offset(nibble_data, nibble_count % 2);
				let count = <Compact<u32>>::decode(input).ok_or(BadFormat)?.0 as usize;
				Ok(Node::Leaf(nibble_slice, take(input, count).ok_or(BadFormat)?))
			}
		}
	}

	fn try_decode_hash(data: &[u8]) -> Option<H::Out> {
		if data.len() == H::LENGTH {
			let mut r = H::Out::default();
			r.as_mut().copy_from_slice(data);
			Some(r)
		} else {
			None
		}
	}

	fn is_empty_node(data: &[u8]) -> bool {
		data == &[EMPTY_TRIE][..]
	}
	fn empty_node() -> Vec<u8> {
		vec![EMPTY_TRIE]
	}

	// TODO: refactor this so that `partial` isn't already encoded with HPE. Should just be an `impl Iterator<Item=u8>`.
	fn leaf_node(partial: &[u8], value: &[u8]) -> Vec<u8> {
		let mut output = partial_to_key(partial, LEAF_NODE_OFFSET, LEAF_NODE_BIG);
		value.encode_to(&mut output);
		output
	}

	// TODO: refactor this so that `partial` isn't already encoded with HPE. Should just be an `impl Iterator<Item=u8>`.
	fn ext_node(partial: &[u8], child: ChildReference<H::Out>) -> Vec<u8> {
		let mut output = partial_to_key(partial, EXTENSION_NODE_OFFSET, EXTENSION_NODE_BIG);
		match child {
			ChildReference::Hash(h) => 
				h.as_ref().encode_to(&mut output),
			ChildReference::Inline(inline_data, len) =>
				(&AsRef::<[u8]>::as_ref(&inline_data)[..len]).encode_to(&mut output),
		};
		output
	}

	fn branch_node<I>(children: I, maybe_value: Option<DBValue>) -> Vec<u8>
		where I: IntoIterator<Item=Option<ChildReference<H::Out>>> + Iterator<Item=Option<ChildReference<H::Out>>>
	{
		let mut output = vec![0, 0, 0];
		let have_value = if let Some(value) = maybe_value {
			(&*value).encode_to(&mut output);
			true
		} else {
			false
		};
		let prefix = branch_node(have_value, children.map(|maybe_child| match maybe_child {
			Some(ChildReference::Hash(h)) => {
				h.as_ref().encode_to(&mut output);
				true
			}
			Some(ChildReference::Inline(inline_data, len)) => {
				(&AsRef::<[u8]>::as_ref(&inline_data)[..len]).encode_to(&mut output);
				true
			}
			None => false,
		}));
		output[0..3].copy_from_slice(&prefix[..]);
		output
	}
}
