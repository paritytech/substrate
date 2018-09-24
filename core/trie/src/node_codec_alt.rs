// Copyright 2015-2018 Parity Technologies (UK) Ltd.
// This file is part of Parity.

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

//! `NodeCodec` implementation for Rlp

use std::marker::PhantomData;
use patricia_trie::{DBValue, NibbleSlice, NodeCodec, node::Node, ChildReference, Hasher};
use codec::{Encode, Decode, Compact};
use codec_error::CodecError;
use codec_triestream::{EMPTY_TRIE, LEAF_NODE_OFFSET, LEAF_NODE_BIG, EXTENSION_NODE_OFFSET,
	EXTENSION_NODE_BIG, branch_node};
use super::{take, partial_to_key, node_len, node_header::NodeHeader};

/// Concrete implementation of a `NodeCodec` with Parity Codec encoding, generic over the `Hasher`
#[derive(Default, Clone)]
pub struct ParityNodeCodecAlt<H: Hasher>(PhantomData<H>);

// NOTE: what we'd really like here is:
// `impl<H: Hasher> NodeCodec<H> for RlpNodeCodec<H> where H::Out: Decodable`
// but due to the current limitations of Rust const evaluation we can't
// do `const HASHED_NULL_NODE: H::Out = H::Out( … … )`. Perhaps one day soon?
impl<H: Hasher> NodeCodec<H> for ParityNodeCodecAlt<H> {
	type Error = CodecError;

	fn hashed_null_node() -> H::Out {
		H::hash(&[0u8][..])
	}

	fn decode(data: &[u8]) -> ::std::result::Result<Node, Self::Error> {
		//println!("decoding... {:#x?}", data);
		let input = &mut &*data;
		let r = match NodeHeader::decode(input).ok_or(CodecError::BadFormat)? {
			NodeHeader::Null => Ok(Node::Empty),
			NodeHeader::Branch(has_value) => {
//				//println!("decode: branch({})", has_value);
				let bitmap = u16::decode(input).ok_or(CodecError::BadFormat)?;
				let value = if has_value {
					let count = <Compact<u32>>::decode(input).ok_or(CodecError::BadFormat)?.0 as usize;
					Some(take(input, count).ok_or(CodecError::BadFormat)?)
				} else {
					None
				};
				let mut children = [None; 16];
				let mut pot_cursor = 1;
				for i in 0..16 {
					if bitmap & pot_cursor != 0 {
						let count = node_len(*input, H::LENGTH).ok_or(CodecError::BadFormat)?.0;
						children[i] = Some(take(input, count).ok_or(CodecError::BadFormat)?);
					}
					pot_cursor <<= 1;
				}
				Ok(Node::Branch(children, value))
			}
			NodeHeader::Extension(nibble_count) => {
//				//println!("decode: ext({})", nibble_count);
				let nibble_data = take(input, (nibble_count + 1) / 2).ok_or(CodecError::BadFormat)?;
				let nibble_slice = NibbleSlice::new_offset(nibble_data, nibble_count % 2);
//				//println!("decode: ext: nibble_slice({:?})", nibble_slice);
				let count = node_len(*input, H::LENGTH).ok_or(CodecError::BadFormat)?.0;
//				//println!("decode: ext: node_len {}", count);
				Ok(Node::Extension(nibble_slice, take(input, count).ok_or(CodecError::BadFormat)?))
			}
			NodeHeader::Leaf(nibble_count) => {
//				//println!("decode: leaf({})", nibble_count);
				let nibble_data = take(input, (nibble_count + 1) / 2).ok_or(CodecError::BadFormat)?;
				let nibble_slice = NibbleSlice::new_offset(nibble_data, nibble_count % 2);
				let count = <Compact<u32>>::decode(input).ok_or(CodecError::BadFormat)?.0 as usize;
				Ok(Node::Leaf(nibble_slice, take(input, count).ok_or(CodecError::BadFormat)?))
			}
		};
		//println!("decode: {:#x?} -> {:#x?}", data, r);
		r
	}

	fn try_decode_hash(data: &[u8]) -> Option<H::Out> {
		let r = if data.len() == H::LENGTH + 1 && data[0] == EMPTY_TRIE {
			let mut r = H::Out::default();
			r.as_mut().copy_from_slice(&data[1..]);
			Some(r)
		} else {
			None
		};
		//println!("try_decode_hash: {:#x?} -> {:#x?}", data, r);
		r
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
		//println!("leaf_node: {:#x?}", output);
		output
	}

	// TODO: refactor this so that `partial` isn't already encoded with HPE. Should just be an `impl Iterator<Item=u8>`.
	fn ext_node(partial: &[u8], child: ChildReference<H::Out>) -> Vec<u8> {
		let mut output = partial_to_key(partial, EXTENSION_NODE_OFFSET, EXTENSION_NODE_BIG);
		match child {
			ChildReference::Hash(h) => {
				output.push(EMPTY_TRIE);
				output.extend_from_slice(h.as_ref());
			}
			ChildReference::Inline(inline_data, len) =>
				output.extend_from_slice(&AsRef::<[u8]>::as_ref(&inline_data)[..len]),
		};
		//println!("ext_node: {:#x?}", output);
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
				output.push(EMPTY_TRIE);
				output.extend_from_slice(h.as_ref());
				true
			}
			Some(ChildReference::Inline(inline_data, len)) => {
				output.extend_from_slice(&AsRef::<[u8]>::as_ref(&inline_data)[..len]);
				true
			}
			None => false,
		}));
		output[0..3].copy_from_slice(&prefix[..]);
		//println!("branch_node: {:#x?}", output);
		output
	}
}
