// Copyright 2015-2019 Parity Technologies (UK) Ltd.
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

use rstd::marker::PhantomData;
use rstd::vec::Vec;
use rstd::borrow::Borrow;
use codec::{Encode, Decode, Compact};
use hash_db::Hasher;
use trie_db::{self, NibbleSlice, node::Node, ChildReference,
	nibble_ops, Partial, NodeCodec as NodeCodecT};
use crate::error::Error;
use crate::trie_constants;
use super::{node_header::{NodeHeader, NodeKind}};

fn take<'a>(input: &mut &'a[u8], count: usize) -> Option<&'a[u8]> {
	if input.len() < count {
		return None
	}
	let r = &(*input)[..count];
	*input = &(*input)[count..];
	Some(r)
}

/// Concrete implementation of a `NodeCodec` with Parity Codec encoding, generic over the `Hasher`
#[derive(Default, Clone)]
pub struct NodeCodec<H>(PhantomData<H>);

impl<H: Hasher> NodeCodecT<H> for NodeCodec<H> {
	type Error = Error;

	fn hashed_null_node() -> <H as Hasher>::Out {
		H::hash(<Self as NodeCodecT<_>>::empty_node())
	}

	fn decode(data: &[u8]) -> rstd::result::Result<Node, Self::Error> {
		let input = &mut &*data;
		let head = NodeHeader::decode(input).ok_or(Error::BadFormat)?;
		match head {
			NodeHeader::Null => Ok(Node::Empty),
			NodeHeader::Branch(has_value, nibble_count) => {
				let padding = nibble_count % nibble_ops::NIBBLE_PER_BYTE != 0;
				// check that the padding is valid (if any)
				if padding && nibble_ops::pad_left(input[0]) != 0 {
					return Err(Error::BadFormat);
				}
				let nibble_data = take(
					input,
					(nibble_count + (nibble_ops::NIBBLE_PER_BYTE - 1)) / nibble_ops::NIBBLE_PER_BYTE,
				).ok_or(Error::BadFormat)?;
				let nibble_slice = NibbleSlice::new_offset(
					nibble_data,
					nibble_ops::number_padding(nibble_count),
				);
				let bitmap_slice = take(input, BITMAP_LENGTH).ok_or(Error::BadFormat)?;
				let bitmap = Bitmap::decode(&bitmap_slice[..])?;
				let value = if has_value {
					let count = <Compact<u32>>::decode(input).ok_or(Error::BadFormat)?.0 as usize;
					Some(take(input, count).ok_or(Error::BadFormat)?)
				} else {
					None
				};
				let mut children = [None; 16];

				for i in 0..nibble_ops::NIBBLE_LENGTH {
					if bitmap.value_at(i) {
						let count = <Compact<u32>>::decode(input).ok_or(Error::BadFormat)?.0 as usize;
						children[i] = Some(take(input, count).ok_or(Error::BadFormat)?);
					}
				}
				Ok(Node::NibbledBranch(nibble_slice, children, value))
			}
			NodeHeader::Leaf(nibble_count) => {
				let padding = nibble_count % nibble_ops::NIBBLE_PER_BYTE != 0;
				// check that the padding is valid (if any)
				if padding && nibble_ops::pad_left(input[0]) != 0 {
					return Err(Error::BadFormat);
				}
				let nibble_data = take(
					input,
					(nibble_count + (nibble_ops::NIBBLE_PER_BYTE - 1)) / nibble_ops::NIBBLE_PER_BYTE,
				).ok_or(Error::BadFormat)?;
				let nibble_slice = NibbleSlice::new_offset(
					nibble_data,
					nibble_ops::number_padding(nibble_count),
				);
				let count = <Compact<u32>>::decode(input).ok_or(Error::BadFormat)?.0 as usize;
				Ok(Node::Leaf(nibble_slice, take(input, count).ok_or(Error::BadFormat)?))
			}
		}
	}

	fn try_decode_hash(data: &[u8]) -> Option<<H as Hasher>::Out> {
		if data.len() == H::LENGTH {
			let mut r = <H as Hasher>::Out::default();
			r.as_mut().copy_from_slice(data);
			Some(r)
		} else {
			None
		}
	}

	fn is_empty_node(data: &[u8]) -> bool {
		data == <Self as NodeCodecT<_>>::empty_node()
	}

	fn empty_node() -> &'static [u8] {
		&[trie_constants::EMPTY_TRIE]
	}

	fn leaf_node(partial: Partial, value: &[u8]) -> Vec<u8> {
		let mut output = partial_encode(partial, NodeKind::Leaf);
		value.encode_to(&mut output);
		output
	}

	fn extension_node(
		_partial: impl Iterator<Item = u8>,
		_nbnibble: usize,
		_child: ChildReference<<H as Hasher>::Out>,
	) -> Vec<u8> {
		unreachable!()
	}

	fn branch_node(
		_children: impl Iterator<Item = impl Borrow<Option<ChildReference<<H as Hasher>::Out>>>>,
		_maybe_value: Option<&[u8]>,
	) -> Vec<u8> {
		unreachable!()
	}

	fn branch_node_nibbled(
		partial: impl Iterator<Item = u8>,
		number_nibble: usize,
		children: impl Iterator<Item = impl Borrow<Option<ChildReference<<H as Hasher>::Out>>>>,
		maybe_value: Option<&[u8]>,
	) -> Vec<u8> {
		let mut output = if maybe_value.is_some() {
			partial_from_iterator_encode(partial, number_nibble, NodeKind::BranchWithValue)
		} else {
			partial_from_iterator_encode(partial, number_nibble, NodeKind::BranchNoValue)
		};
		let bitmap_index = output.len();
		let mut bitmap: [u8; BITMAP_LENGTH] = [0; BITMAP_LENGTH];
		(0..BITMAP_LENGTH).for_each(|_|output.push(0));
		if let Some(value) = maybe_value {
			value.encode_to(&mut output);
		};
		Bitmap::encode(children.map(|maybe_child| match maybe_child.borrow() {
			Some(ChildReference::Hash(h)) => {
				h.as_ref().encode_to(&mut output);
				true
			}
			&Some(ChildReference::Inline(inline_data, len)) => {
				inline_data.as_ref()[..len].encode_to(&mut output);
				true
			}
			None => false,
		}), bitmap.as_mut());
		output[bitmap_index..bitmap_index + BITMAP_LENGTH]
			.copy_from_slice(&bitmap.as_ref()[..BITMAP_LENGTH]);
		output
	}

}

// utils

/// Encode and allocate node type header (type and size), and partial value.
/// It uses an iterator over encoded partial bytes as input.
fn partial_from_iterator_encode<I: Iterator<Item = u8>>(
	partial: I,
	nibble_count: usize,
	node_kind: NodeKind,
) -> Vec<u8> {
	let nibble_count = rstd::cmp::min(trie_constants::NIBBLE_SIZE_BOUND, nibble_count);

	let mut output = Vec::with_capacity(3 + (nibble_count / nibble_ops::NIBBLE_PER_BYTE));
	match node_kind {
		NodeKind::Leaf => NodeHeader::Leaf(nibble_count).encode_to(&mut output),
		NodeKind::BranchWithValue => NodeHeader::Branch(true, nibble_count).encode_to(&mut output),
		NodeKind::BranchNoValue => NodeHeader::Branch(false, nibble_count).encode_to(&mut output),
	};
	output.extend(partial);
	output
}

/// Encode and allocate node type header (type and size), and partial value.
/// Same as `partial_from_iterator_encode` but uses non encoded `Partial` as input.
fn partial_encode(partial: Partial, node_kind: NodeKind) -> Vec<u8> {
	let number_nibble_encoded = (partial.0).0 as usize;
	let nibble_count = partial.1.len() * nibble_ops::NIBBLE_PER_BYTE + number_nibble_encoded;

	let nibble_count = rstd::cmp::min(trie_constants::NIBBLE_SIZE_BOUND, nibble_count);

	let mut output = Vec::with_capacity(3 + partial.1.len());
	match node_kind {
		NodeKind::Leaf => NodeHeader::Leaf(nibble_count).encode_to(&mut output),
		NodeKind::BranchWithValue => NodeHeader::Branch(true, nibble_count).encode_to(&mut output),
		NodeKind::BranchNoValue => NodeHeader::Branch(false, nibble_count).encode_to(&mut output),
	};
	if number_nibble_encoded > 0 {
		output.push(nibble_ops::pad_right((partial.0).1));
	}
	output.extend_from_slice(&partial.1[..]);
	output
}

const BITMAP_LENGTH: usize = 2;

/// Radix 16 trie, bitmap encoding implementation,
/// it contains children mapping information for a branch
/// (children presence only), it encodes into
/// a compact bitmap encoding representation.
pub(crate) struct Bitmap(u16);

impl Bitmap {

	pub fn decode(data: &[u8]) -> Result<Self, Error> {
		u16::decode(&mut &data[..])
			.ok_or(Error::BadFormat)
			.map(|v|Bitmap(v))
	}

	pub fn value_at(&self, i: usize) -> bool {
		self.0 & (1u16 << i) != 0
	}

	pub fn encode<I: Iterator<Item = bool>>(has_children: I , dest: &mut [u8]) {
		let mut bitmap: u16 = 0;
		let mut cursor: u16 = 1;
		for v in has_children {
			if v { bitmap |= cursor }
			cursor <<= 1;
		}
		dest[0] = (bitmap % 256) as u8;
		dest[1] = (bitmap / 256) as u8;
	}
}

