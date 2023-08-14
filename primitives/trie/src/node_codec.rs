// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! `NodeCodec` implementation for Substrate's trie format.

use super::node_header::{NodeHeader, NodeKind};
use crate::{error::Error, trie_constants};
use codec::{Compact, Decode, Encode, Input};
use hash_db::Hasher;
use sp_std::{borrow::Borrow, marker::PhantomData, ops::Range, vec::Vec};
use trie_db::{
	nibble_ops,
	node::{NibbleSlicePlan, NodeHandlePlan, NodePlan, Value, ValuePlan},
	ChildReference, NodeCodec as NodeCodecT,
};

/// Helper struct for trie node decoder. This implements `codec::Input` on a byte slice, while
/// tracking the absolute position. This is similar to `std::io::Cursor` but does not implement
/// `Read` and `io` is not in `sp-std`.
struct ByteSliceInput<'a> {
	data: &'a [u8],
	offset: usize,
}

impl<'a> ByteSliceInput<'a> {
	fn new(data: &'a [u8]) -> Self {
		ByteSliceInput { data, offset: 0 }
	}

	fn take(&mut self, count: usize) -> Result<Range<usize>, codec::Error> {
		if self.offset + count > self.data.len() {
			return Err("out of data".into())
		}

		let range = self.offset..(self.offset + count);
		self.offset += count;
		Ok(range)
	}
}

impl<'a> Input for ByteSliceInput<'a> {
	fn remaining_len(&mut self) -> Result<Option<usize>, codec::Error> {
		Ok(Some(self.data.len().saturating_sub(self.offset)))
	}

	fn read(&mut self, into: &mut [u8]) -> Result<(), codec::Error> {
		let range = self.take(into.len())?;
		into.copy_from_slice(&self.data[range]);
		Ok(())
	}

	fn read_byte(&mut self) -> Result<u8, codec::Error> {
		if self.offset + 1 > self.data.len() {
			return Err("out of data".into())
		}

		let byte = self.data[self.offset];
		self.offset += 1;
		Ok(byte)
	}
}

/// Concrete implementation of a [`NodeCodecT`] with SCALE encoding.
///
/// It is generic over `H` the [`Hasher`].
#[derive(Default, Clone)]
pub struct NodeCodec<H>(PhantomData<H>);

impl<H> NodeCodecT for NodeCodec<H>
where
	H: Hasher,
{
	const ESCAPE_HEADER: Option<u8> = Some(trie_constants::ESCAPE_COMPACT_HEADER);
	type Error = Error<H::Out>;
	type HashOut = H::Out;

	fn hashed_null_node() -> <H as Hasher>::Out {
		H::hash(<Self as NodeCodecT>::empty_node())
	}

	fn decode_plan(data: &[u8]) -> Result<NodePlan, Self::Error> {
		let mut input = ByteSliceInput::new(data);

		let header = NodeHeader::decode(&mut input)?;
		let contains_hash = header.contains_hash_of_value();

		let branch_has_value = if let NodeHeader::Branch(has_value, _) = &header {
			*has_value
		} else {
			// hashed_value_branch
			true
		};

		match header {
			NodeHeader::Null => Ok(NodePlan::Empty),
			NodeHeader::HashedValueBranch(nibble_count) | NodeHeader::Branch(_, nibble_count) => {
				let padding = nibble_count % nibble_ops::NIBBLE_PER_BYTE != 0;
				// check that the padding is valid (if any)
				if padding && nibble_ops::pad_left(data[input.offset]) != 0 {
					return Err(Error::BadFormat)
				}
				let partial = input.take(
					(nibble_count + (nibble_ops::NIBBLE_PER_BYTE - 1)) /
						nibble_ops::NIBBLE_PER_BYTE,
				)?;
				let partial_padding = nibble_ops::number_padding(nibble_count);
				let bitmap_range = input.take(BITMAP_LENGTH)?;
				let bitmap = Bitmap::decode(&data[bitmap_range])?;
				let value = if branch_has_value {
					Some(if contains_hash {
						ValuePlan::Node(input.take(H::LENGTH)?)
					} else {
						let count = <Compact<u32>>::decode(&mut input)?.0 as usize;
						ValuePlan::Inline(input.take(count)?)
					})
				} else {
					None
				};
				let mut children = [
					None, None, None, None, None, None, None, None, None, None, None, None, None,
					None, None, None,
				];
				for i in 0..nibble_ops::NIBBLE_LENGTH {
					if bitmap.value_at(i) {
						let count = <Compact<u32>>::decode(&mut input)?.0 as usize;
						let range = input.take(count)?;
						children[i] = Some(if count == H::LENGTH {
							NodeHandlePlan::Hash(range)
						} else {
							NodeHandlePlan::Inline(range)
						});
					}
				}
				Ok(NodePlan::NibbledBranch {
					partial: NibbleSlicePlan::new(partial, partial_padding),
					value,
					children,
				})
			},
			NodeHeader::HashedValueLeaf(nibble_count) | NodeHeader::Leaf(nibble_count) => {
				let padding = nibble_count % nibble_ops::NIBBLE_PER_BYTE != 0;
				// check that the padding is valid (if any)
				if padding && nibble_ops::pad_left(data[input.offset]) != 0 {
					return Err(Error::BadFormat)
				}
				let partial = input.take(
					(nibble_count + (nibble_ops::NIBBLE_PER_BYTE - 1)) /
						nibble_ops::NIBBLE_PER_BYTE,
				)?;
				let partial_padding = nibble_ops::number_padding(nibble_count);
				let value = if contains_hash {
					ValuePlan::Node(input.take(H::LENGTH)?)
				} else {
					let count = <Compact<u32>>::decode(&mut input)?.0 as usize;
					ValuePlan::Inline(input.take(count)?)
				};

				Ok(NodePlan::Leaf {
					partial: NibbleSlicePlan::new(partial, partial_padding),
					value,
				})
			},
		}
	}

	fn is_empty_node(data: &[u8]) -> bool {
		data == <Self as NodeCodecT>::empty_node()
	}

	fn empty_node() -> &'static [u8] {
		&[trie_constants::EMPTY_TRIE]
	}

	fn leaf_node(partial: impl Iterator<Item = u8>, number_nibble: usize, value: Value) -> Vec<u8> {
		let contains_hash = matches!(&value, Value::Node(..));
		let mut output = if contains_hash {
			partial_from_iterator_encode(partial, number_nibble, NodeKind::HashedValueLeaf)
		} else {
			partial_from_iterator_encode(partial, number_nibble, NodeKind::Leaf)
		};
		match value {
			Value::Inline(value) => {
				Compact(value.len() as u32).encode_to(&mut output);
				output.extend_from_slice(value);
			},
			Value::Node(hash) => {
				debug_assert!(hash.len() == H::LENGTH);
				output.extend_from_slice(hash);
			},
		}
		output
	}

	fn extension_node(
		_partial: impl Iterator<Item = u8>,
		_nbnibble: usize,
		_child: ChildReference<<H as Hasher>::Out>,
	) -> Vec<u8> {
		unreachable!("No extension codec.")
	}

	fn branch_node(
		_children: impl Iterator<Item = impl Borrow<Option<ChildReference<<H as Hasher>::Out>>>>,
		_maybe_value: Option<Value>,
	) -> Vec<u8> {
		unreachable!("No extension codec.")
	}

	fn branch_node_nibbled(
		partial: impl Iterator<Item = u8>,
		number_nibble: usize,
		children: impl Iterator<Item = impl Borrow<Option<ChildReference<<H as Hasher>::Out>>>>,
		value: Option<Value>,
	) -> Vec<u8> {
		let contains_hash = matches!(&value, Some(Value::Node(..)));
		let mut output = match (&value, contains_hash) {
			(&None, _) =>
				partial_from_iterator_encode(partial, number_nibble, NodeKind::BranchNoValue),
			(_, false) =>
				partial_from_iterator_encode(partial, number_nibble, NodeKind::BranchWithValue),
			(_, true) =>
				partial_from_iterator_encode(partial, number_nibble, NodeKind::HashedValueBranch),
		};

		let bitmap_index = output.len();
		let mut bitmap: [u8; BITMAP_LENGTH] = [0; BITMAP_LENGTH];
		(0..BITMAP_LENGTH).for_each(|_| output.push(0));
		match value {
			Some(Value::Inline(value)) => {
				Compact(value.len() as u32).encode_to(&mut output);
				output.extend_from_slice(value);
			},
			Some(Value::Node(hash)) => {
				debug_assert!(hash.len() == H::LENGTH);
				output.extend_from_slice(hash);
			},
			None => (),
		}
		Bitmap::encode(
			children.map(|maybe_child| match maybe_child.borrow() {
				Some(ChildReference::Hash(h)) => {
					h.as_ref().encode_to(&mut output);
					true
				},
				&Some(ChildReference::Inline(inline_data, len)) => {
					inline_data.as_ref()[..len].encode_to(&mut output);
					true
				},
				None => false,
			}),
			bitmap.as_mut(),
		);
		output[bitmap_index..bitmap_index + BITMAP_LENGTH]
			.copy_from_slice(&bitmap[..BITMAP_LENGTH]);
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
	let mut output = Vec::with_capacity(4 + (nibble_count / nibble_ops::NIBBLE_PER_BYTE));
	match node_kind {
		NodeKind::Leaf => NodeHeader::Leaf(nibble_count).encode_to(&mut output),
		NodeKind::BranchWithValue => NodeHeader::Branch(true, nibble_count).encode_to(&mut output),
		NodeKind::BranchNoValue => NodeHeader::Branch(false, nibble_count).encode_to(&mut output),
		NodeKind::HashedValueLeaf =>
			NodeHeader::HashedValueLeaf(nibble_count).encode_to(&mut output),
		NodeKind::HashedValueBranch =>
			NodeHeader::HashedValueBranch(nibble_count).encode_to(&mut output),
	};
	output.extend(partial);
	output
}

const BITMAP_LENGTH: usize = 2;

/// Radix 16 trie, bitmap encoding implementation,
/// it contains children mapping information for a branch
/// (children presence only), it encodes into
/// a compact bitmap encoding representation.
pub(crate) struct Bitmap(u16);

impl Bitmap {
	pub fn decode(data: &[u8]) -> Result<Self, codec::Error> {
		let value = u16::decode(&mut &data[..])?;
		if value == 0 {
			Err("Bitmap without a child.".into())
		} else {
			Ok(Bitmap(value))
		}
	}

	pub fn value_at(&self, i: usize) -> bool {
		self.0 & (1u16 << i) != 0
	}

	pub fn encode<I: Iterator<Item = bool>>(has_children: I, dest: &mut [u8]) {
		let mut bitmap: u16 = 0;
		let mut cursor: u16 = 1;
		for v in has_children {
			if v {
				bitmap |= cursor
			}
			cursor <<= 1;
		}
		dest[0] = (bitmap % 256) as u8;
		dest[1] = (bitmap / 256) as u8;
	}
}
