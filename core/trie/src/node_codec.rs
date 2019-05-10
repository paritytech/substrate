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
use trie_db::{self, NibbleSlice, node::Node, ChildReference, ChildBitmap,
	NibbleOps, Partial, NodeCodec as NodeCodecT, ChildSliceIx};
use crate::error::Error;
use crate::s_cst;
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
pub struct NodeCodec<H, N, BM>(PhantomData<(H,N,BM)>);

impl<
	H: Hasher,
	N: NibbleOps,
	BM: ChildBitmap<Error = Error>
> NodeCodecT<H, N> for NodeCodec<H, N, BM> {
	type Error = Error;
	type BM = BM;

	fn hashed_null_node() -> <H as Hasher>::Out {
		H::hash(<Self as NodeCodecT<_, N>>::empty_node())
	}

	fn decode(data: &[u8]) -> rstd::result::Result<Node<N>, Self::Error> {
		let input = &mut &*data;
		let head = NodeHeader::decode(input).ok_or(Error::BadFormat)?;
		match head {
			NodeHeader::Null => Ok(Node::Empty),
			NodeHeader::Branch(has_value, nibble_count) => {
				let nb_nibble_hpe = nibble_count % N::NIBBLE_PER_BYTE;
				if nb_nibble_hpe > 0 && N::masked_left((N::NIBBLE_PER_BYTE - nb_nibble_hpe) as u8, input[0]) != 0 {
					return Err(Error::BadFormat);
				}
				let nibble_data = take(input, (nibble_count + (N::NIBBLE_PER_BYTE - 1)) / N::NIBBLE_PER_BYTE)
					.ok_or(Error::BadFormat)?;
				let nibble_slice = NibbleSlice::new_offset(nibble_data,
					N::nb_padding(nibble_count));
				let bm_slice = take(input, BM::ENCODED_LEN).ok_or(Error::BadFormat)?;
				let bitmap = BM::decode(&bm_slice[..])?;
				let value = if has_value {
					let count = <Compact<u32>>::decode(input).ok_or(Error::BadFormat)?.0 as usize;
					Some(take(input, count).ok_or(Error::BadFormat)?)
				} else {
					None
				};
				let mut children: N::ChildSliceIx = Default::default();
				let child_val = &**input;
				let mut ix = 0;
				children.as_mut()[0] = ix;
				for i in 0..N::NIBBLE_LEN {
					if bitmap.value_at(i) {
						let count = <Compact<u32>>::decode(input).ok_or(Error::BadFormat)?.0 as usize;
						let _ = take(input, count);
						ix += count + N::ChildSliceIx::CONTENT_HEADER_SIZE;
					}
					children.as_mut()[i + 1] = ix;
				}
				Ok(Node::NibbledBranch(nibble_slice, (children, child_val), value))
			}
			NodeHeader::Leaf(nibble_count) => {
				let nb_nibble_hpe = nibble_count % N::NIBBLE_PER_BYTE;
				if nb_nibble_hpe > 0 && N::masked_left((N::NIBBLE_PER_BYTE - nb_nibble_hpe) as u8, input[0]) != 0 {
					return Err(Error::BadFormat);
				}
				let nibble_data = take(input, (nibble_count + (N::NIBBLE_PER_BYTE - 1)) / N::NIBBLE_PER_BYTE)
					.ok_or(Error::BadFormat)?;
				let nibble_slice = NibbleSlice::new_offset(nibble_data,
					N::nb_padding(nibble_count));
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
		data == <Self as NodeCodecT<_, N>>::empty_node()
	}

	fn empty_node() -> &'static [u8] {
		&[s_cst::EMPTY_TRIE]
	}

	fn leaf_node(partial: Partial, value: &[u8]) -> Vec<u8> {
		let mut output = partial_enc::<N>(partial, NodeKind::Leaf);
		value.encode_to(&mut output);
		output
	}

	fn ext_node(_partial: impl Iterator<Item = u8>, _nbnibble: usize, _child: ChildReference<<H as Hasher>::Out>) -> Vec<u8> {
		unreachable!()
	}

	fn branch_node(
		_children: impl Iterator<Item = impl Borrow<Option<ChildReference<<H as Hasher>::Out>>>>,
		_maybe_value: Option<&[u8]>) -> Vec<u8> {
		unreachable!()
	}

	fn branch_node_nibbled(
		partial: impl Iterator<Item = u8>,
		nb_nibble: usize,
		children: impl Iterator<Item = impl Borrow<Option<ChildReference<<H as Hasher>::Out>>>>,
		maybe_value: Option<&[u8]>) -> Vec<u8> {
		let mut output = if maybe_value.is_some() {
			partial_enc_it::<N,_>(partial, nb_nibble, NodeKind::BranchWithValue)
		} else {
			partial_enc_it::<N,_>(partial, nb_nibble, NodeKind::BranchNoValue)
		};
		let bm_ix = output.len();
		let mut bm: BM::Buff = Default::default();
		(0..BM::ENCODED_LEN).for_each(|_|output.push(0));
		if let Some(value) = maybe_value {
			value.encode_to(&mut output);
		};
		BM::encode(children.map(|maybe_child| match maybe_child.borrow() {
			Some(ChildReference::Hash(h)) => {
				h.as_ref().encode_to(&mut output);
				true
			}
			&Some(ChildReference::Inline(inline_data, len)) => {
				inline_data.as_ref()[..len].encode_to(&mut output);
				true
			}
			None => false,
		}), bm.as_mut());
		output[bm_ix..bm_ix + BM::ENCODED_LEN].copy_from_slice(&bm.as_ref()[..BM::ENCODED_LEN]);
		output
	}

}

// utils

fn partial_enc_it<N: NibbleOps, I: Iterator<Item = u8>>(partial: I, nibble_count: usize, node_kind: NodeKind) -> Vec<u8> {
	let nibble_count = rstd::cmp::min(s_cst::NIBBLE_SIZE_BOUND, nibble_count);

	let mut output = Vec::with_capacity(3 + (nibble_count / N::NIBBLE_PER_BYTE));
	match node_kind {
		NodeKind::Leaf => NodeHeader::Leaf(nibble_count).encode_to(&mut output),
		NodeKind::BranchWithValue => NodeHeader::Branch(true, nibble_count).encode_to(&mut output),
		NodeKind::BranchNoValue => NodeHeader::Branch(false, nibble_count).encode_to(&mut output),
	};
	output.extend(partial);
	output
}

fn partial_enc<N: NibbleOps>(partial: Partial, node_kind: NodeKind) -> Vec<u8> {
	let nb_nibble_hpe = (partial.0).0 as usize;
	let nibble_count = partial.1.len() * N::NIBBLE_PER_BYTE + nb_nibble_hpe;

	let nibble_count = rstd::cmp::min(s_cst::NIBBLE_SIZE_BOUND, nibble_count);

	let mut output = Vec::with_capacity(3 + partial.1.len());
	match node_kind {
		NodeKind::Leaf => NodeHeader::Leaf(nibble_count).encode_to(&mut output),
		NodeKind::BranchWithValue => NodeHeader::Branch(true, nibble_count).encode_to(&mut output),
		NodeKind::BranchNoValue => NodeHeader::Branch(false, nibble_count).encode_to(&mut output),
	};
	if nb_nibble_hpe > 0 {
		output.push(N::masked_right((N::NIBBLE_PER_BYTE - nb_nibble_hpe) as u8, (partial.0).1));
	}
	output.extend_from_slice(&partial.1[..]);
	output
}

/// bitmap codec for radix 16
pub struct BitMap16(u16);

impl ChildBitmap for BitMap16 {
	const ENCODED_LEN: usize = 2;
	type Error = Error;
	type Buff = [u8;3]; // need a byte for header

	fn decode(data: &[u8]) -> Result<Self, Self::Error> {
		u16::decode(&mut &data[..])
			.ok_or(Error::BadFormat)
			.map(|v|BitMap16(v))
	}

	fn value_at(&self, i: usize) -> bool {
		self.0 & (1u16 << i) != 0
	}

	fn encode<I: Iterator<Item = bool>>(has_children: I , dest: &mut [u8]) {
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
