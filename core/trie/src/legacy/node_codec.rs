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
use codec::{Encode, Decode, Compact};
use hash_db::Hasher;
use trie_db::{self, NibbleSlice, NibbleOps, node::Node, ChildReference, Partial, ChildBitmap, ChildSliceIx};
use trie_db::NodeCodec as TraitNodeCodec;
use crate::error::Error;
use crate::legacy::util::{EMPTY_TRIE, LEAF_NODE_OFFSET, EXTENSION_NODE_OVER,
	take, partial_to_key, partial_to_key_it, LEAF_NODE_OVER,
	EXTENSION_NODE_OFFSET, branch_node_buf};
use rstd::borrow::Borrow;
use super::node_header::NodeHeader;
#[cfg(not(feature = "std"))]
use rstd::prelude::{vec, Vec};

/// Concrete implementation of a `NodeCodec` with Parity Codec encoding, generic over the `Hasher`
#[derive(Default, Clone)]
pub struct NodeCodec<H, N, BM>(PhantomData<(H, N, BM)>);

impl<H: Hasher, N: NibbleOps, BM: ChildBitmap<Error = Error>> TraitNodeCodec<H, N> for NodeCodec<H, N, BM> {
	type Error = Error;

	fn hashed_null_node() -> <H as Hasher>::Out {
		H::hash(<Self as TraitNodeCodec<_, N>>::empty_node())
	}

	fn decode(data: &[u8]) -> ::rstd::result::Result<Node<N>, Self::Error> {
		use Error::BadFormat;
		let input = &mut &*data;
		match NodeHeader::decode(input).ok_or(BadFormat)? {
			NodeHeader::Null => Ok(Node::Empty),
			NodeHeader::Branch(has_value) => {
				let bm_slice = take(input, BM::ENCODED_LEN).ok_or(BadFormat)?;
				let bitmap = BM::decode(&bm_slice[..])?;

				let value = if has_value {
					let count = <Compact<u32>>::decode(input).ok_or(BadFormat)?.0 as usize;
					Some(take(input, count).ok_or(BadFormat)?)
				} else {
					None
				};
				let mut children: N::ChildSliceIx = Default::default();
				let child_val = &**input;
				let mut ix = 0;
				children.as_mut()[0] = ix;
				for i in 0..N::NIBBLE_LEN {
					if bitmap.value_at(i) {
						let count = <Compact<u32>>::decode(input).ok_or(BadFormat)?.0 as usize;
						let _ = take(input, count);
						ix += count + N::ChildSliceIx::CONTENT_HEADER_SIZE;
					}
					children.as_mut()[i + 1] = ix;
				}
				Ok(Node::Branch((children, child_val), value))
			}
			NodeHeader::Extension(nibble_count) => {
				let nb_nibble_hpe = nibble_count % N::NIBBLE_PER_BYTE;
				if nb_nibble_hpe > 0 && N::masked_left((N::NIBBLE_PER_BYTE - nb_nibble_hpe) as u8, input[0]) != 0 {
					return Err(Error::BadFormat);
				}

				let nibble_data = take(input, (nibble_count + (N::NIBBLE_PER_BYTE - 1)) / N::NIBBLE_PER_BYTE)
					.ok_or(BadFormat)?;
				let nibble_slice = NibbleSlice::new_offset(nibble_data,
					N::nb_padding(nibble_count));
				let count = <Compact<u32>>::decode(input).ok_or(BadFormat)?.0 as usize;
				Ok(Node::Extension(nibble_slice, take(input, count).ok_or(BadFormat)?))
			}
			NodeHeader::Leaf(nibble_count) => {
				let nb_nibble_hpe = nibble_count % N::NIBBLE_PER_BYTE;
				if nb_nibble_hpe > 0 && N::masked_left((N::NIBBLE_PER_BYTE - nb_nibble_hpe) as u8, input[0]) != 0 {
					return Err(Error::BadFormat);
				}


				let nibble_data = take(input, (nibble_count + (N::NIBBLE_PER_BYTE - 1)) / N::NIBBLE_PER_BYTE)
					.ok_or(BadFormat)?;
				let nibble_slice = NibbleSlice::new_offset(nibble_data,
					N::nb_padding(nibble_count));
				let count = <Compact<u32>>::decode(input).ok_or(BadFormat)?.0 as usize;
				Ok(Node::Leaf(nibble_slice, take(input, count).ok_or(BadFormat)?))
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
		data == <Self as TraitNodeCodec<_, N>>::empty_node()
	}

	fn empty_node() -> &'static[u8] {
		&[EMPTY_TRIE]
	}

	fn leaf_node(partial: Partial, value: &[u8]) -> Vec<u8> {
		let mut output = partial_to_key::<N>(partial, LEAF_NODE_OFFSET, LEAF_NODE_OVER);
		value.encode_to(&mut output);
		output
	}

	fn ext_node(partial: impl Iterator<Item = u8>, nb_nibble: usize, child: ChildReference<<H as Hasher>::Out>) -> Vec<u8> {
		let mut output = partial_to_key_it::<N,_>(partial, nb_nibble, EXTENSION_NODE_OFFSET, EXTENSION_NODE_OVER);
		match child {
			ChildReference::Hash(h) => h.as_ref().encode_to(&mut output),
			ChildReference::Inline(inline_data, len) => (&AsRef::<[u8]>::as_ref(&inline_data)[..len]).encode_to(&mut output),
		};
		output
	}

	fn branch_node(
		children: impl Iterator<Item = impl Borrow<Option<ChildReference<<H as Hasher>::Out>>>>,
		maybe_value: Option<&[u8]>) -> Vec<u8> {
		let mut output = vec![0;BM::ENCODED_LEN + 1];
		let mut prefix: BM::Buff = Default::default();
		let have_value = if let Some(value) = maybe_value {
			value.encode_to(&mut output);
			true
		} else {
			false
		};
		branch_node_buf::<BM, _>(have_value, children.map(|maybe_child| match maybe_child.borrow() {
			Some(ChildReference::Hash(h)) => {
				h.as_ref().encode_to(&mut output);
				true
			}
			&Some(ChildReference::Inline(inline_data, len)) => {
				inline_data.as_ref()[..len].encode_to(&mut output);
				true
			}
			None => false,
		}), prefix.as_mut());
		output[0..BM::ENCODED_LEN + 1].copy_from_slice(prefix.as_ref());
		output
	}

	fn branch_node_nibbled(
		_partial:	impl Iterator<Item = u8>,
		_nb_nibble: usize,
		_children: impl Iterator<Item = impl Borrow<Option<ChildReference<<H as Hasher>::Out>>>>,
		_maybe_value: Option<&[u8]>) -> Vec<u8> {
		unreachable!()
	}

}
