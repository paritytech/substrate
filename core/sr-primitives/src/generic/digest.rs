// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Generic implementation of a digest.

use rstd::prelude::*;

use codec::{Decode, Encode, Codec, Input};
use traits::{self, Member, DigestItem as DigestItemT, MaybeSerializeDebug};

use substrate_primitives::hash::H512 as Signature;

#[derive(PartialEq, Eq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
pub struct Digest<Item> {
	pub logs: Vec<Item>,
}

impl<Item> Default for Digest<Item> {
	fn default() -> Self {
		Digest { logs: Vec::new(), }
	}
}

impl<Item> traits::Digest for Digest<Item> where
	Item: DigestItemT + Codec
{
	type Hash = Item::Hash;
	type Item = Item;

	fn logs(&self) -> &[Self::Item] {
		&self.logs
	}

	fn push(&mut self, item: Self::Item) {
		self.logs.push(item);
	}

	fn pop(&mut self) -> Option<Self::Item> {
		self.logs.pop()
	}
}

/// Digest item that is able to encode/decode 'system' digest items and
/// provide opaque access to other items.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
pub enum DigestItem<Hash, AuthorityId> {
	/// System digest item announcing that authorities set has been changed
	/// in the block. Contains the new set of authorities.
	AuthoritiesChange(Vec<AuthorityId>),
	/// System digest item that contains the root of changes trie at given
	/// block. It is created for every block iff runtime supports changes
	/// trie creation.
	ChangesTrieRoot(Hash),
	/// Put a Seal on it
	Seal(u64, Signature),
	/// Any 'non-system' digest item, opaque to the native code.
	Other(Vec<u8>),
}


/// A 'referencing view' for digest item. Does not own its contents. Used by
/// final runtime implementations for encoding/decoding its log items.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum DigestItemRef<'a, Hash: 'a, AuthorityId: 'a> {
	/// Reference to `DigestItem::AuthoritiesChange`.
	AuthoritiesChange(&'a [AuthorityId]),
	/// Reference to `DigestItem::ChangesTrieRoot`.
	ChangesTrieRoot(&'a Hash),
	/// A sealed signature for testing
	Seal(&'a u64, &'a Signature),
	/// Any 'non-system' digest item, opaque to the native code.
	/// Reference to `DigestItem::Other`.
	Other(&'a Vec<u8>),
}

/// Type of the digest item. Used to gain explicit control over `DigestItem` encoding
/// process. We need an explicit control, because final runtimes are encoding their own
/// digest items using `DigestItemRef` type and we can't auto-derive `Decode`
/// trait for `DigestItemRef`.
#[repr(u32)]
#[derive(Encode, Decode)]
enum DigestItemType {
	Other = 0,
	AuthoritiesChange,
	ChangesTrieRoot,
	Seal,
}

impl<Hash, AuthorityId> DigestItem<Hash, AuthorityId> {
	/// Returns Some if `self` is a `DigestItem::Other`.
	pub fn as_other(&self) -> Option<&Vec<u8>> {
		match *self {
			DigestItem::Other(ref v) => Some(v),
			_ => None,
		}
	}

	/// Returns a 'referencing view' for this digest item.
	fn dref<'a>(&'a self) -> DigestItemRef<'a, Hash, AuthorityId> {
		match *self {
			DigestItem::AuthoritiesChange(ref v) => DigestItemRef::AuthoritiesChange(v),
			DigestItem::ChangesTrieRoot(ref v) => DigestItemRef::ChangesTrieRoot(v),
			DigestItem::Seal(ref v, ref s) => DigestItemRef::Seal(v, s),
			DigestItem::Other(ref v) => DigestItemRef::Other(v),
		}
	}
}

impl<
	Hash: Codec + Member + MaybeSerializeDebug,
	AuthorityId: Codec + Member + MaybeSerializeDebug
> traits::DigestItem for DigestItem<Hash, AuthorityId> {
	type Hash = Hash;
	type AuthorityId = AuthorityId;

	fn as_authorities_change(&self) -> Option<&[Self::AuthorityId]> {
		self.dref().as_authorities_change()
	}

	fn as_changes_trie_root(&self) -> Option<&Hash> {
		self.dref().as_changes_trie_root()
	}
}

impl<Hash: Encode, AuthorityId: Encode> Encode for DigestItem<Hash, AuthorityId> {
	fn encode(&self) -> Vec<u8> {
		self.dref().encode()
	}
}

impl<Hash: Decode, AuthorityId: Decode> Decode for DigestItem<Hash, AuthorityId> {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		let item_type: DigestItemType = Decode::decode(input)?;
		match item_type {
			DigestItemType::AuthoritiesChange => Some(DigestItem::AuthoritiesChange(
				Decode::decode(input)?,
			)),
			DigestItemType::ChangesTrieRoot => Some(DigestItem::ChangesTrieRoot(
				Decode::decode(input)?,
			)),
			DigestItemType::Seal => {
				let vals: (u64, Signature) = Decode::decode(input)?;
				Some(DigestItem::Seal(vals.0, vals.1))
			},
			DigestItemType::Other => Some(DigestItem::Other(
				Decode::decode(input)?,
			)),
		}
	}
}

impl<'a, Hash: Codec + Member, AuthorityId: Codec + Member> DigestItemRef<'a, Hash, AuthorityId> {
	pub fn as_authorities_change(&self) -> Option<&'a [AuthorityId]> {
		match *self {
			DigestItemRef::AuthoritiesChange(ref authorities) => Some(authorities),
			_ => None,
		}
	}

	pub fn as_changes_trie_root(&self) -> Option<&'a Hash> {
		match *self {
			DigestItemRef::ChangesTrieRoot(ref changes_trie_root) => Some(changes_trie_root),
			_ => None,
		}
	}
}

impl<'a, Hash: Encode, AuthorityId: Encode> Encode for DigestItemRef<'a, Hash, AuthorityId> {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		match *self {
			DigestItemRef::AuthoritiesChange(authorities) => {
				DigestItemType::AuthoritiesChange.encode_to(&mut v);
				authorities.encode_to(&mut v);
			},
			DigestItemRef::ChangesTrieRoot(changes_trie_root) => {
				DigestItemType::ChangesTrieRoot.encode_to(&mut v);
				changes_trie_root.encode_to(&mut v);
			},
			DigestItemRef::Seal(val, sig) => {
				DigestItemType::Seal.encode_to(&mut v);
				(val, sig).encode_to(&mut v);
			},
			DigestItemRef::Other(val) => {
				DigestItemType::Other.encode_to(&mut v);
				val.encode_to(&mut v);
			},
		}

		v
	}
}
