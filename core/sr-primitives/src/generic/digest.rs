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

//! Generic implementation of a digest.

#[cfg(feature = "std")]
use serde::Serialize;

use rstd::prelude::*;

use crate::ConsensusEngineId;
use crate::codec::{Decode, Encode, Codec, Input};
use crate::traits::{self, Member, DigestItem as DigestItemT, MaybeHash};

/// Generic header digest.
#[derive(PartialEq, Eq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize))]
pub struct Digest<Item> {
	/// A list of logs in the digest.
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
#[cfg_attr(feature = "std", derive(Debug))]
#[allow(deprecated)]
pub enum DigestItem<Hash, AuthorityId, SealSignature> {
	/// System digest item announcing that authorities set has been changed
	/// in the block. Contains the new set of authorities.
	AuthoritiesChange(Vec<AuthorityId>),
	/// System digest item that contains the root of changes trie at given
	/// block. It is created for every block iff runtime supports changes
	/// trie creation.
	ChangesTrieRoot(Hash),
	/// The old way to put a Seal on it.  Deprecated.
	#[deprecated(
		since = "1.0",
		note = "New versions of Substrate will never generate this, and it will be rejected on new blockchains.",
	)]
	Seal(u64, SealSignature),
	/// Put a Seal on it
	Consensus(ConsensusEngineId, Vec<u8>),
	/// Any 'non-system' digest item, opaque to the native code.
	Other(Vec<u8>),
}

#[cfg(feature = "std")]
impl<Hash: Encode, AuthorityId: Encode, SealSignature: Encode> ::serde::Serialize for DigestItem<Hash, AuthorityId, SealSignature> {
	fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
		self.using_encoded(|bytes| {
			::substrate_primitives::bytes::serialize(bytes, seq)
		})
	}
}


/// A 'referencing view' for digest item. Does not own its contents. Used by
/// final runtime implementations for encoding/decoding its log items.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
#[allow(deprecated)]
pub enum DigestItemRef<'a, Hash: 'a, AuthorityId: 'a, SealSignature: 'a> {
	/// Reference to `DigestItem::AuthoritiesChange`.
	AuthoritiesChange(&'a [AuthorityId]),
	/// Reference to `DigestItem::ChangesTrieRoot`.
	ChangesTrieRoot(&'a Hash),
	/// A deprecated sealed signature for testing
	#[deprecated]
	Seal(&'a u64, &'a SealSignature),
	/// A sealed signature for testing
	Consensus(&'a ConsensusEngineId, &'a [u8]),
	/// Any 'non-system' digest item, opaque to the native code.
	/// Reference to `DigestItem::Other`.
	Other(&'a [u8]),
}

/// Type of the digest item. Used to gain explicit control over `DigestItem` encoding
/// process. We need an explicit control, because final runtimes are encoding their own
/// digest items using `DigestItemRef` type and we can't auto-derive `Decode`
/// trait for `DigestItemRef`.
#[repr(u32)]
#[derive(Encode, Decode)]
enum DigestItemType {
	Other = 0,
	AuthoritiesChange = 1,
	ChangesTrieRoot = 2,
	Seal = 3,
	Consensus = 4,
}

impl<Hash, AuthorityId, SealSignature> DigestItem<Hash, AuthorityId, SealSignature> {
	/// Returns Some if `self` is a `DigestItem::Other`.
	pub fn as_other(&self) -> Option<&Vec<u8>> {
		match *self {
			DigestItem::Other(ref v) => Some(v),
			_ => None,
		}
	}

	/// Returns a 'referencing view' for this digest item.
	#[allow(deprecated)]
	fn dref<'a>(&'a self) -> DigestItemRef<'a, Hash, AuthorityId, SealSignature> {
		match *self {
			DigestItem::AuthoritiesChange(ref v) => DigestItemRef::AuthoritiesChange(v),
			DigestItem::ChangesTrieRoot(ref v) => DigestItemRef::ChangesTrieRoot(v),
			DigestItem::Seal(ref v, ref s) => DigestItemRef::Seal(v, s),
			DigestItem::Consensus(ref v, ref s) => DigestItemRef::Consensus(v, s),
			DigestItem::Other(ref v) => DigestItemRef::Other(v),
		}
	}
}

impl<
	Hash: Codec + Member,
	AuthorityId: Codec + Member + MaybeHash,
	SealSignature: Codec + Member,
> traits::DigestItem for DigestItem<Hash, AuthorityId, SealSignature> {
	type Hash = Hash;
	type AuthorityId = AuthorityId;

	fn as_authorities_change(&self) -> Option<&[Self::AuthorityId]> {
		self.dref().as_authorities_change()
	}

	fn as_changes_trie_root(&self) -> Option<&Self::Hash> {
		self.dref().as_changes_trie_root()
	}
}

impl<Hash: Encode, AuthorityId: Encode, SealSignature: Encode> Encode for DigestItem<Hash, AuthorityId, SealSignature> {
	fn encode(&self) -> Vec<u8> {
		self.dref().encode()
	}
}

impl<Hash: Decode, AuthorityId: Decode, SealSignature: Decode> Decode for DigestItem<Hash, AuthorityId, SealSignature> {
	#[allow(deprecated)]
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
				let vals: (u64, SealSignature) = Decode::decode(input)?;
				Some(DigestItem::Seal(vals.0, vals.1))
			},
			DigestItemType::Consensus => {
				let vals: (ConsensusEngineId, Vec<u8>) = Decode::decode(input)?;
				Some(DigestItem::Consensus(vals.0, vals.1))
			}
			DigestItemType::Other => Some(DigestItem::Other(
				Decode::decode(input)?,
			)),
		}
	}
}

impl<'a, Hash: Codec + Member, AuthorityId: Codec + Member, SealSignature: Codec + Member> DigestItemRef<'a, Hash, AuthorityId, SealSignature> {
	/// Cast this digest item into `AuthoritiesChange`.
	pub fn as_authorities_change(&self) -> Option<&'a [AuthorityId]> {
		match *self {
			DigestItemRef::AuthoritiesChange(ref authorities) => Some(authorities),
			_ => None,
		}
	}

	/// Cast this digest item into `ChangesTrieRoot`.
	pub fn as_changes_trie_root(&self) -> Option<&'a Hash> {
		match *self {
			DigestItemRef::ChangesTrieRoot(ref changes_trie_root) => Some(changes_trie_root),
			_ => None,
		}
	}
}

#[allow(deprecated)]
impl<'a, Hash: Encode, AuthorityId: Encode, SealSignature: Encode> Encode for DigestItemRef<'a, Hash, AuthorityId, SealSignature> {
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
			DigestItemRef::Consensus(val, sig) => {
				DigestItemType::Consensus.encode_to(&mut v);
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

#[cfg(test)]
mod tests {
	use super::*;
	use substrate_primitives::hash::H512 as Signature;

	#[test]
	#[allow(deprecated)]
	fn should_serialize_digest() {
		let digest = Digest {
			logs: vec![
				DigestItem::AuthoritiesChange(vec![1]),
				DigestItem::ChangesTrieRoot(4),
				DigestItem::Seal(1, Signature::from_low_u64_be(15)),
				DigestItem::Other(vec![1, 2, 3]),
			],
		};

		assert_eq!(
			::serde_json::to_string(&digest).unwrap(),
			r#"{"logs":["0x010401000000","0x0204000000","0x0301000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f","0x000c010203"]}"#
		);
	}
}
