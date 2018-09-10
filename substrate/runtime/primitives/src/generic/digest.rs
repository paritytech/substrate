// Copyright 2017 Parity Technologies (UK) Ltd.
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
use traits::{self, Member, DigestItem as DigestItemT};

#[derive(PartialEq, Eq, Clone, Encode, Decode)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
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
	type Item = Item;

	fn logs(&self) -> &[Self::Item] {
		&self.logs
	}

	fn push(&mut self, item: Self::Item) {
		self.logs.push(item);
	}
}

/// Digest item that is able to encode/decode 'system' digest items and
/// provide opaque access to other items.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
pub enum DigestItem<AuthorityId> {
	/// System digest item announcing that authorities set has been changed
	/// in the block. Contains the new set of authorities.
	AuthoritiesChange(Vec<AuthorityId>),
	/// Any 'non-system' digest item, opaque to the native code.
	Other(Vec<u8>),
}

/// A 'referencing view' for digest item. Does not own its contents. Used by
/// final runtime implementations for encoding/decoding its log items.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum DigestItemRef<'a, AuthorityId: 'a> {
	/// Reference to `DigestItem::AuthoritiesChange`.
	AuthoritiesChange(&'a [AuthorityId]),
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
}

impl<AuthorityId> DigestItem<AuthorityId> {
	/// Returns Some if `self` is a `DigestItem::Other`.
	pub fn as_other(&self) -> Option<&Vec<u8>> {
		match *self {
			DigestItem::Other(ref v) => Some(v),
			_ => None,
		}
	}

	/// Returns a 'referencing view' for this digest item.
	fn dref<'a>(&'a self) -> DigestItemRef<'a, AuthorityId> {
		match *self {
			DigestItem::AuthoritiesChange(ref v) => DigestItemRef::AuthoritiesChange(v),
			DigestItem::Other(ref v) => DigestItemRef::Other(v),
		}
	}
}

impl<AuthorityId: Member> traits::DigestItem for DigestItem<AuthorityId> {
	type AuthorityId = AuthorityId;

	fn as_authorities_change(&self) -> Option<&[Self::AuthorityId]> {
		match *self {
			DigestItem::AuthoritiesChange(ref authorities) => Some(authorities),
			_ => None,
		}
	}
}

impl<AuthorityId: Encode> Encode for DigestItem<AuthorityId> {
	fn encode(&self) -> Vec<u8> {
		self.dref().encode()
	}
}

impl<AuthorityId: Decode> Decode for DigestItem<AuthorityId> {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		let item_type: DigestItemType = Decode::decode(input)?;
		match item_type {
			DigestItemType::AuthoritiesChange => Some(DigestItem::AuthoritiesChange(
				Decode::decode(input)?,
			)),
			DigestItemType::Other => Some(DigestItem::Other(
				Decode::decode(input)?,
			)),
		}
	}
}

impl<'a, AuthorityId: Encode> Encode for DigestItemRef<'a, AuthorityId> {
	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		match *self {
			DigestItemRef::AuthoritiesChange(authorities) => {
				DigestItemType::AuthoritiesChange.encode_to(&mut v);
				authorities.encode_to(&mut v);
			},
			DigestItemRef::Other(val) => {
				DigestItemType::Other.encode_to(&mut v);
				val.encode_to(&mut v);
			},
		}

		v
	}
}
