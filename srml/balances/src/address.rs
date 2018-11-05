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

//! Address type that is union of index and id for an account.

#[cfg(feature = "std")]
use std::fmt;
use super::{Member, Decode, Encode, AsPrimitive, Input, Output};

/// A vetted and verified extrinsic from the external world.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug, Hash))]
pub enum Address<AccountId, AccountIndex> where
	AccountId: Member,
	AccountIndex: Member,
{
	/// It's an account ID (pubkey).
	#[cfg_attr(feature = "std", serde(deserialize_with="AccountId::deserialize"))]
	Id(AccountId),
	/// It's an account index.
	#[cfg_attr(feature = "std", serde(deserialize_with="AccountIndex::deserialize"))]
	Index(AccountIndex),
}

#[cfg(feature = "std")]
impl<AccountId, AccountIndex> fmt::Display for Address<AccountId, AccountIndex> where
	AccountId: Member,
	AccountIndex: Member,
{
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "{:?}", self)
	}
}

impl<AccountId, AccountIndex> From<AccountId> for Address<AccountId, AccountIndex> where
	AccountId: Member,
	AccountIndex: Member,
{
	fn from(a: AccountId) -> Self {
		Address::Id(a)
	}
}

fn need_more_than<T: PartialOrd>(a: T, b: T) -> Option<T> {
	if a < b { Some(a) } else { None }
}

impl<AccountId, AccountIndex> Decode for Address<AccountId, AccountIndex> where
	AccountId: Member + Decode,
	AccountIndex: Member + Decode + PartialOrd<AccountIndex> + Ord + AsPrimitive<u32> + AsPrimitive<u16> + AsPrimitive<u8> + Copy,
{
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(match input.read_byte()? {
			x @ 0x00...0xef => Address::Index(x.as_()),
			0xfc => Address::Index(need_more_than(0xef, u16::decode(input)?)?.as_()),
			0xfd => Address::Index(need_more_than(0xffff, u32::decode(input)?)?.as_()),
			0xfe => Address::Index(need_more_than(0xffffffffu32.as_(), Decode::decode(input)?)?),
			0xff => Address::Id(Decode::decode(input)?),
			_ => return None,
		})
	}
}

impl<AccountId, AccountIndex> Encode for Address<AccountId, AccountIndex> where
	AccountId: Member + Encode,
	AccountIndex: Member + Encode + PartialOrd<AccountIndex> + Ord + Copy + AsPrimitive<u32> + AsPrimitive<u16> + AsPrimitive<u8>,
	u32: AsPrimitive<AccountIndex>,
{
	fn encode_to<T: Output>(&self, dest: &mut T) {
		match *self {
			Address::Id(ref i) => {
				dest.push_byte(255);
				dest.push(i);
			}
			Address::Index(i) if i > 0xffffffffu32.as_() => {
				dest.push_byte(254);
				dest.push(&i);
			}
			// small enough to be encoded as 4 bytes
			Address::Index(i) if i > 0xffffu32.as_() => {
				dest.push_byte(253);
				dest.push(&AsPrimitive::<u32>::as_(i));
			}
			// small enough to be encoded as 2 bytes
			Address::Index(i) if i >= 0xf0u32.as_() => {
				dest.push_byte(252);
				dest.push(&AsPrimitive::<u16>::as_(i));
			}
			// small enough to be encoded as 1 byte
			Address::Index(i) => dest.push_byte(i.as_())
		}
	}
}

impl<AccountId, AccountIndex> Default for Address<AccountId, AccountIndex> where
	AccountId: Member + Default,
	AccountIndex: Member,
{
	fn default() -> Self {
		Address::Id(Default::default())
	}
}
