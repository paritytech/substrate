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

//! Address type that is union of index and id for an account.

#[cfg(feature = "std")]
use std::fmt;
use crate::{Member, Decode, Encode, As, Input, Output};

/// An indices-aware address, which can be either a direct `AccountId` or
/// an index.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug, Hash))]
pub enum Address<AccountId, AccountIndex> where
	AccountId: Member,
	AccountIndex: Member,
{
	/// It's an account ID (pubkey).
	Id(AccountId),
	/// It's an account index.
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
	if a < b { Some(b) } else { None }
}

impl<AccountId, AccountIndex> Decode for Address<AccountId, AccountIndex> where
	AccountId: Member + Decode,
	AccountIndex: Member + Decode + PartialOrd<AccountIndex> + Ord + As<u32> + As<u16> + As<u8> + Copy,
{
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		Some(match input.read_byte()? {
			x @ 0x00...0xef => Address::Index(As::sa(x)),
			0xfc => Address::Index(As::sa(need_more_than(0xef, u16::decode(input)?)?)),
			0xfd => Address::Index(As::sa(need_more_than(0xffff, u32::decode(input)?)?)),
			0xfe => Address::Index(need_more_than(As::sa(0xffffffffu32), Decode::decode(input)?)?),
			0xff => Address::Id(Decode::decode(input)?),
			_ => return None,
		})
	}
}

impl<AccountId, AccountIndex> Encode for Address<AccountId, AccountIndex> where
	AccountId: Member + Encode,
	AccountIndex: Member + Encode + PartialOrd<AccountIndex> + Ord + As<u32> + As<u16> + As<u8> + Copy,
{
	fn encode_to<T: Output>(&self, dest: &mut T) {
		match *self {
			Address::Id(ref i) => {
				dest.push_byte(255);
				dest.push(i);
			}
			Address::Index(i) if i > As::sa(0xffffffffu32) => {
				dest.push_byte(254);
				dest.push(&i);
			}
			Address::Index(i) if i > As::sa(0xffffu32) => {
				dest.push_byte(253);
				dest.push(&As::<u32>::as_(i));
			}
			Address::Index(i) if i >= As::sa(0xf0u32) => {
				dest.push_byte(252);
				dest.push(&As::<u16>::as_(i));
			}
			Address::Index(i) => dest.push_byte(As::<u8>::as_(i)),
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

#[cfg(test)]
mod tests {
	use crate::{Encode, Decode};

	type Address = super::Address<[u8; 8], u32>;
	fn index(i: u32) -> Address { super::Address::Index(i) }
	fn id(i: [u8; 8]) -> Address { super::Address::Id(i) }

	fn compare(a: Option<Address>, d: &[u8]) {
		if let Some(ref a) = a {
			assert_eq!(d, &a.encode()[..]);
		}
		assert_eq!(Address::decode(&mut &d[..]), a);
	}

	#[test]
	fn it_should_work() {
		compare(Some(index(2)), &[2][..]);
		compare(None, &[240][..]);
		compare(None, &[252, 239, 0][..]);
		compare(Some(index(240)), &[252, 240, 0][..]);
		compare(Some(index(304)), &[252, 48, 1][..]);
		compare(None, &[253, 255, 255, 0, 0][..]);
		compare(Some(index(0x10000)), &[253, 0, 0, 1, 0][..]);
		compare(Some(id([42, 69, 42, 69, 42, 69, 42, 69])), &[255, 42, 69, 42, 69, 42, 69, 42, 69][..]);
	}
}
