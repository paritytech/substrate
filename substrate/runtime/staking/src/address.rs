// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Address type that is union of index and id for an account.

#[cfg(feature = "std")]
use std::fmt;
use super::{Member, Decode, Encode, As, Input, Output};
use primitives::address_format::{SS58, SS58Compatible};
use ed25519::Public;

/// A vetted and verified extrinsic from the external world.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug, Hash))]
pub enum Address<AccountId, AccountIndex> where
	AccountId: Member + fmt::Display + Into<SS58Compatible>,
	AccountIndex: Member + fmt::Display + Into<SS58Compatible>,
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
	AccountId: Member + Sized + fmt::Display + Into<SS58Compatible> + Default + fmt::Debug + Sync,
	AccountIndex: Member + Sized + fmt::Display + Into<SS58Compatible> + fmt::Debug + Sync,
	Public: From<AccountIndex>
{
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
		write!(f, "{:?}", &self.clone().encode())
	}
}

impl<AccountId, AccountIndex> From<AccountId> for Address<AccountId, AccountIndex> where
	AccountId: Member + fmt::Display + Into<SS58Compatible>,
	AccountIndex: Member + fmt::Display + Into<SS58Compatible>,
{
	fn from(a: AccountId) -> Self {
		Address::Id(a)
	}
}

fn need_more_than<T: PartialOrd>(a: T, b: T) -> Option<T> {
	if a < b { Some(a) } else { None }
}

impl<AccountId, AccountIndex> Decode for Address<AccountId, AccountIndex> where
	AccountId: Member + fmt::Display + Decode,
	AccountIndex: Member + fmt::Display + Decode + PartialOrd<AccountIndex> + Ord + As<u32> + As<u16> + As<u8> + Copy,
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
	AccountId: Member + fmt::Display + Encode,
	AccountIndex: Member + fmt::Display + Encode + PartialOrd<AccountIndex> + Ord + As<u32> + As<u16> + As<u8> + Copy,
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
	AccountId: Member + fmt::Display + Into<SS58Compatible> + Default,
	AccountIndex: Member + fmt::Display + Into<SS58Compatible>,
{
	fn default() -> Self {
		Address::Id(Default::default())
	}
}

impl<AccountId, AccountIndex> Into<Public> for Address<AccountId, AccountIndex> where
    AccountId: Member + fmt::Display + Into<SS58Compatible> + Default + fmt::Debug + Sync,
    AccountIndex: Member + fmt::Display + Into<SS58Compatible> +  fmt::Debug + Sync,


{
	fn into(self) -> Public {
		match self {
			Address::Id(id)  => Into::<Public>::into(id),
			Address::Index(id) => Into::<Public>::into(id)
		}
	}
}

impl<AccountId, AccountIndex> SS58 for Address<AccountId, AccountIndex> where
	AccountId: Member + fmt::Display + Into<SS58Compatible> + Default + fmt::Debug + Sync,
	AccountIndex: Member + fmt::Display + Into<SS58Compatible> +  fmt::Debug + Sync,
	Vec<u8>: From<AccountIndex>
{}

impl<AccountId, AccountIndex> Into<SS58Compatible> for Address<AccountId, AccountIndex> where
		AccountId: Member + fmt::Display + Into<SS58Compatible> + Default + fmt::Debug + Sync,
		AccountIndex: Member + fmt::Display + Into<SS58Compatible> + fmt::Debug + Sync,
		Vec<u8>: From<AccountIndex>
{
	fn into(self) -> SS58Compatible {
		SS58Compatible(self.into())
	}
}