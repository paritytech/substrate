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

use rstd::prelude::*;
use super::{Member, Slicable, As, Input};

/// A vetted and verified extrinsic from the external world.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize, Debug))]
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

impl<AccountId, AccountIndex> From<AccountId> for Address<AccountId, AccountIndex> where
 	AccountId: Member,
 	AccountIndex: Member,
{
	fn from(a: AccountId) -> Self {
		Address::Id(a)
	}
}

impl<AccountId, AccountIndex> Slicable for Address<AccountId, AccountIndex> where
	AccountId: Member + Slicable,
	AccountIndex: Member + Slicable + PartialOrd<AccountIndex> + Ord + As<u32> + As<u16> + As<u8> + Copy,
{
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		match input.read_byte()? {
			255 => Some(Address::Id(Slicable::decode(input)?)),
			254 => Some(Address::Index(Slicable::decode(input)?)),
			253 => Some(Address::Index(As::sa(u32::decode(input)?))),
			252 => Some(Address::Index(As::sa(u16::decode(input)?))),
			x => Some(Address::Index(As::sa(x))),
		}
	}

	fn encode(&self) -> Vec<u8> {
		let mut v = Vec::new();

		match *self {
			Address::Id(ref i) => {
				v.push(255);
				i.using_encoded(|s| v.extend(s));
			}
			Address::Index(i) if i > As::sa(0xffffffffu32) => {
				v.push(254);
				i.using_encoded(|s| v.extend(s));
			}
			Address::Index(i) if i > As::sa(0xffffu32) => {
				v.push(253);
				As::<u32>::as_(i).using_encoded(|s| v.extend(s));
			}
			Address::Index(i) if i >= As::sa(252u32) => {
				v.push(252);
				As::<u16>::as_(i).using_encoded(|s| v.extend(s));
			}
			Address::Index(i) => v.push(As::<u8>::as_(i)),
		}

		v
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
