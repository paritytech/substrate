// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use codec::{self, Encode, EncodeLike, Input, Output};

/// Role that the peer sent to us during the handshake, with the addition of what our local node
/// knows about that peer.
///
/// > **Note**: This enum is different from the `Role` enum. The `Role` enum indicates what a
/// >			node says about itself, while `ObservedRole` is a `Role` merged with the
/// >			information known locally about that node.
#[derive(Debug, Clone)]
pub enum ObservedRole {
	/// Full node.
	Full,
	/// Light node.
	Light,
	/// Third-party authority.
	Authority,
}

impl ObservedRole {
	/// Returns `true` for `ObservedRole::Light`.
	pub fn is_light(&self) -> bool {
		matches!(self, Self::Light)
	}
}

/// Role of the local node.
#[derive(Debug, Clone)]
pub enum Role {
	/// Regular full node.
	Full,
	/// Actual authority.
	Authority,
}

impl Role {
	/// True for [`Role::Authority`].
	pub fn is_authority(&self) -> bool {
		matches!(self, Self::Authority)
	}
}

impl std::fmt::Display for Role {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Full => write!(f, "FULL"),
			Self::Authority => write!(f, "AUTHORITY"),
		}
	}
}

bitflags::bitflags! {
	/// Bitmask of the roles that a node fulfills.
	pub struct Roles: u8 {
		/// No network.
		const NONE = 0b00000000;
		/// Full node, does not participate in consensus.
		const FULL = 0b00000001;
		/// Light client node.
		const LIGHT = 0b00000010;
		/// Act as an authority
		const AUTHORITY = 0b00000100;
	}
}

impl Roles {
	/// Does this role represents a client that holds full chain data locally?
	pub fn is_full(&self) -> bool {
		self.intersects(Self::FULL | Self::AUTHORITY)
	}

	/// Does this role represents a client that does not participates in the consensus?
	pub fn is_authority(&self) -> bool {
		*self == Self::AUTHORITY
	}

	/// Does this role represents a client that does not hold full chain data locally?
	pub fn is_light(&self) -> bool {
		!self.is_full()
	}
}

impl<'a> From<&'a Role> for Roles {
	fn from(roles: &'a Role) -> Self {
		match roles {
			Role::Full => Self::FULL,
			Role::Authority => Self::AUTHORITY,
		}
	}
}

impl Encode for Roles {
	fn encode_to<T: Output + ?Sized>(&self, dest: &mut T) {
		dest.push_byte(self.bits())
	}
}

impl EncodeLike for Roles {}

impl codec::Decode for Roles {
	fn decode<I: Input>(input: &mut I) -> Result<Self, codec::Error> {
		Self::from_bits(input.read_byte()?).ok_or_else(|| codec::Error::from("Invalid bytes"))
	}
}
