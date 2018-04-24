// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

bitflags! {
	/// Node roles bitmask.
	pub struct Role: u32 {
		/// No network.
		const NONE = 0b00000000;
		/// Full node, doe not participate in consensus.
		const FULL = 0b00000001;
		/// Light client node.
		const LIGHT = 0b00000010;
		/// Act as a validator.
		const VALIDATOR = 0b00000100;
		/// Act as a collator.
		const COLLATOR = 0b00001000;
	}
}

/// Protocol configuration
#[derive(Clone)]
pub struct ProtocolConfig {
	/// Assigned roles.
	pub roles: Role,
}

impl Default for ProtocolConfig {
	fn default() -> ProtocolConfig {
		ProtocolConfig {
			roles: Role::FULL,
		}
	}
}
