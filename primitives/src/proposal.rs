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
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Proposals for relay-chain governance.
//!
//! This describes a combination of a function ID and data that can be used to call into
//! an internal function.

use bytes;

/// Internal functions that can be dispatched to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[repr(u8)]
pub enum InternalFunction {
	/// Set the system's code.
	SystemSetCode = 0,
	/// Set the number of sessions per era.
	StakingSetSessionsPerEra = 1,
	/// Set the minimum bonding duration for staking.
	StakingSetBondingDuration = 2,
	/// Set the validator count for staking.
	StakingSetValidatorCount = 3,
	/// Set the per-mille of validator approval required for governance changes.
	GovernanceSetApprovalPpmRequired = 4,
	/// Set the session length.
	SessionSetLength = 5,
}

impl InternalFunction {
	/// Derive `Some` value from a `u8`, or `None` if it's invalid.
	pub fn from_u8(value: u8) -> Option<InternalFunction> {
		use self::*;
		let functions = [
			InternalFunction::SystemSetCode,
			InternalFunction::StakingSetSessionsPerEra,
			InternalFunction::StakingSetBondingDuration,
			InternalFunction::StakingSetValidatorCount,
			InternalFunction::GovernanceSetApprovalPpmRequired,
			InternalFunction::SessionSetLength
		];
		if (value as usize) < functions.len() {
			Some(functions[value as usize])
		} else {
			None
		}
	}
}

/// An internal function.
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Proposal {
	/// The privileged function to call.
	pub function: InternalFunction,
	/// The serialised data to call it with.
	#[serde(with = "bytes")]
	pub input_data: Vec<u8>,
}

#[cfg(test)]
mod test {
	use super::*;
	use support::StaticHexInto;

	#[test]
	fn slicing_should_work() {
		let p = Proposal {
			function: InternalFunction::SystemSetCode,
			input_data: b"Hello world".to_vec(),
		};
		let v = p.to_vec();
		assert_eq!(v, "000b00000048656c6c6f20776f726c64".convert::<Vec<u8>>());

		let o = Proposal::from_slice(&v).unwrap();
		assert_eq!(p, o);
	}
}
