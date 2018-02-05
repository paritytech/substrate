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

//! Proposal: This describes a combination of a function ID and data that can be used to call into
//! an internal function.

use runtime_std::prelude::*;
use runtime_std::mem;
use codec::{Slicable, Joiner, StreamReader};
use runtime::{system, governance, staking, session};

/// Internal functions that can be dispatched to.
#[derive(Clone, Copy)]
#[cfg_attr(feature = "with-std", derive(PartialEq, Debug))]
#[repr(u8)]
pub enum InternalFunction {
	SystemSetCode = 0x00,

	SessionSetLength = 0x10,
	SessionForceNewSession = 0x11,

	StakingSetSessionsPerEra = 0x20,
	StakingSetBondingDuration = 0x21,
	StakingSetValidatorCount = 0x22,
	StakingForceNewEra = 0x23,

	GovernanceSetApprovalPpmRequired = 0x30,
}

impl InternalFunction {
	/// Derive `Some` value from a `u8`, or `None` if it's invalid.
	pub fn from_u8(value: u8) -> Option<InternalFunction> {
		use self::*;
		let functions = [
			InternalFunction::SystemSetCode,
			InternalFunction::SessionSetLength,
			InternalFunction::SessionForceNewSession,
			InternalFunction::StakingSetSessionsPerEra,
			InternalFunction::StakingSetBondingDuration,
			InternalFunction::StakingSetValidatorCount,
			InternalFunction::StakingForceNewEra,
			InternalFunction::GovernanceSetApprovalPpmRequired,
		];
		functions.iter().map(|&f| f).find(|&f| value == f as u8)
	}
}

/// An internal function.
#[cfg_attr(feature = "with-std", derive(PartialEq, Debug))]
pub struct Proposal {
	/// The priviledged function to call.
	pub function: InternalFunction,
	/// The serialised data to call it with.
	pub input_data: Vec<u8>,
}

impl Slicable for Proposal {
	fn set_as_slice<F: Fn(&mut[u8], usize) -> bool>(fill_slice: &F) -> Option<Self> {
		Some(Proposal {
			function: InternalFunction::from_u8(Slicable::set_as_slice(fill_slice)?)?,
			input_data: Slicable::set_as_slice(&|s, o| fill_slice(s, o + 1))?,
		})
	}

	fn to_vec(&self) -> Vec<u8> {
		Vec::new()
			.join(&(self.function as u8))
			.join(&self.input_data)
	}

	fn size_of(data: &[u8]) -> Option<usize> {
		let first_part = mem::size_of::<u8>();
		let second_part = <Vec<u8>>::size_of(&data[first_part..])?;
		Some(first_part + second_part)
	}
}

impl Proposal {
	pub fn enact(&self) {
		let mut params = StreamReader::new(&self.input_data);
		match self.function {
			InternalFunction::SystemSetCode => {
				let code: Vec<u8> = params.read().unwrap();
				system::privileged::set_code(&code);
			}
			InternalFunction::SessionSetLength => {
				let value = params.read().unwrap();
				session::privileged::set_length(value);
			}
			InternalFunction::SessionForceNewSession => {
				session::privileged::force_new_session();
			}
			InternalFunction::StakingSetSessionsPerEra => {
				let value = params.read().unwrap();
				staking::privileged::set_sessions_per_era(value);
			}
			InternalFunction::StakingSetBondingDuration => {
				let value = params.read().unwrap();
				staking::privileged::set_bonding_duration(value);
			}
			InternalFunction::StakingSetValidatorCount => {
				let value = params.read().unwrap();
				staking::privileged::set_validator_count(value);
			}
			InternalFunction::StakingForceNewEra => {
				staking::privileged::force_new_era();
			}
			InternalFunction::GovernanceSetApprovalPpmRequired => {
				let value = params.read().unwrap();
				governance::privileged::set_approval_ppm_required(value);
			}
		}
	}
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
