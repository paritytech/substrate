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

use runtime_support::{size_of, Vec};
use slicable::Slicable;
use joiner::Joiner;
use streamreader::StreamReader;
use runtime::{system, governance, staking, session};

/// Internal functions that can be dispatched to.
#[cfg_attr(test, derive(PartialEq, Debug))]
#[derive(Clone, Copy)]
pub enum InternalFunction {
	SystemSetCode,
	StakingSetSessionsPerEra,
	StakingSetBondingDuration,
	StakingSetValidatorCount,
	GovernanceSetApprovalPpmRequired,
	SessionSetLength,
}

impl InternalFunction {
	/// Derive `Some` value from a `u8`, or `None` if it's invalid.
	pub fn from_u8(value: u8) -> Option<InternalFunction> {
		match value {
			x if x == InternalFunction::SystemSetCode as u8 => Some(InternalFunction::SystemSetCode),
			x if x == InternalFunction::StakingSetSessionsPerEra as u8 => Some(InternalFunction::StakingSetSessionsPerEra),
			x if x == InternalFunction::StakingSetBondingDuration as u8 => Some(InternalFunction::StakingSetBondingDuration),
			x if x == InternalFunction::StakingSetValidatorCount as u8 => Some(InternalFunction::StakingSetValidatorCount),
			x if x == InternalFunction::GovernanceSetApprovalPpmRequired as u8 => Some(InternalFunction::GovernanceSetApprovalPpmRequired),
			x if x == InternalFunction::SessionSetLength as u8 => Some(InternalFunction::SessionSetLength),
			_ => None,
		}
	}
}

/// An internal function.
#[cfg_attr(test, derive(PartialEq, Debug))]
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
		let first_part = size_of::<u8>();
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
				system::set_code(&code);
			}
			InternalFunction::StakingSetSessionsPerEra => {
				let value = params.read().unwrap();
				staking::set_sessions_per_era(value);
			}
			InternalFunction::StakingSetBondingDuration => {
				let value = params.read().unwrap();
				staking::set_bonding_duration(value);
			}
			InternalFunction::StakingSetValidatorCount => {
				let value = params.read().unwrap();
				staking::set_validator_count(value);
			}
			InternalFunction::GovernanceSetApprovalPpmRequired => {
				let value = params.read().unwrap();
				governance::set_approval_ppm_required(value);
			}
			InternalFunction::SessionSetLength => {
				let value = params.read().unwrap();
				session::set_length(value);
			}
		}
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use statichex::StaticHexInto;

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
