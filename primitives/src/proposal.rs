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

use bytes::Vec;
use block::Number as BlockNumber;
use codec::Slicable;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[repr(u8)]
enum InternalFunctionId {
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

impl InternalFunctionId {
	/// Derive `Some` value from a `u8`, or `None` if it's invalid.
	fn from_u8(value: u8) -> Option<InternalFunctionId> {
		use self::*;
		let functions = [
			InternalFunctionId::SystemSetCode,
			InternalFunctionId::StakingSetSessionsPerEra,
			InternalFunctionId::StakingSetBondingDuration,
			InternalFunctionId::StakingSetValidatorCount,
			InternalFunctionId::GovernanceSetApprovalPpmRequired,
			InternalFunctionId::SessionSetLength
		];
		if (value as usize) < functions.len() {
			Some(functions[value as usize])
		} else {
			None
		}
	}
}

/// Internal functions that can be dispatched to.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub enum InternalFunction {
	/// Set the system's code.
	SystemSetCode(Vec<u8>),
	/// Set the number of sessions per era.
	StakingSetSessionsPerEra(BlockNumber),
	/// Set the minimum bonding duration for staking.
	StakingSetBondingDuration(BlockNumber),
	/// Set the validator count for staking.
	StakingSetValidatorCount(u32),
	/// Set the per-mille of validator approval required for governance changes.
	GovernanceSetApprovalPpmRequired(u32),
	/// Set the session length.
	SessionSetLength(BlockNumber),
}

/// An internal function.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct Proposal {
	/// The privileged function to call.
	pub function: InternalFunction,
}

impl Slicable for Proposal {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		let id = try_opt!(u8::from_slice(value).and_then(InternalFunctionId::from_u8));
		let function = match id {
			InternalFunctionId::SystemSetCode =>
				InternalFunction::SystemSetCode(try_opt!(Slicable::from_slice(value))),
			InternalFunctionId::StakingSetSessionsPerEra =>
				InternalFunction::StakingSetSessionsPerEra(try_opt!(Slicable::from_slice(value))),
			InternalFunctionId::StakingSetBondingDuration =>
				InternalFunction::StakingSetBondingDuration(try_opt!(Slicable::from_slice(value))),
			InternalFunctionId::StakingSetValidatorCount =>
				InternalFunction::StakingSetValidatorCount(try_opt!(Slicable::from_slice(value))),
			InternalFunctionId::GovernanceSetApprovalPpmRequired =>
				InternalFunction::GovernanceSetApprovalPpmRequired(try_opt!(Slicable::from_slice(value))),
			InternalFunctionId::SessionSetLength =>
				InternalFunction::SessionSetLength(try_opt!(Slicable::from_slice(value))),
		};

		Some(Proposal { function })
	}

	fn to_vec(&self) -> Vec<u8> {
		let mut v = Vec::new();
		match self.function {
			InternalFunction::SystemSetCode(ref data) => {
				(InternalFunctionId::SystemSetCode as u8).as_slice_then(|s| v.extend(s));
				data.as_slice_then(|s| v.extend(s));
			}
			InternalFunction::StakingSetSessionsPerEra(ref data) => {
				(InternalFunctionId::StakingSetSessionsPerEra as u8).as_slice_then(|s| v.extend(s));
				data.as_slice_then(|s| v.extend(s));
			}
			InternalFunction::StakingSetBondingDuration(ref data) => {
				(InternalFunctionId::StakingSetBondingDuration as u8).as_slice_then(|s| v.extend(s));
				data.as_slice_then(|s| v.extend(s));
			}
			InternalFunction::StakingSetValidatorCount(ref data) => {
				(InternalFunctionId::StakingSetValidatorCount as u8).as_slice_then(|s| v.extend(s));
				data.as_slice_then(|s| v.extend(s));
			}
			InternalFunction::GovernanceSetApprovalPpmRequired(ref data) => {
				(InternalFunctionId::GovernanceSetApprovalPpmRequired as u8).as_slice_then(|s| v.extend(s));
				data.as_slice_then(|s| v.extend(s));
			}
			InternalFunction::SessionSetLength(ref data) => {
				(InternalFunctionId::SessionSetLength as u8).as_slice_then(|s| v.extend(s));
				data.as_slice_then(|s| v.extend(s));
			}
		}

		v
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(self.to_vec().as_slice())
	}
}
