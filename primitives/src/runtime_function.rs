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

//! Polkadot runtime functions.
//! This describes a function that can be called from an external transaction.

use bytes::Vec;
use codec::Slicable;

/// Public functions that can be dispatched to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[repr(u8)]
enum FunctionId {
	/// Set the timestamp.
	TimestampSet = 0x00,
	/// Set temporary session key as a validator.
	SessionSetKey = 0x10,
	/// Staking subsystem: begin staking.
	StakingStake = 0x20,
	/// Staking subsystem: stop staking.
	StakingUnstake = 0x21,
	/// Staking subsystem: transfer stake.
	StakingTransfer = 0x22,
	/// Make a proposal for the governance system.
	GovernancePropose = 0x30,
	/// Approve a proposal for the governance system.
	GovernanceApprove = 0x31,
}

impl FunctionId {
	/// Derive `Some` value from a `u8`, or `None` if it's invalid.
	fn from_u8(value: u8) -> Option<FunctionId> {
		use self::*;
		let functions = [FunctionId::StakingStake, FunctionId::StakingUnstake,
			FunctionId::StakingTransfer, FunctionId::SessionSetKey, FunctionId::TimestampSet,
			FunctionId::GovernancePropose, FunctionId::GovernanceApprove];
		functions.iter().map(|&f| f).find(|&f| value == f as u8)
	}
}

/// Functions on the runtime.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub enum Function {
	/// Set the timestamp.
	TimestampSet(::Timestamp),
	/// Set temporary session key as a validator.
	SessionSetKey(::SessionKey),
	/// Staking subsystem: begin staking.
	StakingStake,
	/// Staking subsystem: stop staking.
	StakingUnstake,
	/// Staking subsystem: transfer stake.
	StakingTransfer(::AccountId, ::Balance),
	/// Make a proposal for the governance system.
	GovernancePropose(::proposal::Proposal),
	/// Approve a proposal for the governance system.
	GovernanceApprove(::block::Number),
}

impl Slicable for Function {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		let id = try_opt!(u8::from_slice(value).and_then(FunctionId::from_u8));
		Some(match id {
			FunctionId::TimestampSet =>
				Function::TimestampSet(try_opt!(Slicable::from_slice(value))),
			FunctionId::SessionSetKey =>
				Function::SessionSetKey(try_opt!(Slicable::from_slice(value))),
			FunctionId::StakingStake => Function::StakingStake,
			FunctionId::StakingUnstake => Function::StakingUnstake,
			FunctionId::StakingTransfer => {
				let to  = try_opt!(Slicable::from_slice(value));
				let amount = try_opt!(Slicable::from_slice(value));

				Function::StakingTransfer(to, amount)
			}
			FunctionId::GovernancePropose =>
				Function::GovernancePropose(try_opt!(Slicable::from_slice(value))),
			FunctionId::GovernanceApprove =>
				Function::GovernanceApprove(try_opt!(Slicable::from_slice(value))),
		})
	}

	fn to_vec(&self) -> Vec<u8> {
		let mut v = Vec::new();
		match *self {
			Function::TimestampSet(ref data) => {
				(FunctionId::TimestampSet as u8).as_slice_then(|s| v.extend(s));
				data.as_slice_then(|s| v.extend(s));
			}
			Function::SessionSetKey(ref data) => {
				(FunctionId::SessionSetKey as u8).as_slice_then(|s| v.extend(s));
				data.as_slice_then(|s| v.extend(s));
			}
			Function::StakingStake => {
				(FunctionId::StakingStake as u8).as_slice_then(|s| v.extend(s));
			}
			Function::StakingUnstake => {
				(FunctionId::StakingUnstake as u8).as_slice_then(|s| v.extend(s));
			}
			Function::StakingTransfer(ref to, ref amount) => {
				(FunctionId::StakingTransfer as u8).as_slice_then(|s| v.extend(s));
				to.as_slice_then(|s| v.extend(s));
				amount.as_slice_then(|s| v.extend(s));
			}
			Function::GovernancePropose(ref data) => {
				(FunctionId::GovernancePropose as u8).as_slice_then(|s| v.extend(s));
				data.as_slice_then(|s| v.extend(s));
			}
			Function::GovernanceApprove(ref data) => {
				(FunctionId::GovernanceApprove as u8).as_slice_then(|s| v.extend(s));
				data.as_slice_then(|s| v.extend(s));
			}
		}

		v
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(self.to_vec().as_slice())
	}
}
