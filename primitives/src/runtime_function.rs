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

/// Public functions that can be dispatched to.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[repr(u8)]
pub enum Function {
	/// Staking subsystem: begin staking.
	StakingStake = 0,
	/// Staking subsystem: stop staking.
	StakingUnstake = 1,
	/// Staking subsystem: transfer stake.
	StakingTransfer = 2,
	/// Set temporary session key as a validator.
	SessionSetKey = 3,
	/// Set the timestamp.
	TimestampSet = 4,
	/// Make a proposal for the governance system.
	GovernancePropose = 5,
	/// Approve a proposal for the governance system.
	GovernanceApprove = 6,
}

impl Function {
	/// Derive `Some` value from a `u8`, or `None` if it's invalid.
	pub fn from_u8(value: u8) -> Option<Function> {
		match value {
			0 => Some(Function::StakingStake),
			1 => Some(Function::StakingUnstake),
			2 => Some(Function::StakingTransfer),
			3 => Some(Function::SessionSetKey),
			4 => Some(Function::TimestampSet),
			5 => Some(Function::GovernancePropose),
			6 => Some(Function::GovernanceApprove),
			_ => None,
		}
	}
}
