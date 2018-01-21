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

//! Function data: This describes a function that can be called from an external transaction.

use primitives::AccountID;
use streamreader::StreamReader;
use runtime::{staking, session, timestamp, governance};

/// Public functions that can be dispatched to.
#[cfg_attr(test, derive(PartialEq, Debug))]
#[derive(Clone, Copy)]
pub enum Function {
	StakingStake,
	StakingUnstake,
	StakingTransfer,
	SessionSetKey,
	TimestampSet,
	GovernancePropose,
	GovernanceApprove,
}

impl Function {
	/// Derive `Some` value from a `u8`, or `None` if it's invalid.
	pub fn from_u8(value: u8) -> Option<Function> {
		match value {
			x if x == Function::StakingStake as u8 => Some(Function::StakingStake),
			x if x == Function::StakingUnstake as u8 => Some(Function::StakingUnstake),
			x if x == Function::StakingTransfer as u8 => Some(Function::StakingTransfer),
			x if x == Function::SessionSetKey as u8 => Some(Function::SessionSetKey),
			x if x == Function::TimestampSet as u8 => Some(Function::TimestampSet),
			x if x == Function::GovernancePropose as u8 => Some(Function::GovernancePropose),
			x if x == Function::GovernanceApprove as u8 => Some(Function::GovernanceApprove),
			_ => None,
		}
	}
}

impl Function {
	/// Dispatch the function.
	pub fn dispatch(&self, transactor: &AccountID, data: &[u8]) {
		let mut params = StreamReader::new(data);
		match *self {
			Function::StakingStake => {
				staking::stake(transactor);
			}
			Function::StakingUnstake => {
				staking::unstake(transactor);
			}
			Function::StakingTransfer => {
				let dest = params.read().unwrap();
				let value = params.read().unwrap();
				staking::transfer(transactor, &dest, value);
			}
			Function::SessionSetKey => {
				let session = params.read().unwrap();
				session::set_key(transactor, &session);
			}
			Function::TimestampSet => {
				let t = params.read().unwrap();
				timestamp::set(t);
			}
			Function::GovernancePropose => {
				let proposal = params.read().unwrap();
				governance::propose(transactor, &proposal);
			}
			Function::GovernanceApprove => {
				let era_index = params.read().unwrap();
				governance::approve(transactor, era_index);
			}
		}
	}
}
