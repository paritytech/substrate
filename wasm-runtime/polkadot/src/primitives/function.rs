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
use codec::StreamReader;
use runtime::{staking, session, timestamp, governance};

/// Public functions that can be dispatched to.
#[derive(Clone, Copy)]
#[cfg_attr(feature = "with-std", derive(PartialEq, Debug))]
#[repr(u8)]
pub enum Function {
	StakingStake = 0,
	StakingUnstake = 1,
	StakingTransfer = 2,
	SessionSetKey = 3,
	TimestampSet = 4,
	GovernancePropose = 5,
	GovernanceApprove = 6,
}

impl Function {
	/// Derive `Some` value from a `u8`, or `None` if it's invalid.
	pub fn from_u8(value: u8) -> Option<Function> {
		use self::*;
		let functions = [Function::StakingStake, Function::StakingUnstake,
			Function::StakingTransfer, Function::SessionSetKey, Function::TimestampSet,
			Function::GovernancePropose, Function::GovernanceApprove];
		if (value as usize) < functions.len() {
			Some(functions[value as usize])
		} else {
			None
		}
	}
}

impl Function {
	/// Dispatch the function.
	pub fn dispatch(&self, transactor: &AccountID, data: &[u8]) {
		let mut params = StreamReader::new(data);
		match *self {
			Function::StakingStake => {
				staking::public::stake(transactor);
			}
			Function::StakingUnstake => {
				staking::public::unstake(transactor);
			}
			Function::StakingTransfer => {
				let dest = params.read().unwrap();
				let value = params.read().unwrap();
				staking::public::transfer(transactor, &dest, value);
			}
			Function::SessionSetKey => {
				let session = params.read().unwrap();
				session::public::set_key(transactor, &session);
			}
			Function::TimestampSet => {
				let t = params.read().unwrap();
				timestamp::public::set(t);
			}
			Function::GovernancePropose => {
				let proposal = params.read().unwrap();
				governance::public::propose(transactor, &proposal);
			}
			Function::GovernanceApprove => {
				let era_index = params.read().unwrap();
				governance::public::approve(transactor, era_index);
			}
		}
	}
}
