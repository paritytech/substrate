use runtime::{staking, session};
use primitives::AccountID;
use streamreader::StreamReader;

/// The functions that a transaction can call (and be dispatched to).
#[cfg_attr(test, derive(PartialEq, Debug))]
#[derive(Clone, Copy)]
pub enum Function {
	StakingStake,
	StakingUnstake,
	StakingTransferStake,
	SessionSetKey,
}

impl Function {
	pub fn from_u8(value: u8) -> Option<Function> {
		match value {
			x if x == Function::StakingStake as u8 => Some(Function::StakingStake),
			x if x == Function::StakingUnstake as u8 => Some(Function::StakingUnstake),
			x if x == Function::StakingTransferStake as u8 => Some(Function::StakingTransferStake),
			x if x == Function::SessionSetKey as u8 => Some(Function::SessionSetKey),
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
			Function::StakingTransferStake => {
				let dest = params.read().unwrap();
				let value = params.read().unwrap();
				staking::transfer_stake(transactor, &dest, value);
			}
			Function::SessionSetKey => {
				let session = params.read().unwrap();
				session::set_key(transactor, &session);
			}
		}
	}
}
