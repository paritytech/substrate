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

//! Transaction type.

use bytes::Vec;
use codec::Slicable;

#[cfg(feature = "std")]
use std::fmt;

#[cfg(not(feature = "std"))]
use alloc::fmt;

use relay::block::Number as BlockNumber;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[repr(u8)]
enum InternalFunctionId {
	/// Set the system's code.
	SystemSetCode = 0x00,

	/// Set the session length.
	SessionSetLength = 0x10,
	/// Force a new session.
	SessionForceNewSession = 0x11,

	/// Set the number of sessions per era.
	StakingSetSessionsPerEra = 0x20,
	/// Set the minimum bonding duration for staking.
	StakingSetBondingDuration = 0x21,
	/// Set the validator count for staking.
	StakingSetValidatorCount = 0x22,
	/// Force a new staking era.
	StakingForceNewEra = 0x23,

	/// Set the per-mille of validator approval required for governance changes.
	GovernanceSetApprovalPpmRequired = 0x30,

}

impl InternalFunctionId {
	/// Derive `Some` value from a `u8`, or `None` if it's invalid.
	fn from_u8(value: u8) -> Option<InternalFunctionId> {
		let functions = [
			InternalFunctionId::SystemSetCode,
			InternalFunctionId::SessionSetLength,
			InternalFunctionId::SessionForceNewSession,
			InternalFunctionId::StakingSetSessionsPerEra,
			InternalFunctionId::StakingSetBondingDuration,
			InternalFunctionId::StakingSetValidatorCount,
			InternalFunctionId::StakingForceNewEra,
			InternalFunctionId::GovernanceSetApprovalPpmRequired,
		];
		functions.iter().map(|&f| f).find(|&f| value == f as u8)
	}
}

/// Internal functions that can be dispatched to.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub enum InternalFunction {
	/// Set the system's code.
	SystemSetCode(Vec<u8>),
	/// Set the session length.
	SessionSetLength(BlockNumber),
	/// Force a new session.
	SessionForceNewSession,
	/// Set the number of sessions per era.
	StakingSetSessionsPerEra(BlockNumber),
	/// Set the minimum bonding duration for staking.
	StakingSetBondingDuration(BlockNumber),
	/// Set the validator count for staking.
	StakingSetValidatorCount(u32),
	/// Force a new staking era.
	StakingForceNewEra,
	/// Set the per-mille of validator approval required for governance changes.
	GovernanceSetApprovalPpmRequired(u32),

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
			InternalFunctionId::SessionSetLength =>
				InternalFunction::SessionSetLength(try_opt!(Slicable::from_slice(value))),
			InternalFunctionId::SessionForceNewSession => InternalFunction::SessionForceNewSession,
			InternalFunctionId::StakingSetSessionsPerEra =>
				InternalFunction::StakingSetSessionsPerEra(try_opt!(Slicable::from_slice(value))),
			InternalFunctionId::StakingSetBondingDuration =>
				InternalFunction::StakingSetBondingDuration(try_opt!(Slicable::from_slice(value))),
			InternalFunctionId::StakingSetValidatorCount =>
				InternalFunction::StakingSetValidatorCount(try_opt!(Slicable::from_slice(value))),
			InternalFunctionId::StakingForceNewEra => InternalFunction::StakingForceNewEra,
			InternalFunctionId::GovernanceSetApprovalPpmRequired =>
				InternalFunction::GovernanceSetApprovalPpmRequired(try_opt!(Slicable::from_slice(value))),
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
			InternalFunction::SessionSetLength(ref data) => {
				(InternalFunctionId::SessionSetLength as u8).as_slice_then(|s| v.extend(s));
				data.as_slice_then(|s| v.extend(s));
			}
			InternalFunction::SessionForceNewSession => {
				(InternalFunctionId::SessionForceNewSession as u8).as_slice_then(|s| v.extend(s));
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
			InternalFunction::StakingForceNewEra => {
				(InternalFunctionId::StakingForceNewEra as u8).as_slice_then(|s| v.extend(s));
			}
			InternalFunction::GovernanceSetApprovalPpmRequired(ref data) => {
				(InternalFunctionId::GovernanceSetApprovalPpmRequired as u8).as_slice_then(|s| v.extend(s));
				data.as_slice_then(|s| v.extend(s));
			}
		}

		v
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(self.to_vec().as_slice())
	}
}


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
	TimestampSet(u64),
	/// Set temporary session key as a validator.
	SessionSetKey(::relay::SessionKey),
	/// Staking subsystem: begin staking.
	StakingStake,
	/// Staking subsystem: stop staking.
	StakingUnstake,
	/// Staking subsystem: transfer stake.
	StakingTransfer(::relay::AccountId, u64),
	/// Make a proposal for the governance system.
	GovernancePropose(Proposal),
	/// Approve a proposal for the governance system.
	GovernanceApprove(BlockNumber),
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

/// A vetted and verified transaction from the external world.
#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct Transaction {
	/// Who signed it (note this is not a signature).
	pub signed: super::AccountId,
	/// The number of transactions have come before from the same signer.
	pub nonce: super::TxOrder,
	/// The function that should be called.
	pub function: Function,
}

impl Slicable for Transaction {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		Some(Transaction {
			signed: try_opt!(Slicable::from_slice(value)),
			nonce: try_opt!(Slicable::from_slice(value)),
			function: try_opt!(Slicable::from_slice(value)),
		})
	}

	fn to_vec(&self) -> Vec<u8> {
		let mut v = Vec::new();

		self.signed.as_slice_then(|s| v.extend(s));
		self.nonce.as_slice_then(|s| v.extend(s));
		self.function.as_slice_then(|s| v.extend(s));

		v
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(self.to_vec().as_slice())
	}
}

/// A transactions right from the external world. Unchecked.
#[derive(Eq, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
pub struct UncheckedTransaction {
	/// The actual transaction information.
	pub transaction: Transaction,
	/// The signature; should be an Ed25519 signature applied to the serialised `transaction` field.
	pub signature: super::Signature,
}

impl Slicable for UncheckedTransaction {
	fn from_slice(value: &mut &[u8]) -> Option<Self> {
		Some(UncheckedTransaction {
			transaction: try_opt!(Transaction::from_slice(value)),
			signature: try_opt!(Slicable::from_slice(value)),
		})
	}

	fn to_vec(&self) -> Vec<u8> {
		let mut v = Vec::new();

		self.transaction.signed.as_slice_then(|s| v.extend(s));
		self.transaction.nonce.as_slice_then(|s| v.extend(s));
		self.transaction.function.as_slice_then(|s| v.extend(s));
		self.signature.as_slice_then(|s| v.extend(s));

		v
	}

	fn as_slice_then<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		f(self.to_vec().as_slice())
	}
}

impl ::codec::NonTrivialSlicable for UncheckedTransaction {}

impl PartialEq for UncheckedTransaction {
	fn eq(&self, other: &Self) -> bool {
		self.signature.iter().eq(other.signature.iter()) && self.transaction == other.transaction
	}
}

impl fmt::Debug for UncheckedTransaction {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "UncheckedTransaction({:?})", self.transaction)
	}
}

#[cfg(test)]
mod tests {
	use ::codec::Slicable;
	use super::*;

	#[test]
	fn serialize_unchecked() {
		let tx = UncheckedTransaction {
			transaction: Transaction {
				signed: [1; 32],
				nonce: 999u64,
				function: Function::TimestampSet(135135),
			},
			signature: ::hash::H512([0; 64]),
		};

		let v = Slicable::to_vec(&tx);
		assert_eq!(UncheckedTransaction::from_slice(&mut &v[..]).unwrap(), tx);
	}
}
