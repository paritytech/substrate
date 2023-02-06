// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! A crate that hosts a common definitions that are relevant for the pallet-contracts.

#![cfg_attr(not(feature = "std"), no_std)]

use bitflags::bitflags;
use codec::{Decode, Encode};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{Saturating, Zero},
	DispatchError, RuntimeDebug,
};
use sp_std::prelude::*;
use sp_weights::Weight;

/// Result type of a `bare_call` or `bare_instantiate` call.
///
/// It contains the execution result together with some auxiliary information.
#[derive(Eq, PartialEq, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct ContractResult<R, Balance> {
	/// How much weight was consumed during execution.
	pub gas_consumed: Weight,
	/// How much weight is required as gas limit in order to execute this call.
	///
	/// This value should be used to determine the weight limit for on-chain execution.
	///
	/// # Note
	///
	/// This can only different from [`Self::gas_consumed`] when weight pre charging
	/// is used. Currently, only `seal_call_runtime` makes use of pre charging.
	/// Additionally, any `seal_call` or `seal_instantiate` makes use of pre-charging
	/// when a non-zero `gas_limit` argument is supplied.
	pub gas_required: Weight,
	/// How much balance was deposited and reserved during execution in order to pay for storage.
	///
	/// The storage deposit is never actually charged from the caller in case of [`Self::result`]
	/// is `Err`. This is because on error all storage changes are rolled back.
	pub storage_deposit: StorageDeposit<Balance>,
	/// An optional debug message. This message is only filled when explicitly requested
	/// by the code that calls into the contract. Otherwise it is empty.
	///
	/// The contained bytes are valid UTF-8. This is not declared as `String` because
	/// this type is not allowed within the runtime.
	///
	/// Clients should not make any assumptions about the format of the buffer.
	/// They should just display it as-is. It is **not** only a collection of log lines
	/// provided by a contract but a formatted buffer with different sections.
	///
	/// # Note
	///
	/// The debug message is never generated during on-chain execution. It is reserved for
	/// RPC calls.
	pub debug_message: Vec<u8>,
	/// The execution result of the wasm code.
	pub result: R,
}

/// Result type of a `bare_call` call.
pub type ContractExecResult<Balance> =
	ContractResult<Result<ExecReturnValue, DispatchError>, Balance>;

/// Result type of a `bare_instantiate` call.
pub type ContractInstantiateResult<AccountId, Balance> =
	ContractResult<Result<InstantiateReturnValue<AccountId>, DispatchError>, Balance>;

/// Result type of a `bare_code_upload` call.
pub type CodeUploadResult<CodeHash, Balance> =
	Result<CodeUploadReturnValue<CodeHash, Balance>, DispatchError>;

/// Result type of a `get_storage` call.
pub type GetStorageResult = Result<Option<Vec<u8>>, ContractAccessError>;

/// The possible errors that can happen querying the storage of a contract.
#[derive(Eq, PartialEq, Encode, Decode, RuntimeDebug, TypeInfo)]
pub enum ContractAccessError {
	/// The given address doesn't point to a contract.
	DoesntExist,
	/// Storage key cannot be decoded from the provided input data.
	KeyDecodingFailed,
}

bitflags! {
	/// Flags used by a contract to customize exit behaviour.
	#[derive(Encode, Decode, TypeInfo)]
	pub struct ReturnFlags: u32 {
		/// If this bit is set all changes made by the contract execution are rolled back.
		const REVERT = 0x0000_0001;
	}
}

/// Output of a contract call or instantiation which ran to completion.
#[derive(PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct ExecReturnValue {
	/// Flags passed along by `seal_return`. Empty when `seal_return` was never called.
	pub flags: ReturnFlags,
	/// Buffer passed along by `seal_return`. Empty when `seal_return` was never called.
	pub data: Vec<u8>,
}

impl ExecReturnValue {
	/// The contract did revert all storage changes.
	pub fn did_revert(&self) -> bool {
		self.flags.contains(ReturnFlags::REVERT)
	}
}

/// The result of a successful contract instantiation.
#[derive(PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct InstantiateReturnValue<AccountId> {
	/// The output of the called constructor.
	pub result: ExecReturnValue,
	/// The account id of the new contract.
	pub account_id: AccountId,
}

/// The result of succesfully uploading a contract.
#[derive(PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct CodeUploadReturnValue<CodeHash, Balance> {
	/// The key under which the new code is stored.
	pub code_hash: CodeHash,
	/// The deposit that was reserved at the caller. Is zero when the code already existed.
	pub deposit: Balance,
}

/// Reference to an existing code hash or a new wasm module.
#[derive(Eq, PartialEq, Encode, Decode, RuntimeDebug, TypeInfo)]
pub enum Code<Hash> {
	/// A wasm module as raw bytes.
	Upload(Vec<u8>),
	/// The code hash of an on-chain wasm blob.
	Existing(Hash),
}

impl<T: Into<Vec<u8>>, Hash> From<T> for Code<Hash> {
	fn from(from: T) -> Self {
		Code::Upload(from.into())
	}
}

/// The amount of balance that was either charged or refunded in order to pay for storage.
#[derive(Eq, PartialEq, Ord, PartialOrd, Encode, Decode, RuntimeDebug, Clone, TypeInfo)]
pub enum StorageDeposit<Balance> {
	/// The transaction reduced storage consumption.
	///
	/// This means that the specified amount of balance was transferred from the involved
	/// contracts to the call origin.
	Refund(Balance),
	/// The transaction increased overall storage usage.
	///
	/// This means that the specified amount of balance was transferred from the call origin
	/// to the contracts involved.
	Charge(Balance),
}

impl<Balance: Zero> Default for StorageDeposit<Balance> {
	fn default() -> Self {
		Self::Charge(Zero::zero())
	}
}

impl<Balance: Zero + Copy> StorageDeposit<Balance> {
	/// Returns how much balance is charged or `0` in case of a refund.
	pub fn charge_or_zero(&self) -> Balance {
		match self {
			Self::Charge(amount) => *amount,
			Self::Refund(_) => Zero::zero(),
		}
	}

	pub fn is_zero(&self) -> bool {
		match self {
			Self::Charge(amount) => amount.is_zero(),
			Self::Refund(amount) => amount.is_zero(),
		}
	}
}

impl<Balance> StorageDeposit<Balance>
where
	Balance: Saturating + Ord + Copy,
{
	/// This is essentially a saturating signed add.
	pub fn saturating_add(&self, rhs: &Self) -> Self {
		use StorageDeposit::*;
		match (self, rhs) {
			(Charge(lhs), Charge(rhs)) => Charge(lhs.saturating_add(*rhs)),
			(Refund(lhs), Refund(rhs)) => Refund(lhs.saturating_add(*rhs)),
			(Charge(lhs), Refund(rhs)) =>
				if lhs >= rhs {
					Charge(lhs.saturating_sub(*rhs))
				} else {
					Refund(rhs.saturating_sub(*lhs))
				},
			(Refund(lhs), Charge(rhs)) =>
				if lhs > rhs {
					Refund(lhs.saturating_sub(*rhs))
				} else {
					Charge(rhs.saturating_sub(*lhs))
				},
		}
	}

	/// This is essentially a saturating signed sub.
	pub fn saturating_sub(&self, rhs: &Self) -> Self {
		use StorageDeposit::*;
		match (self, rhs) {
			(Charge(lhs), Refund(rhs)) => Charge(lhs.saturating_add(*rhs)),
			(Refund(lhs), Charge(rhs)) => Refund(lhs.saturating_add(*rhs)),
			(Charge(lhs), Charge(rhs)) =>
				if lhs >= rhs {
					Charge(lhs.saturating_sub(*rhs))
				} else {
					Refund(rhs.saturating_sub(*lhs))
				},
			(Refund(lhs), Refund(rhs)) =>
				if lhs > rhs {
					Refund(lhs.saturating_sub(*rhs))
				} else {
					Charge(rhs.saturating_sub(*lhs))
				},
		}
	}

	/// If the amount of deposit (this type) is constrained by a `limit` this calcuates how
	/// much balance (if any) is still available from this limit.
	///
	/// # Note
	///
	/// In case of a refund the return value can be larger than `limit`.
	pub fn available(&self, limit: &Balance) -> Balance {
		use StorageDeposit::*;
		match self {
			Charge(amount) => limit.saturating_sub(*amount),
			Refund(amount) => limit.saturating_add(*amount),
		}
	}
}
