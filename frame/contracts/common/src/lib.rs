// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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
use sp_core::Bytes;
use sp_runtime::{
	traits::{Saturating, Zero},
	DispatchError, RuntimeDebug,
};
use sp_std::prelude::*;

#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};

#[cfg(feature = "std")]
use sp_rpc::number::NumberOrHex;

/// Result type of a `bare_call` or `bare_instantiate` call.
///
/// It contains the execution result together with some auxiliary information.
#[derive(Eq, PartialEq, Encode, Decode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[cfg_attr(
	feature = "std",
	serde(
		rename_all = "camelCase",
		bound(serialize = "R: Serialize, Balance: Copy + Into<NumberOrHex>"),
		bound(deserialize = "R: Deserialize<'de>, Balance: TryFrom<NumberOrHex>")
	)
)]
pub struct ContractResult<R, Balance> {
	/// How much gas was consumed during execution.
	pub gas_consumed: u64,
	/// How much gas is required as gas limit in order to execute this call.
	///
	/// This value should be used to determine the gas limit for on-chain execution.
	///
	/// # Note
	///
	/// This can only different from [`Self::gas_consumed`] when weight pre charging
	/// is used. Currently, only `seal_call_runtime` makes use of pre charging.
	/// Additionally, any `seal_call` or `seal_instantiate` makes use of pre-charging
	/// when a non-zero `gas_limit` argument is supplied.
	pub gas_required: u64,
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
	#[cfg_attr(feature = "std", serde(with = "as_string"))]
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
#[derive(Eq, PartialEq, Encode, Decode, RuntimeDebug)]
pub enum ContractAccessError {
	/// The given address doesn't point to a contract.
	DoesntExist,
}

bitflags! {
	/// Flags used by a contract to customize exit behaviour.
	#[derive(Encode, Decode)]
	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	#[cfg_attr(feature = "std", serde(rename_all = "camelCase", transparent))]
	pub struct ReturnFlags: u32 {
		/// If this bit is set all changes made by the contract execution are rolled back.
		const REVERT = 0x0000_0001;
	}
}

/// Output of a contract call or instantiation which ran to completion.
#[derive(PartialEq, Eq, Encode, Decode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
pub struct ExecReturnValue {
	/// Flags passed along by `seal_return`. Empty when `seal_return` was never called.
	pub flags: ReturnFlags,
	/// Buffer passed along by `seal_return`. Empty when `seal_return` was never called.
	pub data: Bytes,
}

impl ExecReturnValue {
	/// The contract did revert all storage changes.
	pub fn did_revert(&self) -> bool {
		self.flags.contains(ReturnFlags::REVERT)
	}
}

/// The result of a successful contract instantiation.
#[derive(PartialEq, Eq, Encode, Decode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
pub struct InstantiateReturnValue<AccountId> {
	/// The output of the called constructor.
	pub result: ExecReturnValue,
	/// The account id of the new contract.
	pub account_id: AccountId,
}

/// The result of succesfully uploading a contract.
#[derive(PartialEq, Eq, Encode, Decode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[cfg_attr(
	feature = "std",
	serde(
		rename_all = "camelCase",
		bound(serialize = "CodeHash: Serialize, Balance: Copy + Into<NumberOrHex>"),
		bound(deserialize = "CodeHash: Deserialize<'de>, Balance: TryFrom<NumberOrHex>")
	)
)]
pub struct CodeUploadReturnValue<CodeHash, Balance> {
	/// The key under which the new code is stored.
	pub code_hash: CodeHash,
	/// The deposit that was reserved at the caller. Is zero when the code already existed.
	#[cfg_attr(feature = "std", serde(with = "as_hex"))]
	pub deposit: Balance,
}

/// Reference to an existing code hash or a new wasm module.
#[derive(Eq, PartialEq, Encode, Decode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(rename_all = "camelCase"))]
pub enum Code<Hash> {
	/// A wasm module as raw bytes.
	Upload(Bytes),
	/// The code hash of an on-chain wasm blob.
	Existing(Hash),
}

impl<T: Into<Vec<u8>>, Hash> From<T> for Code<Hash> {
	fn from(from: T) -> Self {
		Code::Upload(Bytes(from.into()))
	}
}

/// The amount of balance that was either charged or refunded in order to pay for storage.
#[derive(Eq, PartialEq, Ord, PartialOrd, Encode, Decode, RuntimeDebug, Clone)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[cfg_attr(
	feature = "std",
	serde(
		rename_all = "camelCase",
		bound(serialize = "Balance: Copy + Into<NumberOrHex>"),
		bound(deserialize = "Balance: TryFrom<NumberOrHex>")
	)
)]
pub enum StorageDeposit<Balance> {
	/// The transaction reduced storage consumption.
	///
	/// This means that the specified amount of balance was transferred from the involved
	/// contracts to the call origin.
	#[cfg_attr(feature = "std", serde(with = "as_hex"))]
	Refund(Balance),
	/// The transaction increased overall storage usage.
	///
	/// This means that the specified amount of balance was transferred from the call origin
	/// to the contracts involved.
	#[cfg_attr(feature = "std", serde(with = "as_hex"))]
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

#[cfg(feature = "std")]
mod as_string {
	use super::*;
	use serde::{ser::Error, Deserializer, Serializer};

	pub fn serialize<S: Serializer>(bytes: &Vec<u8>, serializer: S) -> Result<S::Ok, S::Error> {
		std::str::from_utf8(bytes)
			.map_err(|e| S::Error::custom(format!("Debug buffer contains invalid UTF8: {}", e)))?
			.serialize(serializer)
	}

	pub fn deserialize<'de, D: Deserializer<'de>>(deserializer: D) -> Result<Vec<u8>, D::Error> {
		Ok(String::deserialize(deserializer)?.into_bytes())
	}
}

#[cfg(feature = "std")]
mod as_hex {
	use super::*;
	use serde::{de::Error as _, Deserializer, Serializer};

	pub fn serialize<S, Balance>(balance: &Balance, serializer: S) -> Result<S::Ok, S::Error>
	where
		S: Serializer,
		Balance: Copy + Into<NumberOrHex>,
	{
		Into::<NumberOrHex>::into(*balance).serialize(serializer)
	}

	pub fn deserialize<'de, D, Balance>(deserializer: D) -> Result<Balance, D::Error>
	where
		D: Deserializer<'de>,
		Balance: TryFrom<NumberOrHex>,
	{
		Balance::try_from(NumberOrHex::deserialize(deserializer)?)
			.map_err(|_| D::Error::custom("Cannot decode NumberOrHex to Balance"))
	}
}
