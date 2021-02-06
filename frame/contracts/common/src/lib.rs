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
use sp_runtime::{DispatchError, RuntimeDebug};
use sp_std::prelude::*;

/// Result type of a `bare_call` call.
///
/// The result of a contract execution along with a gas consumed.
#[derive(Eq, PartialEq, Encode, Decode, RuntimeDebug)]
pub struct ContractExecResult {
	pub exec_result: ExecResult,
	pub gas_consumed: u64,
}

/// Result type of a `get_storage` call.
pub type GetStorageResult = Result<Option<Vec<u8>>, ContractAccessError>;

/// Result type of a `rent_projection` call.
pub type RentProjectionResult<BlockNumber> =
	Result<RentProjection<BlockNumber>, ContractAccessError>;

/// The possible errors that can happen querying the storage of a contract.
#[derive(Eq, PartialEq, Encode, Decode, RuntimeDebug)]
pub enum ContractAccessError {
	/// The given address doesn't point to a contract.
	DoesntExist,
	/// The specified contract is a tombstone and thus cannot have any storage.
	IsTombstone,
}

#[derive(Eq, PartialEq, Encode, Decode, RuntimeDebug)]
pub enum RentProjection<BlockNumber> {
	/// Eviction is projected to happen at the specified block number.
	EvictionAt(BlockNumber),
	/// No eviction is scheduled.
	///
	/// E.g. Contract accumulated enough funds to offset the rent storage costs.
	NoEviction,
}

bitflags! {
	/// Flags used by a contract to customize exit behaviour.
	#[derive(Encode, Decode)]
	pub struct ReturnFlags: u32 {
		/// If this bit is set all changes made by the contract execution are rolled back.
		const REVERT = 0x0000_0001;
	}
}

/// Output of a contract call or instantiation which ran to completion.
#[derive(PartialEq, Eq, Encode, Decode, RuntimeDebug)]
pub struct ExecReturnValue {
	/// Flags passed along by `seal_return`. Empty when `seal_return` was never called.
	pub flags: ReturnFlags,
	/// Buffer passed along by `seal_return`. Empty when `seal_return` was never called.
	pub data: Vec<u8>,
}

impl ExecReturnValue {
	/// We understand the absense of a revert flag as success.
	pub fn is_success(&self) -> bool {
		!self.flags.contains(ReturnFlags::REVERT)
	}
}

/// Origin of the error.
///
/// Call or instantiate both called into other contracts and pass through errors happening
/// in those to the caller. This enum is for the caller to distinguish whether the error
/// happened during the execution of the callee or in the current execution context.
#[derive(PartialEq, Eq, Encode, Decode, RuntimeDebug)]
pub enum ErrorOrigin {
	/// Caller error origin.
	///
	/// The error happened in the current exeuction context rather than in the one
	/// of the contract that is called into.
	Caller,
	/// The error happened during execution of the called contract.
	Callee,
}

/// Error returned by contract exection.
#[derive(PartialEq, Eq, Encode, Decode, RuntimeDebug)]
pub struct ExecError {
	/// The reason why the execution failed.
	pub error: DispatchError,
	/// Origin of the error.
	pub origin: ErrorOrigin,
}

impl<T: Into<DispatchError>> From<T> for ExecError {
	fn from(error: T) -> Self {
		Self {
			error: error.into(),
			origin: ErrorOrigin::Caller,
		}
	}
}

/// The result that is returned from contract execution. It either contains the output
/// buffer or an error describing the reason for failure.
pub type ExecResult = Result<ExecReturnValue, ExecError>;
