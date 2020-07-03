// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Runtime API definition required by Contracts RPC extensions.
//!
//! This API should be imported and implemented by the runtime,
//! of a node that wants to use the custom RPC extension
//! adding Contracts access methods.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Codec, Decode, Encode};
use pallet_contracts_primitives::{GetStorageResult, RentProjectionResult};
use sp_runtime::RuntimeDebug;
use sp_std::vec::Vec;

/// A result of execution of a contract.
#[derive(Eq, PartialEq, Encode, Decode, RuntimeDebug)]
pub enum ContractExecResult {
	/// The contract returned successfully.
	///
	/// There is a status code and, optionally, some data returned by the contract.
	Success {
		/// Flags that the contract passed along on returning to alter its exit behaviour.
		/// Described in `pallet_contracts::exec::ReturnFlags`.
		flags: u32,
		/// Output data returned by the contract.
		///
		/// Can be empty.
		data: Vec<u8>,
		/// How much gas was consumed by the call.
		gas_consumed: u64,
	},
	/// The contract execution either trapped or returned an error.
	Error,
}

sp_api::decl_runtime_apis! {
	/// The API to interact with contracts without using executive.
	pub trait ContractsApi<AccountId, Balance, BlockNumber> where
		AccountId: Codec,
		Balance: Codec,
		BlockNumber: Codec,
	{
		/// Perform a call from a specified account to a given contract.
		///
		/// See the contracts' `call` dispatchable function for more details.
		fn call(
			origin: AccountId,
			dest: AccountId,
			value: Balance,
			gas_limit: u64,
			input_data: Vec<u8>,
		) -> ContractExecResult;

		/// Query a given storage key in a given contract.
		///
		/// Returns `Ok(Some(Vec<u8>))` if the storage value exists under the given key in the
		/// specified account and `Ok(None)` if it doesn't. If the account specified by the address
		/// doesn't exist, or doesn't have a contract or if the contract is a tombstone, then `Err`
		/// is returned.
		fn get_storage(
			address: AccountId,
			key: [u8; 32],
		) -> GetStorageResult;

		/// Returns the projected time a given contract will be able to sustain paying its rent.
		///
		/// The returned projection is relevant for the current block, i.e. it is as if the contract
		/// was accessed at the current block.
		///
		/// Returns `Err` if the contract is in a tombstone state or doesn't exist.
		fn rent_projection(address: AccountId) -> RentProjectionResult<BlockNumber>;
	}
}
