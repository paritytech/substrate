// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Runtime API definition required by Contracts RPC extensions.
//!
//! This API should be imported and implemented by the runtime,
//! of a node that wants to use the custom RPC extension
//! adding Contracts access methods.

#![cfg_attr(not(feature = "std"), no_std)]

use rstd::vec::Vec;
use codec::{Encode, Decode, Codec};
use sp_runtime::RuntimeDebug;

/// A result of execution of a contract.
#[derive(Eq, PartialEq, Encode, Decode, RuntimeDebug)]
pub enum ContractExecResult {
	/// The contract returned successfully.
	///
	/// There is a status code and, optionally, some data returned by the contract.
	Success {
		/// Status code returned by the contract.
		status: u8,
		/// Output data returned by the contract.
		///
		/// Can be empty.
		data: Vec<u8>,
	},
	/// The contract execution either trapped or returned an error.
	Error,
}

/// A result type of the get storage call.
///
/// See [`ContractsApi::get_storage`] for more info.
pub type GetStorageResult = Result<Option<Vec<u8>>, GetStorageError>;

/// The possible errors that can happen querying the storage of a contract.
#[derive(Eq, PartialEq, Encode, Decode, RuntimeDebug)]
pub enum GetStorageError {
	/// The given address doesn't point on a contract.
	ContractDoesntExist,
	/// The specified contract is a tombstone and thus cannot have any storage.
	IsTombstone,
}

sp_api::decl_runtime_apis! {
	/// The API to interact with contracts without using executive.
	pub trait ContractsApi<AccountId, Balance> where
		AccountId: Codec,
		Balance: Codec,
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
	}
}
