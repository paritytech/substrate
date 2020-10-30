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

//! Node-specific RPC methods for interaction with contracts.

use std::sync::Arc;

use codec::Codec;
use jsonrpc_core::{Error, ErrorCode, Result};
use jsonrpc_derive::rpc;
use pallet_contracts_primitives::RentProjection;
use serde::{Deserialize, Serialize};
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_core::{Bytes, H256};
use sp_rpc::number;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT},
};
use std::convert::TryInto;
use pallet_contracts_primitives::ContractExecResult;

pub use pallet_contracts_rpc_runtime_api::ContractsApi as ContractsRuntimeApi;

const RUNTIME_ERROR: i64 = 1;
const CONTRACT_DOESNT_EXIST: i64 = 2;
const CONTRACT_IS_A_TOMBSTONE: i64 = 3;

/// A rough estimate of how much gas a decent hardware consumes per second,
/// using native execution.
/// This value is used to set the upper bound for maximal contract calls to
/// prevent blocking the RPC for too long.
///
/// As 1 gas is equal to 1 weight we base this on the conducted benchmarks which
/// determined runtime weights:
/// https://github.com/paritytech/substrate/pull/5446
const GAS_PER_SECOND: u64 = 1_000_000_000_000;

/// A private newtype for converting `ContractAccessError` into an RPC error.
struct ContractAccessError(pallet_contracts_primitives::ContractAccessError);
impl From<ContractAccessError> for Error {
	fn from(e: ContractAccessError) -> Error {
		use pallet_contracts_primitives::ContractAccessError::*;
		match e.0 {
			DoesntExist => Error {
				code: ErrorCode::ServerError(CONTRACT_DOESNT_EXIST),
				message: "The specified contract doesn't exist.".into(),
				data: None,
			},
			IsTombstone => Error {
				code: ErrorCode::ServerError(CONTRACT_IS_A_TOMBSTONE),
				message: "The contract is a tombstone and doesn't have any storage.".into(),
				data: None,
			},
		}
	}
}

/// A struct that encodes RPC parameters required for a call to a smart-contract.
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct CallRequest<AccountId, Balance> {
	origin: AccountId,
	dest: AccountId,
	value: Balance,
	gas_limit: number::NumberOrHex,
	input_data: Bytes,
}

/// An RPC serializable result of contract execution
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub enum RpcContractExecResult {
	/// Successful execution
	Success {
		/// The return flags
		flags: u32,
		/// Output data
		data: Bytes,
		/// How much gas was consumed by the call.
		gas_consumed: u64,
	},
	/// Error execution
	Error(()),
}

impl From<ContractExecResult> for RpcContractExecResult {
	fn from(r: ContractExecResult) -> Self {
		match r.exec_result {
			Ok(val) => RpcContractExecResult::Success {
				flags: val.flags.bits(),
				data: val.data.into(),
				gas_consumed: r.gas_consumed,
			},
			_ => RpcContractExecResult::Error(()),
		}
	}
}

/// Contracts RPC methods.
#[rpc]
pub trait ContractsApi<BlockHash, BlockNumber, AccountId, Balance> {
	/// Executes a call to a contract.
	///
	/// This call is performed locally without submitting any transactions. Thus executing this
	/// won't change any state. Nonetheless, the calling state-changing contracts is still possible.
	///
	/// This method is useful for calling getter-like methods on contracts.
	#[rpc(name = "contracts_call")]
	fn call(
		&self,
		call_request: CallRequest<AccountId, Balance>,
		at: Option<BlockHash>,
	) -> Result<RpcContractExecResult>;

	/// Returns the value under a specified storage `key` in a contract given by `address` param,
	/// or `None` if it is not set.
	#[rpc(name = "contracts_getStorage")]
	fn get_storage(
		&self,
		address: AccountId,
		key: H256,
		at: Option<BlockHash>,
	) -> Result<Option<Bytes>>;

	/// Returns the projected time a given contract will be able to sustain paying its rent.
	///
	/// The returned projection is relevant for the given block, i.e. it is as if the contract was
	/// accessed at the beginning of that block.
	///
	/// Returns `None` if the contract is exempted from rent.
	#[rpc(name = "contracts_rentProjection")]
	fn rent_projection(
		&self,
		address: AccountId,
		at: Option<BlockHash>,
	) -> Result<Option<BlockNumber>>;
}

/// An implementation of contract specific RPC methods.
pub struct Contracts<C, B> {
	client: Arc<C>,
	_marker: std::marker::PhantomData<B>,
}

impl<C, B> Contracts<C, B> {
	/// Create new `Contracts` with the given reference to the client.
	pub fn new(client: Arc<C>) -> Self {
		Contracts {
			client,
			_marker: Default::default(),
		}
	}
}
impl<C, Block, AccountId, Balance>
	ContractsApi<
		<Block as BlockT>::Hash,
		<<Block as BlockT>::Header as HeaderT>::Number,
		AccountId,
		Balance,
	> for Contracts<C, Block>
where
	Block: BlockT,
	C: Send + Sync + 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
	C::Api: ContractsRuntimeApi<
		Block,
		AccountId,
		Balance,
		<<Block as BlockT>::Header as HeaderT>::Number,
	>,
	AccountId: Codec,
	Balance: Codec,
{
	fn call(
		&self,
		call_request: CallRequest<AccountId, Balance>,
		at: Option<<Block as BlockT>::Hash>,
	) -> Result<RpcContractExecResult> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash));

		let CallRequest {
			origin,
			dest,
			value,
			gas_limit,
			input_data,
		} = call_request;

		// Make sure that gas_limit fits into 64 bits.
		let gas_limit: u64 = gas_limit.try_into().map_err(|_| Error {
			code: ErrorCode::InvalidParams,
			message: format!("{:?} doesn't fit in 64 bit unsigned value", gas_limit),
			data: None,
		})?;

		let max_gas_limit = 5 * GAS_PER_SECOND;
		if gas_limit > max_gas_limit {
			return Err(Error {
				code: ErrorCode::InvalidParams,
				message: format!(
					"Requested gas limit is greater than maximum allowed: {} > {}",
					gas_limit, max_gas_limit
				),
				data: None,
			});
		}

		let exec_result = api
			.call(&at, origin, dest, value, gas_limit, input_data.to_vec())
			.map_err(runtime_error_into_rpc_err)?;

		Ok(exec_result.into())
	}

	fn get_storage(
		&self,
		address: AccountId,
		key: H256,
		at: Option<<Block as BlockT>::Hash>,
	) -> Result<Option<Bytes>> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash));

		let result = api
			.get_storage(&at, address, key.into())
			.map_err(runtime_error_into_rpc_err)?
			.map_err(ContractAccessError)?
			.map(Bytes);

		Ok(result)
	}

	fn rent_projection(
		&self,
		address: AccountId,
		at: Option<<Block as BlockT>::Hash>,
	) -> Result<Option<<<Block as BlockT>::Header as HeaderT>::Number>> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash));

		let result = api
			.rent_projection(&at, address)
			.map_err(runtime_error_into_rpc_err)?
			.map_err(ContractAccessError)?;

		Ok(match result {
			RentProjection::NoEviction => None,
			RentProjection::EvictionAt(block_num) => Some(block_num),
		})
	}
}

/// Converts a runtime trap into an RPC error.
fn runtime_error_into_rpc_err(err: impl std::fmt::Debug) -> Error {
	Error {
		code: ErrorCode::ServerError(RUNTIME_ERROR),
		message: "Runtime trapped".into(),
		data: Some(format!("{:?}", err).into()),
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::U256;

	#[test]
	fn call_request_should_serialize_deserialize_properly() {
		type Req = CallRequest<String, u128>;
		let req: Req = serde_json::from_str(r#"
		{
			"origin": "5CiPPseXPECbkjWCa6MnjNokrgYjMqmKndv2rSnekmSK2DjL",
			"dest": "5DRakbLVnjVrW6niwLfHGW24EeCEvDAFGEXrtaYS5M4ynoom",
			"value": 0,
			"gasLimit": 1000000000000,
			"inputData": "0x8c97db39"
		}
		"#).unwrap();
		assert_eq!(req.gas_limit.into_u256(), U256::from(0xe8d4a51000u64));
	}

	#[test]
	fn result_should_serialize_deserialize_properly() {
		fn test(expected: &str) {
			let res: RpcContractExecResult = serde_json::from_str(expected).unwrap();
			let actual = serde_json::to_string(&res).unwrap();
			assert_eq!(actual, expected);
		}
		test(r#"{"success":{"flags":5,"data":"0x1234","gas_consumed":5000}}"#);
		test(r#"{"error":null}"#);
	}
}
