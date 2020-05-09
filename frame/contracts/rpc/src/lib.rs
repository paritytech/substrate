// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

pub use self::gen_client::Client as ContractsClient;
pub use pallet_contracts_rpc_runtime_api::{
	self as runtime_api, ContractExecResult, ContractsApi as ContractsRuntimeApi,
};

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
	gas_limit: number::NumberOrHex<u64>,
	input_data: Bytes,
}

/// An RPC serializable result of contract execution
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
#[serde(rename_all = "camelCase")]
pub enum RpcContractExecResult {
	/// Successful execution
	Success {
		/// Status code
		status: u8,
		/// Output data
		data: Bytes,
	},
	/// Error execution
	Error(()),
}

impl From<ContractExecResult> for RpcContractExecResult {
	fn from(r: ContractExecResult) -> Self {
		match r {
			ContractExecResult::Success { status, data } => RpcContractExecResult::Success {
				status,
				data: data.into(),
			},
			ContractExecResult::Error => RpcContractExecResult::Error(()),
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
		let gas_limit = gas_limit.to_number().map_err(|e| Error {
			code: ErrorCode::InvalidParams,
			message: e,
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
			.map_err(|e| runtime_error_into_rpc_err(e))?;

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
			.map_err(|e| runtime_error_into_rpc_err(e))?
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
			.map_err(|e| runtime_error_into_rpc_err(e))?
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

	#[test]
	fn should_serialize_deserialize_properly() {
		fn test(expected: &str) {
			let res: RpcContractExecResult = serde_json::from_str(expected).unwrap();
			let actual = serde_json::to_string(&res).unwrap();
			assert_eq!(actual, expected);
		}

		test(r#"{"success":{"status":5,"data":"0x1234"}}"#);
		test(r#"{"error":null}"#);
	}
}
