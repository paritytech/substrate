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

//! Node-specific RPC methods for interaction with contracts.

use std::sync::Arc;

use serde::{Serialize, Deserialize};
use client::blockchain::HeaderBackend;
use codec::Codec;
use jsonrpc_core::{Error, ErrorCode, Result};
use jsonrpc_derive::rpc;
use primitives::Bytes;
use sr_primitives::{
	generic::BlockId,
	traits::{Block as BlockT, ProvideRuntimeApi},
};
use rpc_primitives::number;

pub use srml_contracts_rpc_runtime_api::{ContractExecResult, ContractsApi as ContractsRuntimeApi};
pub use self::gen_client::Client as ContractsClient;

/// A struct that encodes RPC parameters required for a call to a smart-contract.
#[derive(Serialize, Deserialize)]
#[serde(rename_all="camelCase")]
#[serde(deny_unknown_fields)]
pub struct CallRequest<AccountId, Balance> {
	origin: AccountId,
	dest: AccountId,
	value: Balance,
	gas_limit: number::NumberOrHex<u64>,
	input_data: Bytes,
}

/// Contracts RPC methods.
#[rpc]
pub trait ContractsApi<BlockHash, AccountId, Balance> {
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
	) -> Result<ContractExecResult>;
}

/// An implementation of contract specific RPC methods.
pub struct Contracts<C, B> {
	client: Arc<C>,
	_marker: std::marker::PhantomData<B>,
}

impl<C, B> Contracts<C, B> {
	/// Create new `Contracts` with the given reference to the client.
	pub fn new(client: Arc<C>) -> Self {
		Contracts { client, _marker: Default::default() }
	}
}

const RUNTIME_ERROR: i64 = 1;

impl<C, Block, AccountId, Balance> ContractsApi<<Block as BlockT>::Hash, AccountId, Balance> for Contracts<C, Block>
where
	Block: BlockT,
	C: Send + Sync + 'static,
	C: ProvideRuntimeApi,
	C: HeaderBackend<Block>,
	C::Api: ContractsRuntimeApi<Block, AccountId, Balance>,
	AccountId: Codec,
	Balance: Codec,
{
	fn call(
		&self,
		call_request: CallRequest<AccountId, Balance>,
		at: Option<<Block as BlockT>::Hash>,
	) -> Result<ContractExecResult> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash
		));

		let CallRequest {
			origin,
			dest,
			value,
			gas_limit,
			input_data
		} = call_request;
		let gas_limit = gas_limit.to_number().map_err(|e| Error {
			code: ErrorCode::InvalidParams,
			message: e,
			data: None,
		})?;

		let exec_result = api
			.call(&at, origin, dest, value, gas_limit, input_data.to_vec())
			.map_err(|e| Error {
				code: ErrorCode::ServerError(RUNTIME_ERROR),
				message: "Runtime trapped while executing a contract.".into(),
				data: Some(format!("{:?}", e).into()),
			})?;

		Ok(exec_result)
	}
}
