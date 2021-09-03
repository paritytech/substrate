// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

#![warn(unused_crate_dependencies)]

use std::{marker::PhantomData, sync::Arc};

use codec::Codec;
use jsonrpsee::{
	proc_macros::rpc,
	types::{
		async_trait,
		error::{CallError, Error as JsonRpseeError},
		JsonRpcResult,
	},
};
use pallet_contracts_primitives::{
	Code, ContractExecResult, ContractInstantiateResult, RentProjection,
};
use serde::{Deserialize, Serialize};
use serde_json::value::to_raw_value;
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_core::{Bytes, H256};
use sp_rpc::number::NumberOrHex;
use sp_runtime::{
	generic::BlockId,
	traits::{self, Block as BlockT, Header as HeaderT},
};
use std::convert::{TryFrom, TryInto};

pub use pallet_contracts_rpc_runtime_api::ContractsApi as ContractsRuntimeApi;

const RUNTIME_ERROR: i32 = 1;
const CONTRACT_DOESNT_EXIST: i32 = 2;
const CONTRACT_IS_A_TOMBSTONE: i32 = 3;

pub type Weight = u64;

/// A rough estimate of how much gas a decent hardware consumes per second,
/// using native execution.
/// This value is used to set the upper bound for maximal contract calls to
/// prevent blocking the RPC for too long.
///
/// As 1 gas is equal to 1 weight we base this on the conducted benchmarks which
/// determined runtime weights:
/// <https://github.com/paritytech/substrate/pull/5446>
const GAS_PER_SECOND: Weight = 1_000_000_000_000;

/// The maximum amount of weight that the call and instantiate rpcs are allowed to consume.
/// This puts a ceiling on the weight limit that is supplied to the rpc as an argument.
const GAS_LIMIT: Weight = 5 * GAS_PER_SECOND;

/// A private newtype for converting `ContractAccessError` into an RPC error.
struct ContractAccessError(pallet_contracts_primitives::ContractAccessError);
impl From<ContractAccessError> for JsonRpseeError {
	fn from(e: ContractAccessError) -> Self {
		use pallet_contracts_primitives::ContractAccessError::*;
		match e.0 {
			DoesntExist => CallError::Custom {
				code: CONTRACT_DOESNT_EXIST,
				message: "The specified contract doesn't exist.".into(),
				data: None,
			}
			.into(),
			IsTombstone => CallError::Custom {
				code: CONTRACT_IS_A_TOMBSTONE,
				message: "The contract is a tombstone and doesn't have any storage.".into(),
				data: None,
			}
			.into(),
		}
	}
}

/// A struct that encodes RPC parameters required for a call to a smart-contract.
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct CallRequest<AccountId> {
	origin: AccountId,
	dest: AccountId,
	value: NumberOrHex,
	gas_limit: NumberOrHex,
	input_data: Bytes,
}

/// A struct that encodes RPC parameters required to instantiate a new smart-contract.
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct InstantiateRequest<AccountId, Hash> {
	origin: AccountId,
	endowment: NumberOrHex,
	gas_limit: NumberOrHex,
	code: Code<Hash>,
	data: Bytes,
	salt: Bytes,
}

/// Contracts RPC methods.
#[rpc(client, server, namespace = "contracts")]
pub trait ContractsApi<BlockHash, BlockNumber, AccountId, Balance, Hash> {
	/// Executes a call to a contract.
	///
	/// This call is performed locally without submitting any transactions. Thus executing this
	/// won't change any state. Nonetheless, the calling state-changing contracts is still possible.
	///
	/// This method is useful for calling getter-like methods on contracts.
	#[method(name = "call")]
	fn call(
		&self,
		call_request: CallRequest<AccountId>,
		at: Option<BlockHash>,
	) -> JsonRpcResult<ContractExecResult>;

	/// Instantiate a new contract.
	///
	/// This call is performed locally without submitting any transactions. Thus the contract
	/// is not actually created.
	///
	/// This method is useful for UIs to dry-run contract instantiations.
	#[method(name = "instantiate")]
	fn instantiate(
		&self,
		instantiate_request: InstantiateRequest<AccountId, Hash>,
		at: Option<BlockHash>,
	) -> JsonRpcResult<ContractInstantiateResult<AccountId, BlockNumber>>;

	/// Returns the value under a specified storage `key` in a contract given by `address` param,
	/// or `None` if it is not set.
	#[method(name = "getStorage")]
	fn get_storage(
		&self,
		address: AccountId,
		key: H256,
		at: Option<BlockHash>,
	) -> JsonRpcResult<Option<Bytes>>;

	/// Returns the projected time a given contract will be able to sustain paying its rent.
	///
	/// The returned projection is relevant for the given block, i.e. it is as if the contract was
	/// accessed at the beginning of that block.
	///
	/// Returns `None` if the contract is exempted from rent.
	#[method(name = "rentProjection")]
	fn rent_projection(
		&self,
		address: AccountId,
		at: Option<BlockHash>,
	) -> JsonRpcResult<Option<BlockNumber>>;
}

/// Contracts RPC methods.
pub struct ContractsRpc<Client, Block, AccountId, Balance, Hash> {
	client: Arc<Client>,
	_block: PhantomData<Block>,
	_account_id: PhantomData<AccountId>,
	_balance: PhantomData<Balance>,
	_hash: PhantomData<Hash>,
}

impl<Client, Block, AccountId, Balance, Hash>
	ContractsRpc<Client, Block, AccountId, Balance, Hash>
{
	/// Create new `Contracts` with the given reference to the client.
	pub fn new(client: Arc<Client>) -> Self {
		Self {
			client,
			_block: Default::default(),
			_account_id: Default::default(),
			_balance: Default::default(),
			_hash: Default::default(),
		}
	}
}

#[async_trait]
impl<Client, Block, AccountId, Balance, Hash>
	ContractsApiServer<
		<Block as BlockT>::Hash,
		<<Block as BlockT>::Header as HeaderT>::Number,
		AccountId,
		Balance,
		Hash,
	> for ContractsRpc<Client, Block, AccountId, Balance, Hash>
where
	Block: BlockT,
	Client: Send + Sync + 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
	Client::Api: ContractsRuntimeApi<
		Block,
		AccountId,
		Balance,
		<<Block as BlockT>::Header as HeaderT>::Number,
		Hash,
	>,
	AccountId: traits::MaybeSerializeDeserialize + Codec + Send + Sync + 'static,
	Balance: Codec + TryFrom<NumberOrHex> + Send + Sync + 'static,
	Hash: traits::MaybeSerializeDeserialize + Codec + Send + Sync + 'static,
{
	fn call(
		&self,
		call_request: CallRequest<AccountId>,
		at: Option<<Block as BlockT>::Hash>,
	) -> JsonRpcResult<ContractExecResult> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(|| self.client.info().best_hash));

		let CallRequest { origin, dest, value, gas_limit, input_data } = call_request;

		let value: Balance = decode_hex(value, "balance")?;
		let gas_limit: Weight = decode_hex(gas_limit, "weight")?;
		limit_gas(gas_limit)?;

		let exec_result = api
			.call(&at, origin, dest, value, gas_limit, input_data.to_vec())
			.map_err(runtime_error_into_rpc_err)?;

		Ok(exec_result)
	}

	fn instantiate(
		&self,
		instantiate_request: InstantiateRequest<AccountId, Hash>,
		at: Option<<Block as BlockT>::Hash>,
	) -> JsonRpcResult<
		ContractInstantiateResult<AccountId, <<Block as BlockT>::Header as HeaderT>::Number>,
	> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(|| self.client.info().best_hash));
		let InstantiateRequest { origin, endowment, gas_limit, code, data, salt } =
			instantiate_request;

		let endowment: Balance = decode_hex(endowment, "balance")?;
		let gas_limit: Weight = decode_hex(gas_limit, "weight")?;
		limit_gas(gas_limit)?;

		let exec_result = api
			.instantiate(&at, origin, endowment, gas_limit, code, data.to_vec(), salt.to_vec())
			.map_err(runtime_error_into_rpc_err)?;

		Ok(exec_result)
	}

	fn get_storage(
		&self,
		address: AccountId,
		key: H256,
		at: Option<<Block as BlockT>::Hash>,
	) -> JsonRpcResult<Option<Bytes>> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(|| self.client.info().best_hash));
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
	) -> JsonRpcResult<Option<<<Block as BlockT>::Header as HeaderT>::Number>> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(|| self.client.info().best_hash));

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
fn runtime_error_into_rpc_err(err: impl std::fmt::Debug) -> JsonRpseeError {
	CallError::Custom {
		code: RUNTIME_ERROR,
		message: "Runtime error".into(),
		data: to_raw_value(&format!("{:?}", err)).ok(),
	}
	.into()
}

fn decode_hex<H: std::fmt::Debug + Copy, T: TryFrom<H>>(
	from: H,
	name: &str,
) -> Result<T, JsonRpseeError> {
	from.try_into().map_err(|_| {
		CallError::Custom {
			code: -32602, // TODO: was `ErrorCode::InvalidParams`
			message: format!("{:?} does not fit into the {} type", from, name),
			data: None,
		}
		.into()
	})
}

fn limit_gas(gas_limit: Weight) -> Result<(), JsonRpseeError> {
	if gas_limit > GAS_LIMIT {
		Err(CallError::Custom {
			code: -32602, // TODO: was `ErrorCode::InvalidParams,`
			message: format!(
				"Requested gas limit is greater than maximum allowed: {} > {}",
				gas_limit, GAS_LIMIT
			),
			data: None,
		}
		.into())
	} else {
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use pallet_contracts_primitives::{ContractExecResult, ContractInstantiateResult};
	use sp_core::U256;

	fn trim(json: &str) -> String {
		json.chars().filter(|c| !c.is_whitespace()).collect()
	}

	#[test]
	fn call_request_should_serialize_deserialize_properly() {
		type Req = CallRequest<String>;
		let req: Req = serde_json::from_str(
			r#"
		{
			"origin": "5CiPPseXPECbkjWCa6MnjNokrgYjMqmKndv2rSnekmSK2DjL",
			"dest": "5DRakbLVnjVrW6niwLfHGW24EeCEvDAFGEXrtaYS5M4ynoom",
			"value": "0x112210f4B16c1cb1",
			"gasLimit": 1000000000000,
			"inputData": "0x8c97db39"
		}
		"#,
		)
		.unwrap();
		assert_eq!(req.gas_limit.into_u256(), U256::from(0xe8d4a51000u64));
		assert_eq!(req.value.into_u256(), U256::from(1234567890987654321u128));
	}

	#[test]
	fn instantiate_request_should_serialize_deserialize_properly() {
		type Req = InstantiateRequest<String, String>;
		let req: Req = serde_json::from_str(
			r#"
		{
			"origin": "5CiPPseXPECbkjWCa6MnjNokrgYjMqmKndv2rSnekmSK2DjL",
			"endowment": "0x88",
			"gasLimit": 42,
			"code": { "existing": "0x1122" },
			"data": "0x4299",
			"salt": "0x9988"
		}
		"#,
		)
		.unwrap();

		assert_eq!(req.origin, "5CiPPseXPECbkjWCa6MnjNokrgYjMqmKndv2rSnekmSK2DjL");
		assert_eq!(req.endowment.into_u256(), 0x88.into());
		assert_eq!(req.gas_limit.into_u256(), 42.into());
		assert_eq!(&*req.data, [0x42, 0x99].as_ref());
		assert_eq!(&*req.salt, [0x99, 0x88].as_ref());
		let code = match req.code {
			Code::Existing(hash) => hash,
			_ => panic!("json encoded an existing hash"),
		};
		assert_eq!(&code, "0x1122");
	}

	#[test]
	fn call_result_should_serialize_deserialize_properly() {
		fn test(expected: &str) {
			let res: ContractExecResult = serde_json::from_str(expected).unwrap();
			let actual = serde_json::to_string(&res).unwrap();
			assert_eq!(actual, trim(expected).as_str());
		}
		test(
			r#"{
			"gasConsumed": 5000,
			"gasRequired": 8000,
			"debugMessage": "HelloWorld",
			"result": {
			  "Ok": {
				"flags": 5,
				"data": "0x1234"
			  }
			}
		}"#,
		);
		test(
			r#"{
			"gasConsumed": 3400,
			"gasRequired": 5200,
			"debugMessage": "HelloWorld",
			"result": {
			  "Err": "BadOrigin"
			}
		}"#,
		);
	}

	#[test]
	fn instantiate_result_should_serialize_deserialize_properly() {
		fn test(expected: &str) {
			let res: ContractInstantiateResult<String, u64> =
				serde_json::from_str(expected).unwrap();
			let actual = serde_json::to_string(&res).unwrap();
			assert_eq!(actual, trim(expected).as_str());
		}
		test(
			r#"{
			"gasConsumed": 5000,
			"gasRequired": 8000,
			"debugMessage": "HelloWorld",
			"result": {
			   "Ok": {
				  "result": {
					 "flags": 5,
					 "data": "0x1234"
				  },
				  "accountId": "5CiPP",
				  "rentProjection": null
			   }
			}
		}"#,
		);
		test(
			r#"{
			"gasConsumed": 3400,
			"gasRequired": 5200,
			"debugMessage": "HelloWorld",
			"result": {
			  "Err": "BadOrigin"
			}
		}"#,
		);
	}
}
