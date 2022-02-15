// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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
use pallet_contracts_primitives::{
	Code, CodeUploadResult, ContractExecResult, ContractInstantiateResult,
};
use serde::{Deserialize, Serialize};
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_core::{Bytes, H256};
use sp_rpc::number::NumberOrHex;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT},
};

pub use pallet_contracts_rpc_runtime_api::ContractsApi as ContractsRuntimeApi;

const RUNTIME_ERROR: i64 = 1;
const CONTRACT_DOESNT_EXIST: i64 = 2;

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
impl From<ContractAccessError> for Error {
	fn from(e: ContractAccessError) -> Error {
		use pallet_contracts_primitives::ContractAccessError::*;
		match e.0 {
			DoesntExist => Error {
				code: ErrorCode::ServerError(CONTRACT_DOESNT_EXIST),
				message: "The specified contract doesn't exist.".into(),
				data: None,
			},
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
	storage_deposit_limit: Option<NumberOrHex>,
	input_data: Bytes,
}

/// A struct that encodes RPC parameters required to instantiate a new smart-contract.
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct InstantiateRequest<AccountId, Hash> {
	origin: AccountId,
	value: NumberOrHex,
	gas_limit: NumberOrHex,
	storage_deposit_limit: Option<NumberOrHex>,
	code: Code<Hash>,
	data: Bytes,
	salt: Bytes,
}

/// A struct that encodes RPC parameters required for a call to upload a new code.
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(deny_unknown_fields)]
pub struct CodeUploadRequest<AccountId> {
	origin: AccountId,
	code: Bytes,
	storage_deposit_limit: Option<NumberOrHex>,
}

/// Contracts RPC methods.
#[rpc]
pub trait ContractsApi<BlockHash, BlockNumber, AccountId, Balance, Hash>
where
	Balance: Copy + TryFrom<NumberOrHex> + Into<NumberOrHex>,
{
	/// Executes a call to a contract.
	///
	/// This call is performed locally without submitting any transactions. Thus executing this
	/// won't change any state. Nonetheless, the calling state-changing contracts is still possible.
	///
	/// This method is useful for calling getter-like methods on contracts or to dry-run a
	/// a contract call in order to determine the `gas_limit`.
	#[rpc(name = "contracts_call")]
	fn call(
		&self,
		call_request: CallRequest<AccountId>,
		at: Option<BlockHash>,
	) -> Result<ContractExecResult<Balance>>;

	/// Instantiate a new contract.
	///
	/// This instantiate is performed locally without submitting any transactions. Thus the contract
	/// is not actually created.
	///
	/// This method is useful for UIs to dry-run contract instantiations.
	#[rpc(name = "contracts_instantiate")]
	fn instantiate(
		&self,
		instantiate_request: InstantiateRequest<AccountId, Hash>,
		at: Option<BlockHash>,
	) -> Result<ContractInstantiateResult<AccountId, Balance>>;

	/// Upload new code without instantiating a contract from it.
	///
	/// This upload is performed locally without submitting any transactions. Thus executing this
	/// won't change any state.
	///
	/// This method is useful for UIs to dry-run code upload.
	#[rpc(name = "contracts_upload_code")]
	fn upload_code(
		&self,
		upload_request: CodeUploadRequest<AccountId>,
		at: Option<BlockHash>,
	) -> Result<CodeUploadResult<Hash, Balance>>;

	/// Returns the value under a specified storage `key` in a contract given by `address` param,
	/// or `None` if it is not set.
	#[rpc(name = "contracts_getStorage")]
	fn get_storage(
		&self,
		address: AccountId,
		key: H256,
		at: Option<BlockHash>,
	) -> Result<Option<Bytes>>;
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
impl<C, Block, AccountId, Balance, Hash>
	ContractsApi<
		<Block as BlockT>::Hash,
		<<Block as BlockT>::Header as HeaderT>::Number,
		AccountId,
		Balance,
		Hash,
	> for Contracts<C, Block>
where
	Block: BlockT,
	C: Send + Sync + 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
	C::Api: ContractsRuntimeApi<
		Block,
		AccountId,
		Balance,
		<<Block as BlockT>::Header as HeaderT>::Number,
		Hash,
	>,
	AccountId: Codec,
	Balance: Codec + Copy + TryFrom<NumberOrHex> + Into<NumberOrHex>,
	Hash: Codec,
{
	fn call(
		&self,
		call_request: CallRequest<AccountId>,
		at: Option<<Block as BlockT>::Hash>,
	) -> Result<ContractExecResult<Balance>> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash));

		let CallRequest { origin, dest, value, gas_limit, storage_deposit_limit, input_data } =
			call_request;

		let value: Balance = decode_hex(value, "balance")?;
		let gas_limit: Weight = decode_hex(gas_limit, "weight")?;
		let storage_deposit_limit: Option<Balance> =
			storage_deposit_limit.map(|l| decode_hex(l, "balance")).transpose()?;
		limit_gas(gas_limit)?;

		api.call(&at, origin, dest, value, gas_limit, storage_deposit_limit, input_data.to_vec())
			.map_err(runtime_error_into_rpc_err)
	}

	fn instantiate(
		&self,
		instantiate_request: InstantiateRequest<AccountId, Hash>,
		at: Option<<Block as BlockT>::Hash>,
	) -> Result<ContractInstantiateResult<AccountId, Balance>> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash));

		let InstantiateRequest {
			origin,
			value,
			gas_limit,
			storage_deposit_limit,
			code,
			data,
			salt,
		} = instantiate_request;

		let value: Balance = decode_hex(value, "balance")?;
		let gas_limit: Weight = decode_hex(gas_limit, "weight")?;
		let storage_deposit_limit: Option<Balance> =
			storage_deposit_limit.map(|l| decode_hex(l, "balance")).transpose()?;
		limit_gas(gas_limit)?;

		api.instantiate(
			&at,
			origin,
			value,
			gas_limit,
			storage_deposit_limit,
			code,
			data.to_vec(),
			salt.to_vec(),
		)
		.map_err(runtime_error_into_rpc_err)
	}

	fn upload_code(
		&self,
		upload_request: CodeUploadRequest<AccountId>,
		at: Option<<Block as BlockT>::Hash>,
	) -> Result<CodeUploadResult<Hash, Balance>> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash));

		let CodeUploadRequest { origin, code, storage_deposit_limit } = upload_request;

		let storage_deposit_limit: Option<Balance> =
			storage_deposit_limit.map(|l| decode_hex(l, "balance")).transpose()?;

		api.upload_code(&at, origin, code.to_vec(), storage_deposit_limit)
			.map_err(runtime_error_into_rpc_err)
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
}

/// Converts a runtime trap into an RPC error.
fn runtime_error_into_rpc_err(err: impl std::fmt::Display) -> Error {
	Error {
		code: ErrorCode::ServerError(RUNTIME_ERROR),
		message: "Runtime error".into(),
		data: Some(err.to_string().into()),
	}
}

fn decode_hex<H: std::fmt::Debug + Copy, T: TryFrom<H>>(from: H, name: &str) -> Result<T> {
	from.try_into().map_err(|_| Error {
		code: ErrorCode::InvalidParams,
		message: format!("{:?} does not fit into the {} type", from, name),
		data: None,
	})
}

fn limit_gas(gas_limit: Weight) -> Result<()> {
	if gas_limit > GAS_LIMIT {
		Err(Error {
			code: ErrorCode::InvalidParams,
			message: format!(
				"Requested gas limit is greater than maximum allowed: {} > {}",
				gas_limit, GAS_LIMIT
			),
			data: None,
		})
	} else {
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
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
			"storageDepositLimit": 5000,
			"inputData": "0x8c97db39"
		}
		"#,
		)
		.unwrap();
		assert_eq!(req.gas_limit.into_u256(), U256::from(0xe8d4a51000u64));
		assert_eq!(req.storage_deposit_limit.map(|l| l.into_u256()), Some(5000.into()));
		assert_eq!(req.value.into_u256(), U256::from(1234567890987654321u128));
	}

	#[test]
	fn instantiate_request_should_serialize_deserialize_properly() {
		type Req = InstantiateRequest<String, String>;
		let req: Req = serde_json::from_str(
			r#"
		{
			"origin": "5CiPPseXPECbkjWCa6MnjNokrgYjMqmKndv2rSnekmSK2DjL",
			"value": "0x88",
			"gasLimit": 42,
			"code": { "existing": "0x1122" },
			"data": "0x4299",
			"salt": "0x9988"
		}
		"#,
		)
		.unwrap();

		assert_eq!(req.origin, "5CiPPseXPECbkjWCa6MnjNokrgYjMqmKndv2rSnekmSK2DjL");
		assert_eq!(req.value.into_u256(), 0x88.into());
		assert_eq!(req.gas_limit.into_u256(), 42.into());
		assert_eq!(req.storage_deposit_limit, None);
		assert_eq!(&*req.data, [0x42, 0x99].as_ref());
		assert_eq!(&*req.salt, [0x99, 0x88].as_ref());
		let code = match req.code {
			Code::Existing(hash) => hash,
			_ => panic!("json encoded an existing hash"),
		};
		assert_eq!(&code, "0x1122");
	}

	#[test]
	fn code_upload_request_should_serialize_deserialize_properly() {
		type Req = CodeUploadRequest<String>;
		let req: Req = serde_json::from_str(
			r#"
		{
			"origin": "5CiPPseXPECbkjWCa6MnjNokrgYjMqmKndv2rSnekmSK2DjL",
			"code": "0x8c97db39",
			"storageDepositLimit": 5000
		}
		"#,
		)
		.unwrap();
		assert_eq!(req.origin, "5CiPPseXPECbkjWCa6MnjNokrgYjMqmKndv2rSnekmSK2DjL");
		assert_eq!(&*req.code, [0x8c, 0x97, 0xdb, 0x39].as_ref());
		assert_eq!(req.storage_deposit_limit.map(|l| l.into_u256()), Some(5000.into()));
	}

	#[test]
	fn call_result_should_serialize_deserialize_properly() {
		fn test(expected: &str) {
			let res: ContractExecResult<u32> = serde_json::from_str(expected).unwrap();
			let actual = serde_json::to_string(&res).unwrap();
			assert_eq!(actual, trim(expected).as_str());
		}
		test(
			r#"{
			"gasConsumed": 5000,
			"gasRequired": 8000,
			"storageDeposit": {"charge": 42000},
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
			"storageDeposit": {"refund": 12000},
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
			let res: ContractInstantiateResult<String, u32> =
				serde_json::from_str(expected).unwrap();
			let actual = serde_json::to_string(&res).unwrap();
			assert_eq!(actual, trim(expected).as_str());
		}
		test(
			r#"{
			"gasConsumed": 5000,
			"gasRequired": 8000,
			"storageDeposit": {"refund": 12000},
			"debugMessage": "HelloWorld",
			"result": {
			   "Ok": {
				  "result": {
					 "flags": 5,
					 "data": "0x1234"
				  },
				  "accountId": "5CiPP"
			   }
			}
		}"#,
		);
		test(
			r#"{
			"gasConsumed": 3400,
			"gasRequired": 5200,
			"storageDeposit": {"charge": 0},
			"debugMessage": "HelloWorld",
			"result": {
			  "Err": "BadOrigin"
			}
		}"#,
		);
	}

	#[test]
	fn code_upload_result_should_serialize_deserialize_properly() {
		fn test(expected: &str) {
			let res: CodeUploadResult<u32, u32> = serde_json::from_str(expected).unwrap();
			let actual = serde_json::to_string(&res).unwrap();
			assert_eq!(actual, trim(expected).as_str());
		}
		test(
			r#"{
				"Ok": {
					"codeHash": 4711,
					"deposit": 99
				}
			}"#,
		);
		test(
			r#"{
				"Err": "BadOrigin"
			}"#,
		);
	}
}
