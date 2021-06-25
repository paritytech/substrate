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

//! RPC interface for the transaction payment module.

use std::sync::Arc;
use std::convert::TryInto;
use codec::{Codec, Decode};
use sp_blockchain::HeaderBackend;
use jsonrpsee_types::error::Error as JsonRpseeError;
use jsonrpsee_types::error::CallError;
use jsonrpsee::RpcModule;
// TODO: (dp) remove
use jsonrpc_core::{Error as RpcError, ErrorCode, Result as OldResult};
use jsonrpc_derive::rpc;
use sp_runtime::{generic::BlockId, traits::{Block as BlockT, MaybeDisplay}};
use sp_api::ProvideRuntimeApi;
use sp_core::Bytes;
use sp_rpc::number::NumberOrHex;
use pallet_transaction_payment_rpc_runtime_api::{FeeDetails, InclusionFee, RuntimeDispatchInfo};
pub use pallet_transaction_payment_rpc_runtime_api::TransactionPaymentApi as TransactionPaymentRuntimeApi;
pub use self::gen_client::Client as TransactionPaymentClient;

/// Provides RPC methods for interacting with Babe.
pub struct TransactionPaymentRpc<C, Block, Balance> {
	/// Shared reference to the client.
	client: Arc<C>,
	_block_marker: std::marker::PhantomData<Block>,
	_balance_marker: std::marker::PhantomData<Balance>,
}

impl<C, Block, Balance> TransactionPaymentRpc<C, Block, Balance>
where
	Block: BlockT,
	C: ProvideRuntimeApi<Block> + HeaderBackend<Block> + Send + Sync + 'static,
	C::Api: TransactionPaymentRuntimeApi<Block, Balance>,
	Balance: Codec + MaybeDisplay + Copy + TryInto<NumberOrHex> + Send + Sync + 'static,
{
	/// Creates a new instance of the BabeRpc handler.
	pub fn new(
		client: Arc<C>,
	) -> Self {
		Self { client, _block_marker: Default::default(), _balance_marker: Default::default() }
	}

	/// Convert this [`TransactionPaymentRpc`] to an [`RpcModule`].
	pub fn into_rpc_module(self) -> Result<RpcModule<Self>, JsonRpseeError> {
		let mut module = RpcModule::new(self);
		module.register_method::<RuntimeDispatchInfo<Balance>, _>("payment_queryInfo", |params, trx_payment| {
			let (encoded_xt, at): (Bytes, Option<<Block as BlockT>::Hash>) = params.parse()?;

			let api = trx_payment.client.runtime_api();
			let at = BlockId::hash(at.unwrap_or_else(|| trx_payment.client.info().best_hash));

			let encoded_len = encoded_xt.len() as u32;

			let uxt: Block::Extrinsic = Decode::decode(&mut &*encoded_xt)
				.map_err(|codec_err| CallError::Failed(Box::new(codec_err)))?;
			api
				.query_info(&at, uxt, encoded_len)
				.map_err(|api_err| CallError::Failed(Box::new(api_err)))
		})?;

		module.register_method("payment_queryFeeDetails", |params, trx_payment| {
			let (encoded_xt, at): (Bytes, Option<<Block as BlockT>::Hash>) = params.parse()?;

			let api = trx_payment.client.runtime_api();
			let at = BlockId::hash(at.unwrap_or_else(|| trx_payment.client.info().best_hash));

			let encoded_len = encoded_xt.len() as u32;

			let uxt: Block::Extrinsic = Decode::decode(&mut &*encoded_xt)
				.map_err(|codec_err| CallError::Failed(Box::new(codec_err)))?;
			let fee_details = api.query_fee_details(&at, uxt, encoded_len)
				.map_err(|api_err| CallError::Failed(Box::new(api_err)))?;

			let try_into_rpc_balance = |value: Balance| {
				value
					.try_into()
					.map_err(|_try_err| CallError::InvalidParams)
			};

			Ok(FeeDetails {
				inclusion_fee: if let Some(inclusion_fee) = fee_details.inclusion_fee {
					Some(InclusionFee {
						base_fee: try_into_rpc_balance(inclusion_fee.base_fee)?,
						len_fee: try_into_rpc_balance(inclusion_fee.len_fee)?,
						adjusted_weight_fee: try_into_rpc_balance(inclusion_fee.adjusted_weight_fee)?,
					})
				} else {
					None
				},
				tip: Default::default(),
			})
		})?;

		Ok(module)
	}
}

#[rpc]
pub trait TransactionPaymentApiRemoveMe<BlockHash, ResponseType> {
	#[rpc(name = "payment_queryInfo")]
	fn query_info(
		&self,
		encoded_xt: Bytes,
		at: Option<BlockHash>
	) -> OldResult<ResponseType>;
	#[rpc(name = "payment_queryFeeDetails")]
	fn query_fee_details(
		&self,
		encoded_xt: Bytes,
		at: Option<BlockHash>
	) -> OldResult<FeeDetails<NumberOrHex>>;
}

/// A struct that implements the [`TransactionPaymentApi`].
pub struct TransactionPayment<C, P> {
	client: Arc<C>,
	_marker: std::marker::PhantomData<P>,
}

impl<C, P> TransactionPayment<C, P> {
	/// Create new `TransactionPayment` with the given reference to the client.
	pub fn new(client: Arc<C>) -> Self {
		Self { client, _marker: Default::default() }
	}
}

// TODO: (dp) used?
/// Error type of this RPC api.
pub enum Error {
	/// The transaction was not decodable.
	DecodeError,
	/// The call to runtime failed.
	RuntimeError,
}

// TODO: (dp) used?
impl From<Error> for i64 {
	fn from(e: Error) -> i64 {
		match e {
			Error::RuntimeError => 1,
			Error::DecodeError => 2,
		}
	}
}

impl<C, Block, Balance> TransactionPaymentApiRemoveMe<
	<Block as BlockT>::Hash,
	RuntimeDispatchInfo<Balance>,
> for TransactionPayment<C, Block>
where
	Block: BlockT,
	C: 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
	C::Api: TransactionPaymentRuntimeApi<Block, Balance>,
	Balance: Codec + MaybeDisplay + Copy + TryInto<NumberOrHex>,
{
	fn query_info(
		&self,
		encoded_xt: Bytes,
		at: Option<<Block as BlockT>::Hash>
	) -> OldResult<RuntimeDispatchInfo<Balance>> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash
		));

		let encoded_len = encoded_xt.len() as u32;

		let uxt: Block::Extrinsic = Decode::decode(&mut &*encoded_xt).map_err(|e| RpcError {
			code: ErrorCode::ServerError(Error::DecodeError.into()),
			message: "Unable to query dispatch info.".into(),
			data: Some(format!("{:?}", e).into()),
		})?;
		api.query_info(&at, uxt, encoded_len).map_err(|e| RpcError {
			code: ErrorCode::ServerError(Error::RuntimeError.into()),
			message: "Unable to query dispatch info.".into(),
			data: Some(format!("{:?}", e).into()),
		})
	}

	fn query_fee_details(
		&self,
		encoded_xt: Bytes,
		at: Option<<Block as BlockT>::Hash>,
	) -> OldResult<FeeDetails<NumberOrHex>> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash
		));

		let encoded_len = encoded_xt.len() as u32;

		let uxt: Block::Extrinsic = Decode::decode(&mut &*encoded_xt).map_err(|e| RpcError {
			code: ErrorCode::ServerError(Error::DecodeError.into()),
			message: "Unable to query fee details.".into(),
			data: Some(format!("{:?}", e).into()),
		})?;
		let fee_details = api.query_fee_details(&at, uxt, encoded_len).map_err(|e| RpcError {
			code: ErrorCode::ServerError(Error::RuntimeError.into()),
			message: "Unable to query fee details.".into(),
			data: Some(format!("{:?}", e).into()),
		})?;

		let try_into_rpc_balance = |value: Balance| value.try_into().map_err(|_| RpcError {
			code: ErrorCode::InvalidParams,
			message: format!("{} doesn't fit in NumberOrHex representation", value),
			data: None,
		});

		Ok(FeeDetails {
			inclusion_fee: if let Some(inclusion_fee) = fee_details.inclusion_fee {
				Some(InclusionFee {
					base_fee: try_into_rpc_balance(inclusion_fee.base_fee)?,
					len_fee: try_into_rpc_balance(inclusion_fee.len_fee)?,
					adjusted_weight_fee: try_into_rpc_balance(inclusion_fee.adjusted_weight_fee)?,
				})
			} else {
				None
			},
			tip: Default::default(),
		})
	}
}
