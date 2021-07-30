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

//! RPC interface for the transaction payment pallet.

pub use self::gen_client::Client as TransactionPaymentClient;
use codec::{Codec, Decode};
use jsonrpc_core::{Error as RpcError, ErrorCode, Result};
use jsonrpc_derive::rpc;
pub use pallet_transaction_payment_rpc_runtime_api::TransactionPaymentApi as TransactionPaymentRuntimeApi;
use pallet_transaction_payment_rpc_runtime_api::{FeeDetails, InclusionFee, RuntimeDispatchInfo};
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_core::Bytes;
use sp_rpc::number::NumberOrHex;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, MaybeDisplay},
};
use std::{convert::TryInto, sync::Arc};

#[rpc]
pub trait TransactionPaymentApi<BlockHash, ResponseType> {
	#[rpc(name = "payment_queryInfo")]
	fn query_info(&self, encoded_xt: Bytes, at: Option<BlockHash>) -> Result<ResponseType>;
	#[rpc(name = "payment_queryFeeDetails")]
	fn query_fee_details(
		&self,
		encoded_xt: Bytes,
		at: Option<BlockHash>,
	) -> Result<FeeDetails<NumberOrHex>>;
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

/// Error type of this RPC api.
pub enum Error {
	/// The transaction was not decodable.
	DecodeError,
	/// The call to runtime failed.
	RuntimeError,
}

impl From<Error> for i64 {
	fn from(e: Error) -> i64 {
		match e {
			Error::RuntimeError => 1,
			Error::DecodeError => 2,
		}
	}
}

impl<C, Block, Balance> TransactionPaymentApi<<Block as BlockT>::Hash, RuntimeDispatchInfo<Balance>>
	for TransactionPayment<C, Block>
where
	Block: BlockT,
	C: 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
	C::Api: TransactionPaymentRuntimeApi<Block, Balance>,
	Balance: Codec + MaybeDisplay + Copy + TryInto<NumberOrHex>,
{
	fn query_info(
		&self,
		encoded_xt: Bytes,
		at: Option<<Block as BlockT>::Hash>,
	) -> Result<RuntimeDispatchInfo<Balance>> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash));

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
	) -> Result<FeeDetails<NumberOrHex>> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash));

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

		let try_into_rpc_balance = |value: Balance| {
			value.try_into().map_err(|_| RpcError {
				code: ErrorCode::InvalidParams,
				message: format!("{} doesn't fit in NumberOrHex representation", value),
				data: None,
			})
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
	}
}
