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

use std::{convert::TryInto, sync::Arc};

use anyhow::anyhow;
use codec::{Codec, Decode};
use jsonrpsee::{
	proc_macros::rpc,
	types::{
		async_trait,
		error::{CallError, Error as JsonRpseeError},
		JsonRpcResult,
	},
};
use pallet_transaction_payment_rpc_runtime_api::{FeeDetails, InclusionFee, RuntimeDispatchInfo};
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_core::Bytes;
use sp_rpc::number::NumberOrHex;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, MaybeDisplay},
};

pub use pallet_transaction_payment_rpc_runtime_api::TransactionPaymentApi as TransactionPaymentRuntimeApi;

#[rpc(client, server, namespace = "payment")]
pub trait TransactionPaymentApi<BlockHash, ResponseType> {
	#[method(name = "queryInfo")]
	fn query_info(&self, encoded_xt: Bytes, at: Option<BlockHash>) -> JsonRpcResult<ResponseType>;

	#[method(name = "queryFeeDetails")]
	fn query_fee_details(
		&self,
		encoded_xt: Bytes,
		at: Option<BlockHash>,
	) -> JsonRpcResult<FeeDetails<NumberOrHex>>;
}

/// Provides RPC methods to query a dispatchable's class, weight and fee.
pub struct TransactionPaymentRpc<C, Block, Balance> {
	/// Shared reference to the client.
	client: Arc<C>,
	_block_marker: std::marker::PhantomData<Block>,
	_balance_marker: std::marker::PhantomData<Balance>,
}

impl<C, Block, Balance> TransactionPaymentRpc<C, Block, Balance> {
	/// Creates a new instance of the TransactionPaymentRpc helper.
	pub fn new(client: Arc<C>) -> Self {
		Self { client, _block_marker: Default::default(), _balance_marker: Default::default() }
	}
}

#[async_trait]
impl<C, Block, Balance>
	TransactionPaymentApiServer<<Block as BlockT>::Hash, RuntimeDispatchInfo<Balance>>
	for TransactionPaymentRpc<C, Block, Balance>
where
	Block: BlockT,
	C: ProvideRuntimeApi<Block> + HeaderBackend<Block> + Send + Sync + 'static,
	C::Api: TransactionPaymentRuntimeApi<Block, Balance>,
	Balance: Codec + MaybeDisplay + Copy + TryInto<NumberOrHex> + Send + Sync + 'static,
{
	fn query_info(
		&self,
		encoded_xt: Bytes,
		at: Option<Block::Hash>,
	) -> JsonRpcResult<RuntimeDispatchInfo<Balance>> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(|| self.client.info().best_hash));

		let encoded_len = encoded_xt.len() as u32;

		let uxt: Block::Extrinsic = Decode::decode(&mut &*encoded_xt)
			.map_err(|codec_err| CallError::from_std_error(codec_err))?;
		api.query_info(&at, uxt, encoded_len)
			.map_err(|api_err| JsonRpseeError::to_call_error(api_err))
	}

	fn query_fee_details(
		&self,
		encoded_xt: Bytes,
		at: Option<Block::Hash>,
	) -> JsonRpcResult<FeeDetails<NumberOrHex>> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(|| self.client.info().best_hash));

		let encoded_len = encoded_xt.len() as u32;

		let uxt: Block::Extrinsic = Decode::decode(&mut &*encoded_xt)
			.map_err(|codec_err| CallError::from_std_error(codec_err))?;
		let fee_details = api
			.query_fee_details(&at, uxt, encoded_len)
			.map_err(|api_err| CallError::from_std_error(api_err))?;

		let try_into_rpc_balance = |value: Balance| {
			value
				.try_into()
				.map_err(|_| anyhow!("{} doesn't fit in NumberOrHex representation", value))
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
