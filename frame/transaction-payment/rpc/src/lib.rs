// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use codec::{Codec, Decode};
use jsonrpsee::{
	proc_macros::rpc,
	types::error::{ErrorObject, ErrorObjectOwned},
};
use pallet_transaction_payment_rpc_runtime_api::{FeeDetails, InclusionFee, RuntimeDispatchInfo};
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_core::Bytes;
use sp_rpc::number::NumberOrHex;
use sp_runtime::traits::{Block as BlockT, MaybeDisplay};

pub use pallet_transaction_payment_rpc_runtime_api::TransactionPaymentApi as TransactionPaymentRuntimeApi;

#[rpc(client, server)]
pub trait TransactionPaymentApi<BlockHash, ResponseType> {
	#[method(name = "payment_queryInfo")]
	fn query_info(&self, encoded_xt: Bytes, at: Option<BlockHash>) -> Result<ResponseType, Error>;

	#[method(name = "payment_queryFeeDetails")]
	fn query_fee_details(
		&self,
		encoded_xt: Bytes,
		at: Option<BlockHash>,
	) -> Result<FeeDetails<NumberOrHex>, Error>;
}

/// Provides RPC methods to query a dispatchable's class, weight and fee.
pub struct TransactionPayment<C, P> {
	/// Shared reference to the client.
	client: Arc<C>,
	_marker: std::marker::PhantomData<P>,
}

impl<C, P> TransactionPayment<C, P> {
	/// Creates a new instance of the TransactionPayment Rpc helper.
	pub fn new(client: Arc<C>) -> Self {
		Self { client, _marker: Default::default() }
	}
}

/// Error type of this RPC api.
pub enum Error {
	/// The transaction was not decodable.
	DecodeError { msg: String, err: codec::Error },
	/// The call to runtime failed.
	RuntimeError { msg: String, err: sp_api::ApiError },
	/// Balance too large
	BalanceTooLarge(String),
}

impl From<Error> for ErrorObjectOwned {
	fn from(err: Error) -> Self {
		match err {
			Error::RuntimeError { msg, err } =>
				ErrorObject::owned(1, msg, Some(format!("{:?}", err))),
			Error::DecodeError { msg, err } =>
				ErrorObject::owned(2, msg, Some(format!("{:?}", err))),
			Error::BalanceTooLarge(msg) => ErrorObject::owned(3, msg, None::<()>),
		}
	}
}

impl<C, Block, Balance>
	TransactionPaymentApiServer<
		<Block as BlockT>::Hash,
		RuntimeDispatchInfo<Balance, sp_weights::Weight>,
	> for TransactionPayment<C, Block>
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
	) -> Result<RuntimeDispatchInfo<Balance, sp_weights::Weight>, Error> {
		let api = self.client.runtime_api();
		let at_hash = at.unwrap_or_else(|| self.client.info().best_hash);

		let encoded_len = encoded_xt.len() as u32;

		let uxt: Block::Extrinsic = Decode::decode(&mut &*encoded_xt).map_err(|e| {
			Error::DecodeError { msg: "Unable to query dispatch info.".to_string(), err: e }
		})?;

		let res = api.query_info(at_hash, uxt, encoded_len).map_err(|e| Error::RuntimeError {
			msg: "Unable to query dispatch info.".to_string(),
			err: e,
		})?;

		Ok(RuntimeDispatchInfo {
			weight: res.weight,
			class: res.class,
			partial_fee: res.partial_fee,
		})
	}

	fn query_fee_details(
		&self,
		encoded_xt: Bytes,
		at: Option<Block::Hash>,
	) -> Result<FeeDetails<NumberOrHex>, Error> {
		let api = self.client.runtime_api();
		let at_hash = at.unwrap_or_else(|| self.client.info().best_hash);

		let encoded_len = encoded_xt.len() as u32;

		let uxt: Block::Extrinsic = Decode::decode(&mut &*encoded_xt).map_err(|e| {
			Error::DecodeError { msg: "Unable to query fee details.".to_string(), err: e }
		})?;
		let fee_details =
			api.query_fee_details(at_hash, uxt, encoded_len)
				.map_err(|e| Error::RuntimeError {
					msg: "Unable to query fee details.".to_string(),
					err: e,
				})?;

		let try_into_rpc_balance = |value: Balance| {
			value.try_into().map_err(|_| {
				Error::BalanceTooLarge(format!(
					"{} doesn't fit in NumberOrHex representation",
					value
				))
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
