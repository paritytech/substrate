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

//! RPC interface for the transaction payment module.

use std::sync::Arc;
use codec::{Codec, Decode};
use sp_blockchain::HeaderBackend;
use jsonrpc_core::{Error as RpcError, ErrorCode, Result};
use jsonrpc_derive::rpc;
use sp_runtime::{generic::BlockId, traits::{Block as BlockT, MaybeDisplay, MaybeFromStr}};
use sp_api::ProvideRuntimeApi;
use sp_core::Bytes;
use pallet_transaction_payment_rpc_runtime_api::RuntimeDispatchInfo;
pub use pallet_transaction_payment_rpc_runtime_api::TransactionPaymentApi as TransactionPaymentRuntimeApi;
pub use self::gen_client::Client as TransactionPaymentClient;

#[rpc]
pub trait TransactionPaymentApi<BlockHash, ResponseType> {
	#[rpc(name = "payment_queryInfo")]
	fn query_info(
		&self,
		encoded_xt: Bytes,
		at: Option<BlockHash>
	) -> Result<ResponseType>;
}

/// A struct that implements the [`TransactionPaymentApi`].
pub struct TransactionPayment<C, P> {
	client: Arc<C>,
	_marker: std::marker::PhantomData<P>,
}

impl<C, P> TransactionPayment<C, P> {
	/// Create new `TransactionPayment` with the given reference to the client.
	pub fn new(client: Arc<C>) -> Self {
		TransactionPayment { client, _marker: Default::default() }
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

impl<C, Block, Balance, Extrinsic> TransactionPaymentApi<<Block as BlockT>::Hash, RuntimeDispatchInfo<Balance>>
	for TransactionPayment<C, (Block, Extrinsic)>
where
	Block: BlockT,
	C: Send + Sync + 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
	C::Api: TransactionPaymentRuntimeApi<Block, Balance, Extrinsic>,
	Balance: Codec + MaybeDisplay + MaybeFromStr,
	Extrinsic: Codec + Send + Sync + 'static,
{
	fn query_info(
		&self,
		encoded_xt: Bytes,
		at: Option<<Block as BlockT>::Hash>
	) -> Result<RuntimeDispatchInfo<Balance>> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash
		));

		let encoded_len = encoded_xt.len() as u32;

		let uxt: Extrinsic = Decode::decode(&mut &*encoded_xt).map_err(|e| RpcError {
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
}
