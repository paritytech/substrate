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

//! RPC interface for the transaction payment module.

pub use self::gen_client::Client as TransactionPaymentClient;
use codec::{Codec, Decode};
use jsonrpc_core::{Error as RpcError, ErrorCode, Result};
use jsonrpc_derive::rpc;
use pallet_transaction_payment_rpc_runtime_api::RuntimeDispatchInfo;
pub use pallet_transaction_payment_rpc_runtime_api::TransactionPaymentApi as TransactionPaymentRuntimeApi;
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_core::Bytes;
use sp_runtime::{
    generic::BlockId,
    traits::{Block as BlockT, MaybeDisplay, MaybeFromStr},
};
use std::sync::Arc;

#[rpc]
pub trait TransactionPaymentApi<BlockHash, ResponseType> {
    #[rpc(name = "payment_queryInfo")]
    fn query_info(&self, encoded_xt: Bytes, at: Option<BlockHash>) -> Result<ResponseType>;
}

/// A struct that implements the [`TransactionPaymentApi`].
pub struct TransactionPayment<C, P> {
    client: Arc<C>,
    _marker: std::marker::PhantomData<P>,
}

impl<C, P> TransactionPayment<C, P> {
    /// Create new `TransactionPayment` with the given reference to the client.
    pub fn new(client: Arc<C>) -> Self {
        TransactionPayment {
            client,
            _marker: Default::default(),
        }
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

impl<C, Block, Balance, Extrinsic>
    TransactionPaymentApi<<Block as BlockT>::Hash, RuntimeDispatchInfo<Balance>>
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
        at: Option<<Block as BlockT>::Hash>,
    ) -> Result<RuntimeDispatchInfo<Balance>> {
        let api = self.client.runtime_api();
        let at = BlockId::hash(at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash));

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
