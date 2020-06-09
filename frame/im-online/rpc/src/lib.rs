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

//! RPC interface for the im-online module.

use std::sync::Arc;
use codec::{Codec, Decode};
use jsonrpc_core::{Error as RpcError, ErrorCode, Result};
use jsonrpc_derive::rpc;
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_runtime::{generic::BlockId, traits::Block as BlockT};
pub use pallet_im_online_rpc_runtime_api::ImOnlineApi as ImOnlineRuntimeApi;
pub use pallet_im_online::AuthIndex;

#[rpc]
pub trait ImOnlineApi<BlockHash> {
        #[rpc(name = "im_online_isOnline")]
        fn is_online(&self, at: Option<BlockHash>, authority_index: AuthIndex) -> Result<bool>;
}

/// A struct that implements the [`ImOnlineApi`].
pub struct ImOnline<C, P> {
        client: Arc<C>,
        _marker: std::marker::PhantomData<P>
}

impl<C, M> ImOnline<C, M> {
        /// Create new `ImOnline` with the given reference to the client.
        pub fn new(client: Arc<C>) -> Self {
                ImOnline { client, _marker: Default::default() }
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

impl<C, Block> ImOnlineApi<<Block as BlockT>::Hash> for ImOnline<C, Block>
where
	Block: BlockT,
	C: Send + Sync + 'static,
	C: ProvideRuntimeApi<Block>,
	C: HeaderBackend<Block>,
	C::Api: ImOnlineRuntimeApi<Block>,
{
	fn is_online(
                &self, 
                at: Option<<Block as BlockT>::Hash>,
                authority_index: AuthIndex, 
        ) -> Result<bool> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash));

		let runtime_api_result = api.is_online(&at, authority_index);
		runtime_api_result.map_err(|e| RpcError {
			code: ErrorCode::ServerError(9876), // No real reason for this value
			message: "Something wrong".into(),
			data: Some(format!("{:?}", e).into()),
		})
	}
}
