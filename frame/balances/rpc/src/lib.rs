// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

//! Node-specific RPC methods for interaction with Balances pallet.

pub use self::gen_client::Client as BalancesClient;
use jsonrpc_core::{Error as RpcError, ErrorCode, Result};
use jsonrpc_derive::rpc;
use pallet_balances::pallet::Config;
pub use pallet_balances_runtime_api::BalancesApi as BalancesRuntimeApi;
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, MaybeDisplay}
};
use std::sync::Arc;

/// Balances RPC methods.
#[rpc]
pub trait BalancesApi<BlockHash, T> where T: Config {
    #[rpc(name="balances_freeBalance")]
    fn free_balance(&self, who: T::AccountId, at: Option<BlockHash>) -> Result<T::Balance>;
}

/// A struct that implements the ['BalancesApi'].
pub struct Balances<C, P> {
    client: Arc<C>,
    _marker: std::marker::PhantomData<P>,
}

impl<C, P> Balances<C, P> {
    /// Create new `Balances` with the given reference to the client.
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

impl<C, Block, T> BalancesApi<<Block as BlockT>::Hash, T>
    for Balances<C, Block>
where
    Block: BlockT,
    C: 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
    C::Api: BalancesRuntimeApi<Block, T>,
    T: Config,
{
    fn free_balance(
        &self,
        who: T::AccountId,
		at: Option<<Block as BlockT>::Hash>,
    ) -> Result<T::Balance> {
        let api = self.client.runtime_api();

		let at = BlockId::hash(at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash));

		api.free_balance(&at, who).map_err(|e| RpcError {
			code: ErrorCode::ServerError(Error::RuntimeError.into()),
			message: "Unable to query dispatch info.".into(),
			data: Some(format!("{:?}", e).into()),
		})
    }
}