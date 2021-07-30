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
pub use pallet_balances_rpc_runtime_api::BalancesApi as BalancesRuntimeApi;

use core::{fmt, str::FromStr};
use codec::Codec;
use jsonrpc_core::{Error as RpcError, ErrorCode, Result};
use jsonrpc_derive::rpc;
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, MaybeDisplay, MaybeFromStr},
};
use std::sync::Arc;
use pallet_balances_rpc_runtime_api::SerdeWrapper;

/// Balances RPC methods.
#[rpc]
pub trait BalancesApi<BlockHash, AccountId, Balance>
where
	Balance: FromStr + fmt::Display
{
    #[rpc(name="balances_freeBalance")]
    fn free_balance(
		&self,
		who: AccountId,
		at: Option<BlockHash>
	) -> Result<SerdeWrapper<Balance>>;
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
	/// The call to runtime failed.
	RuntimeError,
}

impl From<Error> for i64 {
	fn from(e: Error) -> i64 {
		match e {
			Error::RuntimeError => 1,
		}
	}
}

impl<C, Block, AccountId, Balance>
	BalancesApi<
		<Block as BlockT>::Hash,
		AccountId,
		Balance,
    > for Balances<C, Block>
where
    Block: BlockT,
    C: 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
    C::Api: BalancesRuntimeApi<Block, AccountId, Balance>,
    AccountId: Codec,
	Balance: Codec + MaybeDisplay + MaybeFromStr,
{
    fn free_balance(
        &self,
        who: AccountId,
		at: Option<<Block as BlockT>::Hash>,
    ) -> Result<SerdeWrapper<Balance>> {
        let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(||
			// If the block hash is not supplied assume the best block.
			self.client.info().best_hash));

		api.free_balance(&at, who).map_err(|e| RpcError {
			code: ErrorCode::ServerError(Error::RuntimeError.into()),
			message: "Unable to query balances info.".into(),
			data: Some(format!("{:?}", e).into()),
		})
    }
}