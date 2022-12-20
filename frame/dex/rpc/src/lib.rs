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

//! RPC interface for the transaction payment pallet.

use std::{marker::PhantomData, sync::Arc};

use codec::Codec;
use jsonrpsee::{
	core::RpcResult,
	proc_macros::rpc,
	types::error::{CallError, ErrorObject},
};
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, MaybeDisplay},
};

pub use pallet_dex_rpc_runtime_api::DexApi as DexRuntimeApi;

#[rpc(client, server)]
pub trait DexApi<Balance>
where
	Balance: Copy,
{
	#[method(name = "dex_quotePrice")]
	fn quote_price(
		&self,
		asset1: Option<u32>,
		asset2: Option<u32>,
		amount: u64,
	) -> RpcResult<Option<Balance>>;
}

/// Dex RPC methods.
pub struct Dex<Client, Block> {
	client: Arc<Client>,
	_marker: PhantomData<Block>,
}

impl<Client, Block> Dex<Client, Block> {
	/// Creates a new instance of the DEX RPC helper.
	pub fn new(client: Arc<Client>) -> Self {
		Self { client, _marker: Default::default() }
	}
}

/// Error type of this RPC api.
pub enum Error {
	/// The call to runtime failed.
	RuntimeError,
}

impl From<Error> for i32 {
	fn from(e: Error) -> i32 {
		match e {
			Error::RuntimeError => 1,
		}
	}
}

impl<Client, Block, Balance> DexApiServer<Balance> for Dex<Client, Block>
where
	Block: BlockT,
	Client: ProvideRuntimeApi<Block> + HeaderBackend<Block> + Send + Sync + 'static,
	Client::Api: DexRuntimeApi<Block, Balance>,
	Balance: Codec + MaybeDisplay + Copy,
{
	fn quote_price(
		&self,
		asset1: Option<u32>,
		asset2: Option<u32>,
		amount: u64,
	) -> RpcResult<Option<Balance>> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(self.client.info().best_hash);

		api.quote_price(&at, asset1, asset2, amount).map_err(|e| {
			CallError::Custom(ErrorObject::owned(
				Error::RuntimeError.into(),
				"Unable to query price info.",
				Some(e.to_string()),
			))
			.into()
		})
	}
}
