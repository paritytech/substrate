// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! RPC interface for the nomination-pools pallet.
//! Currently supports only one rpc endpoint.

use codec::Codec;
use jsonrpsee::{
	core::{async_trait, RpcResult},
	proc_macros::rpc,
};
pub use pallet_nomination_pools_rpc_runtime_api::NominationPoolsApi as NominationPoolsRuntimeApi;
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_runtime::{generic::BlockId, traits::Block as BlockT};
use std::sync::Arc;

#[rpc(client, server)]
pub trait NominationPoolsRpc<BlockHash, AccountId, ResponseType> {
	#[method(name = "nominationPools_pending_rewards")]
	fn pending_rewards(&self, member: AccountId, at: Option<BlockHash>) -> RpcResult<ResponseType>;
}

pub struct NominationPoolsRpcType<C, P> {
	client: Arc<C>,
	_marker: std::marker::PhantomData<P>,
}

impl<C, P> NominationPoolsRpcType<C, P> {
	pub fn new(client: Arc<C>) -> Self {
		Self { client, _marker: Default::default() }
	}
}

#[async_trait]
impl<C, Block, AccountId, Balance>
	NominationPoolsRpcServer<<Block as BlockT>::Hash, AccountId, Balance>
	for NominationPoolsRpcType<C, Block>
where
	Block: BlockT,
	C: 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
	C::Api: NominationPoolsRuntimeApi<Block, AccountId, Balance>,
	AccountId: Codec,
	Balance: Codec + Default,
{
	fn pending_rewards(&self, member: AccountId, at: Option<Block::Hash>) -> RpcResult<Balance> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(|| self.client.info().best_hash));

		Ok(api.pending_rewards(&at, member).unwrap_or_default())
	}
}
