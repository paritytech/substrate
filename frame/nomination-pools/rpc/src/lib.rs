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

pub use self::gen_client::Client as NominationPoolsClient;
use codec::Codec;
use jsonrpc_derive::rpc;
pub use pallet_nomination_pools_rpc_runtime_api::NominationPoolsApi as NominationPoolsRuntimeApi;
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_runtime::{generic::BlockId, traits::Block as BlockT};
use std::sync::Arc;

#[rpc]
pub trait NominationPoolsRpc<BlockHash, AccountId, ResponseType> {
	#[rpc(name = "nompools_pending_rewards")]
	fn pending_rewards(&self, member: AccountId, at: Option<BlockHash>)
		-> Result<ResponseType, ()>;
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

impl<C, Block, AccountId, Balance>
	NominationPoolsRpc<<Block as BlockT>::Hash, AccountId, MemberStatus<Balance>>
	for NominationPoolsRpcType<C, Block>
where
	Block: BlockT,
	C: 'static + ProvideRuntimeApi<Block> + HeaderBackend<Block>,
	C::Api: NominationPoolsRuntimeApi<Block, AccountId, Balance>,
	AccountId: Codec,
	Balance: Codec,
{
	fn pending_rewards(&self, member: AccountId, at: Option<Block::Hash>) -> Result<Balance, ()> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(at.unwrap_or_else(|| self.client.info().best_hash));

		api.pending_rewards(&at, member).map_err(|_| ())
	}
}
