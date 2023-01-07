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

//! RPC interface for the staking pallet.

use std::sync::Arc;

use codec::Codec;
use jsonrpsee::{
	core::RpcResult,
	proc_macros::rpc,
	types::error::{CallError, ErrorObject},
};
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_rpc::number::NumberOrHex;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, MaybeDisplay},
};

pub use pallet_staking_rpc_runtime_api::StakingApi as StakingRuntimeApi;

#[rpc(client, server)]
pub trait StakingApi<Balance> {
	#[method(name = "staking_nominationsQuota")]
	fn query_nominations_quota(&self) -> RpcResult<u32>;
    #[method(name = "nominationPools_pointsToBalance")]
	fn query_points_to_balance(&self, pool_id: u32) -> RpcResult<u32>;
}

pub struct Staking<C, P> {
	client: Arc<C>,
	_marker: std::marker::PhantomData<P>,
}

impl<C, P> Staking<C, P> {
	pub fn new(client: Arc<C>) -> Self {
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

impl<C, Block, Balance> StakingApiServer<Balance> for Staking<C, Block>
where
	Block: BlockT,
	C: ProvideRuntimeApi<Block> + HeaderBackend<Block> + Send + Sync + 'static,
	C::Api: StakingRuntimeApi<Block, Balance>,
	Balance: Codec + MaybeDisplay + Copy + TryInto<NumberOrHex> + Send + Sync + 'static,
{
	fn query_nominations_quota(&self) -> RpcResult<u32> {
		let api = self.client.runtime_api();
		let at = BlockId::hash(self.client.info().best_hash);

		let runtime_api_result = api.query_nominations_quota(&at);

		Ok(runtime_api_result.map_err(|e| {
			CallError::Custom(ErrorObject::owned(
				Error::RuntimeError.into(),
				"Unable to query the nominations quota.",
				Some(e.to_string()),
			))
		})?)
	}

    fn query_points_to_balance(&self, pool_id: u32) -> RpcResult<u32> {
        let api = self.client.runtime_api();
		let at = BlockId::hash(self.client.info().best_hash);

		let runtime_api_result = api.query_points_to_balance(&at, pool_id);

	    runtime_api_result.map_err(|e| {
			CallError::Custom(ErrorObject::owned(
				Error::RuntimeError.into(),
				"Unable to query the points to balance conversion for pool.",
				Some(e.to_string()),
			))
		})?
    }
}
