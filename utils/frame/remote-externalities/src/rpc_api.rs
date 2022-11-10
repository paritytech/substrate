// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! WS RPC API for one off RPC calls to a substrate node.
// TODO: Consolidate one off RPC calls https://github.com/paritytech/substrate/issues/8988

use jsonrpsee::{
	core::client::{Client, ClientT},
	rpc_params,
	types::ParamsSer,
	ws_client::{WsClient, WsClientBuilder},
};
use serde::de::DeserializeOwned;
use sp_runtime::{generic::SignedBlock, traits::Block as BlockT};
use std::sync::Arc;

enum RpcCall {
	GetHeader,
	GetFinalizedHead,
	GetBlock,
	GetRuntimeVersion,
}

impl RpcCall {
	fn as_str(&self) -> &'static str {
		match self {
			RpcCall::GetHeader => "chain_getHeader",
			RpcCall::GetFinalizedHead => "chain_getFinalizedHead",
			RpcCall::GetBlock => "chain_getBlock",
			RpcCall::GetRuntimeVersion => "state_getRuntimeVersion",
		}
	}
}

/// General purpose method for making RPC calls.
async fn make_request<'a, T: DeserializeOwned>(
	client: &Arc<Client>,
	call: RpcCall,
	params: Option<ParamsSer<'a>>,
) -> Result<T, String> {
	client
		.request::<T>(call.as_str(), params)
		.await
		.map_err(|e| format!("{} request failed: {:?}", call.as_str(), e))
}

enum ConnectionPolicy {
	Reuse(Arc<Client>),
	Reconnect,
}

/// Simple RPC service that is capable of keeping the connection.
///
/// Service will connect to `uri` for the first time already during initialization.
///
/// Be careful with reusing the connection in a multithreaded environment.
pub struct RpcService {
	uri: String,
	policy: ConnectionPolicy,
}

impl RpcService {
	/// Creates a new RPC service. If `keep_connection`, then connects to `uri` right away.
	pub async fn new<S: AsRef<str>>(uri: S, keep_connection: bool) -> Result<Self, String> {
		let policy = if keep_connection {
			ConnectionPolicy::Reuse(Arc::new(Self::build_client(uri.as_ref()).await?))
		} else {
			ConnectionPolicy::Reconnect
		};
		Ok(Self { uri: uri.as_ref().to_string(), policy })
	}

	/// Returns the address at which requests are sent.
	pub fn uri(&self) -> String {
		self.uri.clone()
	}

	/// Build a websocket client that connects to `self.uri`.
	async fn build_client<S: AsRef<str>>(uri: S) -> Result<WsClient, String> {
		WsClientBuilder::default()
			.max_request_body_size(u32::MAX)
			.build(uri)
			.await
			.map_err(|e| format!("`WsClientBuilder` failed to build: {:?}", e))
	}

	/// Generic method for making RPC requests.
	async fn make_request<'a, T: DeserializeOwned>(
		&self,
		call: RpcCall,
		params: Option<ParamsSer<'a>>,
	) -> Result<T, String> {
		match self.policy {
			// `self.keep_connection` must have been `true`.
			ConnectionPolicy::Reuse(ref client) => make_request(client, call, params).await,
			ConnectionPolicy::Reconnect => {
				let client = Arc::new(Self::build_client(&self.uri).await?);
				make_request(&client, call, params).await
			},
		}
	}

	/// Get the header of the block identified by `at`.
	pub async fn get_header<Block>(&self, at: Block::Hash) -> Result<Block::Header, String>
	where
		Block: BlockT,
		Block::Header: DeserializeOwned,
	{
		self.make_request(RpcCall::GetHeader, rpc_params!(at)).await
	}

	/// Get the finalized head.
	pub async fn get_finalized_head<Block: BlockT>(&self) -> Result<Block::Hash, String> {
		self.make_request(RpcCall::GetFinalizedHead, None).await
	}

	/// Get the signed block identified by `at`.
	pub async fn get_block<Block: BlockT + DeserializeOwned>(
		&self,
		at: Block::Hash,
	) -> Result<Block, String> {
		Ok(self
			.make_request::<SignedBlock<Block>>(RpcCall::GetBlock, rpc_params!(at))
			.await?
			.block)
	}

	/// Get the runtime version of a given chain.
	pub async fn get_runtime_version<Block: BlockT + DeserializeOwned>(
		&self,
		at: Option<Block::Hash>,
	) -> Result<sp_version::RuntimeVersion, String> {
		self.make_request(RpcCall::GetRuntimeVersion, rpc_params!(at)).await
	}
}
