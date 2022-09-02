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
use sp_runtime::{
	generic::SignedBlock,
	traits::{Block as BlockT, Header as HeaderT},
};

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
	client: &Client,
	call: RpcCall,
	params: Option<ParamsSer<'a>>,
) -> Result<T, String> {
	client
		.request::<T>(call.as_str(), params)
		.await
		.map_err(|e| format!("{} request failed: {:?}", call.as_str(), e))
}

/// Simple RPC service that is capable of keeping the connection.
///
/// Service will connect to `uri` for the first time during the first request. Instantiation
/// does not trigger connecting.
pub struct RpcService {
	uri: String,
	client: Option<Client>,
	keep_connection: bool,
}

impl RpcService {
	/// Creates a new RPC service.
	///
	/// Does not connect yet.
	pub fn new<S: AsRef<str>>(uri: S, keep_connection: bool) -> Self {
		Self { uri: uri.as_ref().to_string(), client: None, keep_connection }
	}

	/// Returns the address at which requests are sent.
	pub fn uri(&self) -> String {
		self.uri.clone()
	}

	/// Whether to keep and reuse a single connection.
	pub fn keep_connection(&self) -> bool {
		self.keep_connection
	}

	/// Build a websocket client that connects to `self.uri`.
	async fn build_client(&self) -> Result<WsClient, String> {
		WsClientBuilder::default()
			.max_request_body_size(u32::MAX)
			.build(&self.uri)
			.await
			.map_err(|e| format!("`WsClientBuilder` failed to build: {:?}", e))
	}

	/// Generic method for making RPC requests.
	async fn make_request<'a, T: DeserializeOwned>(
		&mut self,
		call: RpcCall,
		params: Option<ParamsSer<'a>>,
	) -> Result<T, String> {
		match &self.client {
			// `self.keep_connection` must be `true.
			Some(ref client) => make_request(client, call, params).await,
			None => {
				let client = self.build_client().await?;
				let result = make_request(&client, call, params).await;
				if self.keep_connection {
					self.client = Some(client)
				};
				result
			},
		}
	}

	/// Get the header of the block identified by `at`.
	pub async fn get_header<Block>(&mut self, at: Block::Hash) -> Result<Block::Header, String>
	where
		Block: BlockT,
		Block::Header: DeserializeOwned,
	{
		self.make_request(RpcCall::GetHeader, rpc_params!(at)).await
	}

	/// Get the finalized head.
	pub async fn get_finalized_head<Block: BlockT>(&mut self) -> Result<Block::Hash, String> {
		self.make_request(RpcCall::GetFinalizedHead, None).await
	}

	/// Get the signed block identified by `at`.
	pub async fn get_block<Block: BlockT + DeserializeOwned>(
		&mut self,
		at: Block::Hash,
	) -> Result<Block, String> {
		Ok(self
			.make_request::<SignedBlock<Block>>(RpcCall::GetBlock, rpc_params!(at))
			.await?
			.block)
	}

	/// Get the runtime version of a given chain.
	pub async fn get_runtime_version<Block: BlockT + DeserializeOwned>(
		&mut self,
		at: Option<Block::Hash>,
	) -> Result<sp_version::RuntimeVersion, String> {
		self.make_request(RpcCall::GetRuntimeVersion, rpc_params!(at)).await
	}
}
