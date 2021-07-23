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

//! WS RPC API for one off RPC calls to a substrate node.
// TODO: Consolidate one off RPC calls https://github.com/paritytech/substrate/issues/8988

use jsonrpsee_ws_client::{
	types::{traits::Client, v2::params::JsonRpcParams},
	WsClient, WsClientBuilder,
};
use sp_runtime::{
	generic::SignedBlock,
	traits::{Block as BlockT, Header as HeaderT},
};

/// Get the header of the block identified by `at`
pub async fn get_header<Block, S>(from: S, at: Block::Hash) -> Result<Block::Header, String>
where
	Block: BlockT,
	Block::Header: serde::de::DeserializeOwned,
	S: AsRef<str>,
{
	let params = vec![hash_to_json::<Block>(at)?];
	let client = build_client(from).await?;

	client
		.request::<Block::Header>("chain_getHeader", JsonRpcParams::Array(params))
		.await
		.map_err(|e| format!("chain_getHeader request failed: {:?}", e))
}

/// Get the finalized head
pub async fn get_finalized_head<Block, S>(from: S) -> Result<Block::Hash, String>
where
	Block: BlockT,
	S: AsRef<str>,
{
	let client = build_client(from).await?;

	client
		.request::<Block::Hash>("chain_getFinalizedHead", JsonRpcParams::NoParams)
		.await
		.map_err(|e| format!("chain_getFinalizedHead request failed: {:?}", e))
}

/// Get the signed block identified by `at`.
pub async fn get_block<Block, S>(from: S, at: Block::Hash) -> Result<Block, String>
where
	S: AsRef<str>,
	Block: BlockT + serde::de::DeserializeOwned,
	Block::Header: HeaderT,
{
	let params = vec![hash_to_json::<Block>(at)?];
	let client = build_client(from).await?;
	let signed_block = client
		.request::<SignedBlock<Block>>("chain_getBlock", JsonRpcParams::Array(params))
		.await
		.map_err(|e| format!("chain_getBlock request failed: {:?}", e))?;

	Ok(signed_block.block)
}

/// Convert a block hash to a serde json value.
fn hash_to_json<Block: BlockT>(hash: Block::Hash) -> Result<serde_json::Value, String> {
	serde_json::to_value(hash)
		.map_err(|e| format!("Block hash could not be converted to JSON: {:?}", e))
}

/// Build a website client that connects to `from`.
async fn build_client<S: AsRef<str>>(from: S) -> Result<WsClient, String> {
	WsClientBuilder::default()
		.max_request_body_size(u32::MAX)
		.build(from.as_ref())
		.await
		.map_err(|e| format!("`WsClientBuilder` failed to build: {:?}", e))
}
