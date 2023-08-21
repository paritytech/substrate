// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! # Shared JSON-RPC client related code and abstractions.
//!
//! It exposes a `WebSocket JSON-RPC` client that implements the RPC interface in [`sc-rpc-api`]
//! along with some abstractions.
//!
//! ## Usage
//!
//! ```no_run
//! # use substrate_rpc_client::{ws_client, StateApi};
//! # use sp_core::{H256, storage::StorageKey};
//!
//! #[tokio::main]
//! async fn main() {
//!
//!     let client = ws_client("ws://127.0.0.1:9944").await.unwrap();
//!     client.storage(StorageKey(vec![]), Some(H256::zero())).await.unwrap();
//!
//!     // if all type params are not known you need to provide type params
//!     StateApi::<H256>::storage(&client, StorageKey(vec![]), None).await.unwrap();
//! }
//! ```

use async_trait::async_trait;
use serde::de::DeserializeOwned;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use std::collections::VecDeque;

pub use jsonrpsee::{
	core::{
		client::{ClientT, Subscription, SubscriptionClientT},
		params::BatchRequestBuilder,
		Error, RpcResult,
	},
	rpc_params,
	ws_client::{WsClient, WsClientBuilder},
};
pub use sc_rpc_api::{
	author::AuthorApiClient as AuthorApi, chain::ChainApiClient as ChainApi,
	child_state::ChildStateApiClient as ChildStateApi, dev::DevApiClient as DevApi,
	offchain::OffchainApiClient as OffchainApi, state::StateApiClient as StateApi,
	system::SystemApiClient as SystemApi,
};

/// Create a new `WebSocket` connection with shared settings.
pub async fn ws_client(uri: impl AsRef<str>) -> Result<WsClient, String> {
	WsClientBuilder::default()
		.max_request_size(u32::MAX)
		.max_response_size(u32::MAX)
		.request_timeout(std::time::Duration::from_secs(60 * 10))
		.connection_timeout(std::time::Duration::from_secs(60))
		.max_buffer_capacity_per_subscription(1024)
		.build(uri)
		.await
		.map_err(|e| format!("`WsClientBuilder` failed to build: {:?}", e))
}

/// Abstraction over RPC calling for headers.
#[async_trait]
pub trait HeaderProvider<Block: BlockT>
where
	Block::Header: HeaderT,
{
	/// Awaits for the header of the block with hash `hash`.
	async fn get_header(&self, hash: Block::Hash) -> Block::Header;
}

#[async_trait]
impl<Block: BlockT> HeaderProvider<Block> for WsClient
where
	Block::Header: DeserializeOwned,
{
	async fn get_header(&self, hash: Block::Hash) -> Block::Header {
		ChainApi::<(), Block::Hash, Block::Header, ()>::header(self, Some(hash))
			.await
			.unwrap()
			.unwrap()
	}
}

/// Abstraction over RPC subscription for finalized headers.
#[async_trait]
pub trait HeaderSubscription<Block: BlockT>
where
	Block::Header: HeaderT,
{
	/// Await for the next finalized header from the subscription.
	///
	/// Returns `None` if either the subscription has been closed or there was an error when reading
	/// an object from the client.
	async fn next_header(&mut self) -> Option<Block::Header>;
}

#[async_trait]
impl<Block: BlockT> HeaderSubscription<Block> for Subscription<Block::Header>
where
	Block::Header: DeserializeOwned,
{
	async fn next_header(&mut self) -> Option<Block::Header> {
		match self.next().await {
			Some(Ok(header)) => Some(header),
			None => {
				log::warn!("subscription closed");
				None
			},
			Some(Err(why)) => {
				log::warn!("subscription returned error: {:?}. Probably decoding has failed.", why);
				None
			},
		}
	}
}

/// Stream of all finalized headers.
///
/// Returned headers are guaranteed to be ordered. There are no missing headers (even if some of
/// them lack justification).
pub struct FinalizedHeaders<
	'a,
	Block: BlockT,
	HP: HeaderProvider<Block>,
	HS: HeaderSubscription<Block>,
> {
	header_provider: &'a HP,
	subscription: HS,
	fetched_headers: VecDeque<Block::Header>,
	last_returned: Option<<Block::Header as HeaderT>::Hash>,
}

impl<'a, Block: BlockT, HP: HeaderProvider<Block>, HS: HeaderSubscription<Block>>
	FinalizedHeaders<'a, Block, HP, HS>
where
	<Block as BlockT>::Header: DeserializeOwned,
{
	pub fn new(header_provider: &'a HP, subscription: HS) -> Self {
		Self {
			header_provider,
			subscription,
			fetched_headers: VecDeque::new(),
			last_returned: None,
		}
	}

	/// Reads next finalized header from the subscription. If some headers (without justification)
	/// have been skipped, fetches them as well. Returns number of headers that have been fetched.
	///
	/// All fetched headers are stored in `self.fetched_headers`.
	async fn fetch(&mut self) -> usize {
		let last_finalized = match self.subscription.next_header().await {
			Some(header) => header,
			None => return 0,
		};

		self.fetched_headers.push_front(last_finalized.clone());

		let mut last_finalized_parent = *last_finalized.parent_hash();
		let last_returned = self.last_returned.unwrap_or(last_finalized_parent);

		while last_finalized_parent != last_returned {
			let parent_header = self.header_provider.get_header(last_finalized_parent).await;
			self.fetched_headers.push_front(parent_header.clone());
			last_finalized_parent = *parent_header.parent_hash();
		}

		self.fetched_headers.len()
	}

	/// Get the next finalized header.
	pub async fn next(&mut self) -> Option<Block::Header> {
		if self.fetched_headers.is_empty() {
			self.fetch().await;
		}

		if let Some(header) = self.fetched_headers.pop_front() {
			self.last_returned = Some(header.hash());
			Some(header)
		} else {
			None
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_runtime::testing::{Block as TBlock, ExtrinsicWrapper, Header, H256};
	use std::sync::Arc;
	use tokio::sync::Mutex;

	type Block = TBlock<ExtrinsicWrapper<()>>;
	type BlockNumber = u64;
	type Hash = H256;

	struct MockHeaderProvider(pub Arc<Mutex<VecDeque<BlockNumber>>>);

	fn headers() -> Vec<Header> {
		let mut headers = vec![Header::new_from_number(0)];
		for n in 1..11 {
			headers.push(Header {
				parent_hash: headers.last().unwrap().hash(),
				..Header::new_from_number(n)
			})
		}
		headers
	}

	#[async_trait]
	impl HeaderProvider<Block> for MockHeaderProvider {
		async fn get_header(&self, _hash: Hash) -> Header {
			let height = self.0.lock().await.pop_front().unwrap();
			headers()[height as usize].clone()
		}
	}

	struct MockHeaderSubscription(pub VecDeque<BlockNumber>);

	#[async_trait]
	impl HeaderSubscription<Block> for MockHeaderSubscription {
		async fn next_header(&mut self) -> Option<Header> {
			self.0.pop_front().map(|h| headers()[h as usize].clone())
		}
	}

	#[tokio::test]
	async fn finalized_headers_works_when_every_block_comes_from_subscription() {
		let heights = vec![4, 5, 6, 7];

		let provider = MockHeaderProvider(Default::default());
		let subscription = MockHeaderSubscription(heights.clone().into());
		let mut headers = FinalizedHeaders::new(&provider, subscription);

		for h in heights {
			assert_eq!(h, headers.next().await.unwrap().number);
		}
		assert_eq!(None, headers.next().await);
	}

	#[tokio::test]
	async fn finalized_headers_come_from_subscription_and_provider_if_in_need() {
		let all_heights = 3..11;
		let heights_in_subscription = vec![3, 4, 6, 10];
		// Consecutive headers will be requested in the reversed order.
		let heights_not_in_subscription = vec![5, 9, 8, 7];

		let provider = MockHeaderProvider(Arc::new(Mutex::new(heights_not_in_subscription.into())));
		let subscription = MockHeaderSubscription(heights_in_subscription.into());
		let mut headers = FinalizedHeaders::new(&provider, subscription);

		for h in all_heights {
			assert_eq!(h, headers.next().await.unwrap().number);
		}
		assert_eq!(None, headers.next().await);
	}
}
