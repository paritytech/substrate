// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Substrate blockchain API.

mod chain_full;
mod chain_light;

#[cfg(test)]
mod tests;

use std::sync::Arc;
use futures::{future, StreamExt, TryStreamExt};
use log::warn;
use rpc::{
	Result as RpcResult,
	futures::{stream, Future, Sink, Stream},
};

use sc_client_api::{BlockchainEvents, light::{Fetcher, RemoteBlockchain}};
use jsonrpc_pubsub::{typed::Subscriber, SubscriptionId, manager::SubscriptionManager};
use jsonrpsee_ws_server::{RpcModule, RpcContextModule};
use jsonrpsee_types::error::Error as JsonRpseeError;
use sp_rpc::{number::NumberOrHex, list::ListOrValue};
use sp_runtime::{
	generic::{BlockId, SignedBlock},
	traits::{Block as BlockT, Header, NumberFor},
};

use self::error::Error as StateError;

pub use sc_rpc_api::chain::*;
use sp_blockchain::HeaderBackend;
use sc_client_api::BlockBackend;

/// Blockchain backend API
#[async_trait::async_trait]
trait ChainBackend<Client, Block: BlockT>: Send + Sync + 'static
	where
		Block: BlockT + 'static,
		Client: HeaderBackend<Block> + BlockchainEvents<Block> + 'static,
{
	/// Get client reference.
	fn client(&self) -> &Arc<Client>;

	/// Get subscriptions reference.
	fn subscriptions(&self) -> &SubscriptionManager;

	/// Tries to unwrap passed block hash, or uses best block hash otherwise.
	fn unwrap_or_best(&self, hash: Option<Block::Hash>) -> Block::Hash {
		match hash.into() {
			None => self.client().info().best_hash,
			Some(hash) => hash,
		}
	}

	/// Get header of a relay chain block.
	async fn header(&self, hash: Option<Block::Hash>) -> Result<Option<Block::Header>, StateError>;

	/// Get header and body of a relay chain block.
	async fn block(&self, hash: Option<Block::Hash>)
		-> Result<Option<SignedBlock<Block>>, StateError>;

	/// Get hash of the n-th block in the canon chain.
	///
	/// By default returns latest block hash.
	fn block_hash(&self, number: Option<NumberOrHex>) -> Result<Option<Block::Hash>, StateError> {
		match number {
			None => Ok(Some(self.client().info().best_hash)),
			Some(num_or_hex) => {
				use std::convert::TryInto;

				// FIXME <2329>: Database seems to limit the block number to u32 for no reason
				let block_num: u32 = num_or_hex.try_into().map_err(|_| {
					StateError::from(format!(
						"`{:?}` > u32::max_value(), the max block number is u32.",
						num_or_hex
					))
				})?;
				let block_num = <NumberFor<Block>>::from(block_num);
				Ok(self
					.client()
					.header(BlockId::number(block_num))
					.map_err(client_err)?
					.map(|h| h.hash()))
			}
		}
	}

	/// Get hash of the last finalized block in the canon chain.
	fn finalized_head(&self) -> Result<Block::Hash, StateError> {
		Ok(self.client().info().finalized_hash)
	}

	/// All new head subscription
	fn subscribe_all_heads(
		&self,
		_metadata: crate::Metadata,
		subscriber: Subscriber<Block::Header>,
	) {
		subscribe_headers(
			self.client(),
			self.subscriptions(),
			subscriber,
			|| self.client().info().best_hash,
			|| self.client().import_notification_stream()
				.map(|notification| Ok::<_, ()>(notification.header))
				.compat(),
		)
	}

	/// Unsubscribe from all head subscription.
	fn unsubscribe_all_heads(
		&self,
		_metadata: Option<crate::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool> {
		Ok(self.subscriptions().cancel(id))
	}

	/// New best head subscription
	fn subscribe_new_heads(
		&self,
		_metadata: crate::Metadata,
		subscriber: Subscriber<Block::Header>,
	) {
		subscribe_headers(
			self.client(),
			self.subscriptions(),
			subscriber,
			|| self.client().info().best_hash,
			|| self.client().import_notification_stream()
				.filter(|notification| future::ready(notification.is_new_best))
				.map(|notification| Ok::<_, ()>(notification.header))
				.compat(),
		)
	}

	/// Unsubscribe from new best head subscription.
	fn unsubscribe_new_heads(
		&self,
		_metadata: Option<crate::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool> {
		Ok(self.subscriptions().cancel(id))
	}

	/// Finalized head subscription
	fn subscribe_finalized_heads(
		&self,
		_metadata: crate::Metadata,
		subscriber: Subscriber<Block::Header>,
	) {
		subscribe_headers(
			self.client(),
			self.subscriptions(),
			subscriber,
			|| self.client().info().finalized_hash,
			|| self.client().finality_notification_stream()
				.map(|notification| Ok::<_, ()>(notification.header))
				.compat(),
		)
	}

	/// Unsubscribe from finalized head subscription.
	fn unsubscribe_finalized_heads(
		&self,
		_metadata: Option<crate::Metadata>,
		id: SubscriptionId,
	) -> RpcResult<bool> {
		Ok(self.subscriptions().cancel(id))
	}
}

/// Create new state API that works on full node.
pub fn new_full<Block: BlockT, Client>(
	client: Arc<Client>,
	subscriptions: SubscriptionManager,
) -> Chain<Block, Client>
	where
		Block: BlockT + 'static,
		Client: BlockBackend<Block> + HeaderBackend<Block> + BlockchainEvents<Block> + 'static,
{
	Chain {
		backend: Box::new(self::chain_full::FullChain::new(client, subscriptions)),
	}
}

/// Create new state API that works on light node.
pub fn new_light<Block: BlockT, Client, F: Fetcher<Block>>(
	client: Arc<Client>,
	subscriptions: SubscriptionManager,
	remote_blockchain: Arc<dyn RemoteBlockchain<Block>>,
	fetcher: Arc<F>,
) -> Chain<Block, Client>
	where
		Block: BlockT + 'static,
		Client: BlockBackend<Block> + HeaderBackend<Block> + BlockchainEvents<Block> + 'static,
		F: Send + Sync + 'static,
{
	Chain {
		backend: Box::new(self::chain_light::LightChain::new(
			client,
			subscriptions,
			remote_blockchain,
			fetcher,
		)),
	}
}

/// Chain API with subscriptions support.
pub struct Chain<Block: BlockT, Client> {
	backend: Box<dyn ChainBackend<Client, Block>>,
}

impl<Block: BlockT, Client> Chain<Block, Client>
where
	Client: BlockchainEvents<Block> + HeaderBackend<Block> + Send + Sync + 'static,
{
	/// Convert a [`Chain`] to an [`RpcModule`]. Registers all the RPC methods available with the RPC server.
	pub fn into_rpc_module(self) -> Result<RpcModule, JsonRpseeError> {
		let mut rpc_module = RpcContextModule::new(self);

		rpc_module.register_method("chain_getHeader", |params, chain| {
			log::info!("chain_getBlock [{:?}]", params);
			// TODO: make is possible to register async methods on jsonrpsee servers.
			//https://github.com/paritytech/jsonrpsee/issues/291
			//
			// NOTE(niklasad1): will block the connection task on the server.
			let hash = params.one()?;
			futures::executor::block_on(chain.header(Some(hash))).map_err(rpc_err)
		})?;

		rpc_module.register_method("chain_getBlock", |params, chain| {
			log::info!("chain_getBlock [{:?}]", params);
			// TODO: make is possible to register async methods on jsonrpsee servers.
			//https://github.com/paritytech/jsonrpsee/issues/291
			//
			// NOTE(niklasad1): will block the connection task on the server.
			let hash = params.one()?;
			futures::executor::block_on(chain.block(Some(hash))).map_err(rpc_err)
		})?;

		rpc_module.register_method("chain_getBlockHash", |params, chain| {
			log::info!("chain_getBlockHash [{:?}]", params);
			let hash = params.one()?;
			chain.block_hash(hash).map_err(rpc_err)
		})?;

		rpc_module.register_method("chain_getFinalizedHead", |_, chain| {
			log::info!("chain_getFinalizedHead []");
			chain.finalized_head().map_err(rpc_err)
		})?;

		// TODO(jsonrpsee): register subscriptions on RpcContextModule
		// or should they be registrered elsewhere?!
		// let mut all_heads_sub = server.register_subscription("chain_subscribeallheads", "chain_subscribeallheads").unwrap();
		// let mut new_heads_sub = server.register_subscription("chain_subscribeNewHeads", "chain_unsubscribeAllHeads").unwrap();
		// let mut finalized_head_sub = server.register_subscription("chain_subscribeFinalizedHeads", "chain_unsubscribeFinalizedHeads").unwrap();
		//
		//	std::thread::spawn(move || loop {
		//		subscription.send(&"hello my friend").unwrap();
		//  });
		Ok(rpc_module.into_module())
	}

	pub async fn header(&self, hash: Option<Block::Hash>) -> Result<Option<Block::Header>, StateError> {
		self.backend.header(hash).await
	}

	pub async fn block(&self, hash: Option<Block::Hash>) -> Result<Option<SignedBlock<Block>>, StateError> {
		self.backend.block(hash).await
	}

	pub fn block_hash(
		&self,
		number: Option<ListOrValue<NumberOrHex>>,
	) -> Result<ListOrValue<Option<Block::Hash>>, StateError> {
		match number {
			None => self.backend.block_hash(None).map(ListOrValue::Value),
			Some(ListOrValue::Value(number)) => self.backend.block_hash(Some(number)).map(ListOrValue::Value),
			Some(ListOrValue::List(list)) => Ok(ListOrValue::List(list
				.into_iter()
				.map(|number| self.backend.block_hash(Some(number)))
				.collect::<Result<_, _>>()?
			))
		}
	}

	pub fn finalized_head(&self) -> Result<Block::Hash, StateError> {
		self.backend.finalized_head()
	}
}

/// Subscribe to new headers.
fn subscribe_headers<Block, Client, F, G, S, ERR>(
	client: &Arc<Client>,
	subscriptions: &SubscriptionManager,
	subscriber: Subscriber<Block::Header>,
	best_block_hash: G,
	stream: F,
) where
	Block: BlockT + 'static,
	Client: HeaderBackend<Block> + 'static,
	F: FnOnce() -> S,
	G: FnOnce() -> Block::Hash,
	ERR: ::std::fmt::Debug,
	S: Stream<Item=Block::Header, Error=ERR> + Send + 'static,
{
	subscriptions.add(subscriber, |sink| {
		// send current head right at the start.
		let header = client.header(BlockId::Hash(best_block_hash()))
			.map_err(client_err)
			.and_then(|header| {
				header.ok_or_else(|| "Best header missing.".to_owned().into())
			})
			.map_err(Into::into);

		// send further subscriptions
		let stream = stream()
			.map(|res| Ok(res))
			.map_err(|e| warn!("Block notification stream error: {:?}", e));

		sink
			.sink_map_err(|e| warn!("Error sending notifications: {:?}", e))
			.send_all(
				stream::iter_result(vec![Ok(header)])
					.chain(stream)
			)
			// we ignore the resulting Stream (if the first stream is over we are unsubscribed)
			.map(|_| ())
	});
}

fn client_err(err: sp_blockchain::Error) -> StateError {
	StateError::Client(Box::new(err))
}

fn rpc_err(err: StateError) -> JsonRpseeError {
	JsonRpseeError::Custom(err.to_string())
}
