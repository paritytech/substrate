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
use std::marker::PhantomData;

use futures::StreamExt;
use sc_client_api::{BlockchainEvents, light::{Fetcher, RemoteBlockchain}};
use jsonrpsee_ws_server::{RpcModule, RpcContextModule, SubscriptionSink};
use jsonrpsee_types::error::{Error as JsonRpseeError, CallError as JsonRpseeCallError};
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
}

/// Create new state API that works on full node.
pub fn new_full<Block: BlockT, Client>(
	client: Arc<Client>,
) -> Chain<Block, Client>
	where
		Block: BlockT + 'static,
		Client: BlockBackend<Block> + HeaderBackend<Block> + BlockchainEvents<Block> + 'static,
{
	Chain {
		backend: Box::new(self::chain_full::FullChain::new(client)),
	}
}

/// Create new state API that works on light node.
pub fn new_light<Block: BlockT, Client, F: Fetcher<Block>>(
	client: Arc<Client>,
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
	pub fn into_rpc_module(self) -> Result<(RpcModule, ChainSubSinks<Block, Client>), JsonRpseeError> {
		let client = self.backend.client().clone();
		let mut ctx_module = RpcContextModule::new(self);

		ctx_module.register_method("chain_getHeader", |params, chain| {
			log::info!("chain_getBlock [{:?}]", params);
			// TODO: make is possible to register async methods on jsonrpsee servers.
			//https://github.com/paritytech/jsonrpsee/issues/291
			//
			// NOTE(niklasad1): will block the connection task on the server.
			let hash = params.one()?;
			futures::executor::block_on(chain.header(Some(hash))).map_err(rpc_err)
		})?;

		ctx_module.register_method("chain_getBlock", |params, chain| {
			log::info!("chain_getBlock [{:?}]", params);
			// TODO: make is possible to register async methods on jsonrpsee servers.
			//https://github.com/paritytech/jsonrpsee/issues/291
			//
			// NOTE(niklasad1): will block the connection task on the server.
			let hash = params.one()?;
			futures::executor::block_on(chain.block(Some(hash))).map_err(rpc_err)
		})?;

		ctx_module.register_method("chain_getBlockHash", |params, chain| {
			log::info!("chain_getBlockHash [{:?}]", params);
			let hash = params.one()?;
			chain.block_hash(hash).map_err(rpc_err)
		})?;

		ctx_module.register_method("chain_getFinalizedHead", |_, chain| {
			log::info!("chain_getFinalizedHead []");
			chain.finalized_head().map_err(rpc_err)
		})?;

		let mut rpc_module = ctx_module.into_module();

		let all_heads = rpc_module.register_subscription("chain_subscribeAllHeads", "chain_unsubscribeAllHeads").unwrap();
		let new_heads = rpc_module.register_subscription("chain_subscribeNewHeads", "chain_unsubscribeNewHeads").unwrap();
		let finalized_heads = rpc_module.register_subscription("chain_subscribeFinalizedHeads", "chain_unsubscribeFinalizedHeads").unwrap();
		// TODO: wrap the different sinks in a new-type error prone with three params with
		// the same type.
		let subs = ChainSubSinks::new(new_heads, all_heads, finalized_heads, client);

		Ok((rpc_module, subs))
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

fn client_err(err: sp_blockchain::Error) -> StateError {
	StateError::Client(Box::new(err))
}

fn rpc_err(err: StateError) -> JsonRpseeCallError {
	JsonRpseeCallError::Failed(Box::new(err))
}

/// Possible subscriptions for the chain RPC API.
pub struct ChainSubSinks<Block, Client> {
	new_heads: SubscriptionSink,
	all_heads: SubscriptionSink,
	finalized_heads: SubscriptionSink,
	client: Arc<Client>,
	marker: PhantomData<Block>,
}

impl<Block: BlockT, Client> ChainSubSinks<Block, Client>
where
	Client: BlockchainEvents<Block> + HeaderBackend<Block> + Send + Sync + 'static,
{
	/// Create new Chain subscription that needs to be spawned.
	pub fn new(
		new_heads: SubscriptionSink,
		all_heads: SubscriptionSink,
		finalized_heads: SubscriptionSink,
		client: Arc<Client>
	) -> Self {
		Self { new_heads, all_heads, finalized_heads, client, marker: PhantomData }
	}

	/// Spawns a event loop that listens for events and sends them out to the subscribers.
	// TODO: better impl.
	pub fn spawn_subscriptions(mut self) {
		std::thread::spawn(move || {
			// Send current head at the start.
			let best_head = self.client.header(BlockId::Hash(self.client.info().best_hash)).expect("header is known; qed");
			let finalized_header = self.client.header(BlockId::Hash(self.client.info().finalized_hash)).expect("header is known; qed");
			let _ = self.all_heads.send(&best_head);
			let _ = self.new_heads.send(&best_head);
			let _ = self.finalized_heads.send(&finalized_header);

			// TODO: this is just an example; we should use select or spawn these tasks
			// on the subscription task executor
			loop {
				let import =
					futures::executor::block_on(self.client.import_notification_stream().next()).unwrap();
				let _ = self.all_heads.send(&import.header);
				let _ = self.new_heads.send(&import.header);
				let finality =
					futures::executor::block_on(self.client.finality_notification_stream().next()).unwrap();
				let _ = self.finalized_heads.send(&finality.header);
			}
		});
	}
}
