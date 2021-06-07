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

use crate::SubscriptionTaskExecutor;

use futures::{StreamExt, FutureExt};
use sc_client_api::{BlockchainEvents, light::{Fetcher, RemoteBlockchain}};
use jsonrpsee_ws_server::RpcModule;
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
	executor: Arc<SubscriptionTaskExecutor>,
) -> Chain<Block, Client>
	where
		Block: BlockT + 'static,
		Client: BlockBackend<Block> + HeaderBackend<Block> + BlockchainEvents<Block> + 'static,
{
	Chain {
		backend: Box::new(self::chain_full::FullChain::new(client)),
		executor,
	}
}

/// Create new state API that works on light node.
pub fn new_light<Block: BlockT, Client, F: Fetcher<Block>>(
	client: Arc<Client>,
	remote_blockchain: Arc<dyn RemoteBlockchain<Block>>,
	fetcher: Arc<F>,
	executor: Arc<SubscriptionTaskExecutor>,
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
		executor,
	}
}

/// Chain API with subscriptions support.
pub struct Chain<Block: BlockT, Client> {
	backend: Box<dyn ChainBackend<Client, Block>>,
	executor: Arc<SubscriptionTaskExecutor>,
}

impl<Block: BlockT, Client> Chain<Block, Client>
where
	Client: BlockchainEvents<Block> + HeaderBackend<Block> + Send + Sync + 'static,
{
	/// Convert a [`Chain`] to an [`RpcModule`]. Registers all the RPC methods available with the RPC server.
	pub fn into_rpc_module(self) -> Result<RpcModule<Self>, JsonRpseeError> {
		let mut rpc_module = RpcModule::new(self);

		rpc_module.register_async_method("chain_getHeader", |params, chain| {
			let hash = params.one().ok();
			async move { chain.header(hash).await.map_err(rpc_err) }.boxed()
		})?;

		rpc_module.register_async_method("chain_getBlock", |params, chain| {
			let hash = params.one().ok();
			async move { chain.block(hash).await.map_err(rpc_err) }.boxed()
		})?;

		rpc_module.register_method("chain_getBlockHash", |params, chain| {
			let hash = params.one().ok();
			chain.block_hash(hash).map_err(rpc_err)
		})?;

		rpc_module.register_method("chain_getFinalizedHead", |_, chain| {
			chain.finalized_head().map_err(rpc_err)
		})?;

		rpc_module.register_subscription("chain_subscribeAllHeads", "chain_unsubscribeAllHeads", |_params, sink, ctx| {
			let executor = ctx.executor.clone();

			let fut = async move {
				let hash = ctx.backend.client().info().best_hash;
				let best_head = ctx.backend.header(Some(hash)).await.expect("hash is valid; qed");
				// TODO(niklasad1): error to detect when the subscription is closed.
				let _ = sink.send(&best_head);
				let stream = ctx.backend.client().import_notification_stream();
				stream.for_each(|item| {
					let _ = sink.send(&item.header);
					futures::future::ready(())
				}).await;
			};

			executor.execute_new(Box::pin(fut));
			Ok(())
		})?;

		rpc_module.register_subscription("chain_subscribeNewHeads", "chain_unsubscribeNewHeads", |_params, sink, ctx| {
			let executor = ctx.executor.clone();

			let fut = async move {
				let hash = ctx.backend.client().info().best_hash;
				let best_head = ctx.backend.header(Some(hash)).await.expect("hash is valid; qed");
				let _ = sink.send(&best_head);
				let stream = ctx.backend.client().import_notification_stream();
				stream.for_each(|item| {
					let _ = sink.send(&item.header);
					futures::future::ready(())
				}).await;
			};

			executor.execute_new(Box::pin(fut));
			Ok(())
		})?;

		rpc_module.register_subscription("chain_subscribeFinalizedHeads", "chain_unsubscribeFinalizedHeads", |_params, sink, ctx| {
			let executor = ctx.executor.clone();

			let fut = async move {
				let hash = ctx.backend.client().info().finalized_hash;
				let finalized_head = ctx.backend.header(Some(hash)).await.expect("hash is valid; qed");
				let _ = sink.send(&finalized_head);
				let stream = ctx.backend.client().finality_notification_stream();
				stream.for_each(|item| {
					let _ = sink.send(&item.header);
					futures::future::ready(())
				}).await;
			};

			executor.execute_new(Box::pin(fut));
			Ok(())
		})?;

		Ok(rpc_module)
	}

	/// TODO: document this
	pub async fn header(&self, hash: Option<Block::Hash>) -> Result<Option<Block::Header>, StateError> {
		self.backend.header(hash).await
	}

	/// TODO: document this
	async fn block(&self, hash: Option<Block::Hash>) -> Result<Option<SignedBlock<Block>>, StateError> {
		self.backend.block(hash).await
	}

	/// TODO: document this
	fn block_hash(
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

	/// TODO: document this
	fn finalized_head(&self) -> Result<Block::Hash, StateError> {
		self.backend.finalized_head()
	}
}

fn client_err(err: sp_blockchain::Error) -> StateError {
	StateError::Client(Box::new(err))
}

fn rpc_err(err: StateError) -> JsonRpseeCallError {
	JsonRpseeCallError::Failed(Box::new(err))
}
