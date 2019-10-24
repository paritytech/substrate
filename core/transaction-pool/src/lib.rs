// Copyright 2018-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Substrate transaction pool.

#![warn(missing_docs)]
#![warn(unused_extern_crates)]

mod api;
mod maintainer;
#[cfg(test)]
mod tests;

pub mod error;

pub use txpool;
pub use crate::api::{FullChainApi, LightChainApi};
pub use crate::maintainer::{
	TransactionPoolMaintainer,
	DefaultFullTransactionPoolMaintainer, DefaultLightTransactionPoolMaintainer,
};

use std::{collections::HashMap, hash::Hash, sync::Arc};
use futures::Future;

use client::{
	Client,
	light::fetcher::Fetcher,
	runtime_api::TaggedTransactionQueue,
};
use primitives::{Blake2Hasher, H256};
use sr_primitives::{
	serde::Serialize,
	generic::BlockId,
	traits::{Block as BlockT, Member, ProvideRuntimeApi},
};

use txpool::{EventStream, Options, watcher::Watcher};

/// Extrinsic hash type for a pool.
pub type ExHash<P> = <P as TransactionPool>::Hash;
/// Block hash type for a pool.
pub type BlockHash<P> = <<P as TransactionPool>::Block as BlockT>::Hash;
/// Extrinsic type for a pool.
pub type ExtrinsicFor<P> = <<P as TransactionPool>::Block as BlockT>::Extrinsic;

/// Transaction pool interface.
pub trait TransactionPool: Send + Sync {
	/// Block type.
	type Block: BlockT;
	/// Transaction Hash type.
	type Hash: Hash + Eq + Member + Serialize;
	/// Error type.
	type Error: From<txpool::error::Error> + txpool::error::IntoPoolError;

	/// Returns a future that imports a bunch of unverified extrinsics to the pool.
	fn submit_at(
		&self,
		at: &BlockId<Self::Block>,
		xts: impl IntoIterator<Item=ExtrinsicFor<Self>> + 'static,
	) -> Box<dyn Future<Output=Result<Vec<Result<Self::Hash, Self::Error>>, Self::Error>> + Send + Unpin>;

	/// Returns a future that imports one unverified extrinsic to the pool.
	fn submit_one(
		&self,
		at: &BlockId<Self::Block>,
		xt: ExtrinsicFor<Self>,
	) -> Box<dyn Future<Output=Result<Self::Hash, Self::Error>> + Send + Unpin>;

	/// Returns a future that import a single extrinsic and starts to watch their progress in the pool.
	fn submit_and_watch(
		&self,
		at: &BlockId<Self::Block>,
		xt: ExtrinsicFor<Self>,
	) -> Box<dyn Future<Output=Result<Watcher<Self::Hash, BlockHash<Self>>, Self::Error>> + Send + Unpin>;

	/// Remove extrinsics identified by given hashes (and dependent extrinsics) from the pool.
	fn remove_invalid(
		&self,
		hashes: &[Self::Hash],
	) -> Vec<Arc<txpool::base_pool::Transaction<Self::Hash, ExtrinsicFor<Self>>>>;

	/// Returns pool status.
	fn status(&self) -> txpool::base_pool::Status;

	/// Get an iterator for ready transactions ordered by priority
	fn ready(&self) -> Box<dyn Iterator<Item=Arc<txpool::base_pool::Transaction<Self::Hash, ExtrinsicFor<Self>>>>>;

	/// Return an event stream of transactions imported to the pool.
	fn import_notification_stream(&self) -> EventStream;

	/// Returns transaction hash
	fn hash_of(&self, xt: &ExtrinsicFor<Self>) -> Self::Hash;

	/// Notify the pool about transactions broadcast.
	fn on_broadcasted(&self, propagations: HashMap<Self::Hash, Vec<String>>);

	/// Returns a future that performs maintenance procedures on the pool.
	fn maintain(
		&self,
		id: &BlockId<Self::Block>,
		retracted: &[BlockHash<Self>],
	) -> Box<dyn Future<Output=()> + Send + Unpin>;
}

/// Basic implementation of transaction pool that can be customized by providing
/// different PoolApi and Maintainer.
pub struct BasicTransactionPool<PoolApi, Maintainer, Block>
	where
		Block: BlockT<Hash=H256>,
		PoolApi: txpool::ChainApi<Block=Block, Hash=H256>,
		Maintainer: TransactionPoolMaintainer<PoolApi>,
{
	pool: Arc<txpool::Pool<PoolApi>>,
	maintainer: Maintainer,
}

impl<PoolApi, Maintainer, Block> BasicTransactionPool<PoolApi, Maintainer, Block>
	where
		Block: BlockT<Hash=H256>,
		PoolApi: txpool::ChainApi<Block=Block, Hash=H256>,
		Maintainer: TransactionPoolMaintainer<PoolApi>,
{
	/// Create new basic transaction pool with given api and maintainer.
	pub fn new(options: Options, pool_api: PoolApi, maintainer: Maintainer) -> Self {
		BasicTransactionPool {
			pool: Arc::new(txpool::Pool::new(options, pool_api)),
			maintainer,
		}
	}
}

impl<Backend, Executor, Block, Api> BasicTransactionPool<
	api::FullChainApi<Client<Backend, Executor, Block, Api>, Block>,
	DefaultFullTransactionPoolMaintainer<Backend, Executor, Block, Api>,
	Block,
> where
	Block: BlockT<Hash=H256>,
	Backend: 'static + client::backend::Backend<Block, Blake2Hasher>,
	Client<Backend, Executor, Block, Api>: ProvideRuntimeApi,
	<Client<Backend, Executor, Block, Api> as ProvideRuntimeApi>::Api: TaggedTransactionQueue<Block>,
	Executor: 'static + Send + Sync + client::CallExecutor<Block, Blake2Hasher>,
	Api: 'static + Send + Sync,
{
	/// Create new basic full transaction pool with default API and maintainer.
	pub fn default_full(options: Options, client: Arc<Client<Backend, Executor, Block, Api>>) -> Self {
		Self::new(
			options,
			FullChainApi::new(client.clone()),
			DefaultFullTransactionPoolMaintainer::new(client),
		)
	}
}

impl<Backend, Executor, Block, Api, F> BasicTransactionPool<
	api::LightChainApi<Client<Backend, Executor, Block, Api>, F, Block>,
	DefaultLightTransactionPoolMaintainer<Backend, Executor, Block, Api, F>,
	Block,
> where
	Block: BlockT<Hash=H256>,
	Backend: 'static + client::backend::Backend<Block, Blake2Hasher>,
	Client<Backend, Executor, Block, Api>: ProvideRuntimeApi,
	<Client<Backend, Executor, Block, Api> as ProvideRuntimeApi>::Api: TaggedTransactionQueue<Block>,
	Executor: 'static + Send + Sync + client::CallExecutor<Block, Blake2Hasher>,
	Api: 'static + Send + Sync,
	F: 'static + Fetcher<Block>,
{
	/// Create new basic light transaction pool with default API and maintainer.
	pub fn default_light(
		options: Options,
		client: Arc<Client<Backend, Executor, Block, Api>>,
		fetcher: Arc<F>,
	) -> Self {
		Self::new(
			options,
			LightChainApi::new(client.clone(), fetcher.clone()),
			DefaultLightTransactionPoolMaintainer::with_defaults(client, fetcher),
		)
	}
}

impl<PoolApi, Maintainer, Block> TransactionPool for BasicTransactionPool<PoolApi, Maintainer, Block>
	where
		Block: BlockT<Hash=H256>,
		PoolApi: 'static + txpool::ChainApi<Block=Block, Hash=H256, Error=error::Error>,
		Maintainer: TransactionPoolMaintainer<PoolApi> + Sync,
{
	type Block = Block;
	type Hash = Block::Hash;
	type Error = error::Error;

	fn submit_at(
		&self,
		at: &BlockId<Self::Block>,
		xts: impl IntoIterator<Item=ExtrinsicFor<Self>> + 'static,
	) -> Box<dyn Future<Output=Result<Vec<Result<Block::Hash, Self::Error>>, Self::Error>> + Send + Unpin> {
		Box::new(self.pool.submit_at(at, xts, false))
	}

	fn submit_one(
		&self,
		at: &BlockId<Self::Block>,
		xt: ExtrinsicFor<Self>,
	) -> Box<dyn Future<Output=Result<Self::Hash, Self::Error>> + Send + Unpin> {
		Box::new(self.pool.submit_one(at, xt))
	}

	fn submit_and_watch(
		&self,
		at: &BlockId<Self::Block>,
		xt: ExtrinsicFor<Self>,
	) -> Box<dyn Future<Output=Result<Watcher<Self::Hash, BlockHash<Self>>, Self::Error>> + Send + Unpin> {
		Box::new(self.pool.submit_and_watch(at, xt))
	}

	fn remove_invalid(
		&self,
		hashes: &[Self::Hash],
	) -> Vec<Arc<txpool::base_pool::Transaction<Self::Hash, ExtrinsicFor<Self>>>> {
		self.pool.remove_invalid(hashes)
	}

	fn status(&self) -> txpool::base_pool::Status {
		self.pool.status()
	}

	fn ready(&self) -> Box<dyn Iterator<Item=Arc<txpool::base_pool::Transaction<Self::Hash, ExtrinsicFor<Self>>>>> {
		Box::new(self.pool.ready())
	}

	fn import_notification_stream(&self) -> EventStream {
		self.pool.import_notification_stream()
	}

	fn hash_of(&self, xt: &ExtrinsicFor<Self>) -> Self::Hash {
		self.pool.hash_of(xt)
	}

	fn on_broadcasted(&self, propagations: HashMap<Self::Hash, Vec<String>>) {
		self.pool.on_broadcasted(propagations)
	}

	fn maintain(
		&self,
		id: &BlockId<Block>,
		retracted: &[Block::Hash],
	) -> Box<dyn Future<Output=()> + Send + Unpin> {
		self.maintainer.maintain(id, retracted, &self.pool)
	}
}
