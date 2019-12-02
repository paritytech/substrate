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

//! Substrate transaction pool implementation.

#![warn(missing_docs)]
#![warn(unused_extern_crates)]

mod api;
mod maintainer;

pub mod error;
#[cfg(test)]
mod tests;

pub use txpool;
pub use crate::api::{FullChainApi, LightChainApi};
pub use crate::maintainer::{FullBasicPoolMaintainer, LightBasicPoolMaintainer};

use std::{collections::HashMap, sync::Arc};
use futures::{Future, FutureExt};

use sp_runtime::{
	generic::BlockId,
	traits::Block as BlockT,
};
use txpool_api::{
	TransactionPool, PoolStatus, ImportNotificationStream,
	TxHash, TransactionFor, TransactionStatusStreamFor,
};

/// Basic implementation of transaction pool that can be customized by providing PoolApi.
pub struct BasicPool<PoolApi, Block>
	where
		Block: BlockT,
		PoolApi: txpool::ChainApi<Block=Block, Hash=Block::Hash>,
{
	pool: Arc<txpool::Pool<PoolApi>>,
}

impl<PoolApi, Block> BasicPool<PoolApi, Block>
	where
		Block: BlockT,
		PoolApi: txpool::ChainApi<Block=Block, Hash=Block::Hash>,
{
	/// Create new basic transaction pool with provided api.
	pub fn new(options: txpool::Options, pool_api: PoolApi) -> Self {
		BasicPool {
			pool: Arc::new(txpool::Pool::new(options, pool_api)),
		}
	}

	/// Gets shared reference to the underlying pool.
	pub fn pool(&self) -> &Arc<txpool::Pool<PoolApi>> {
		&self.pool
	}
}

impl<PoolApi, Block> TransactionPool for BasicPool<PoolApi, Block>
	where
		Block: BlockT,
		PoolApi: 'static + txpool::ChainApi<Block=Block, Hash=Block::Hash, Error=error::Error>,
{
	type Block = PoolApi::Block;
	type Hash = txpool::ExHash<PoolApi>;
	type InPoolTransaction = txpool::base_pool::Transaction<TxHash<Self>, TransactionFor<Self>>;
	type Error = error::Error;

	fn submit_at(
		&self,
		at: &BlockId<Self::Block>,
		xts: impl IntoIterator<Item=TransactionFor<Self>> + 'static,
	) -> Box<dyn Future<Output=Result<Vec<Result<TxHash<Self>, Self::Error>>, Self::Error>> + Send + Unpin> {
		Box::new(self.pool.submit_at(at, xts, false))
	}

	fn submit_one(
		&self,
		at: &BlockId<Self::Block>,
		xt: TransactionFor<Self>,
	) -> Box<dyn Future<Output=Result<TxHash<Self>, Self::Error>> + Send + Unpin> {
		Box::new(self.pool.submit_one(at, xt))
	}

	fn submit_and_watch(
		&self,
		at: &BlockId<Self::Block>,
		xt: TransactionFor<Self>,
	) -> Box<dyn Future<Output=Result<Box<TransactionStatusStreamFor<Self>>, Self::Error>> + Send + Unpin> {
		Box::new(
			self.pool.submit_and_watch(at, xt)
				.map(|result| result.map(|watcher| Box::new(watcher.into_stream()) as _))
		)
	}

	fn remove_invalid(&self, hashes: &[TxHash<Self>]) -> Vec<Arc<Self::InPoolTransaction>> {
		self.pool.remove_invalid(hashes)
	}

	fn status(&self) -> PoolStatus {
		self.pool.status()
	}

	fn ready(&self) -> Box<dyn Iterator<Item=Arc<Self::InPoolTransaction>>> {
		Box::new(self.pool.ready())
	}

	fn import_notification_stream(&self) -> ImportNotificationStream {
		self.pool.import_notification_stream()
	}

	fn hash_of(&self, xt: &TransactionFor<Self>) -> TxHash<Self> {
		self.pool.hash_of(xt)
	}

	fn on_broadcasted(&self, propagations: HashMap<TxHash<Self>, Vec<String>>) {
		self.pool.on_broadcasted(propagations)
	}
}
