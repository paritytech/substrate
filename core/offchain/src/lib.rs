// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Substrate offchain workers.
//!
//! The offchain workers is a special function of the runtime that
//! gets executed after block is imported. During execution
//! it's able to asynchronously submit extrinsics that will either
//! be propagated to other nodes (transactions) or will be
//! added to the next block produced by the node as inherents.
//!
//! Offchain workers can be used for computation-heavy tasks
//! that are not feasible for execution during regular block processing.
//! It can either be tasks that no consensus is required for,
//! or some form of consensus over the data can be built on-chain
//! for instance via:
//! 1. Challenge period for incorrect computations
//! 2. Majority voting for results
//! 3. etc

#![warn(missing_docs)]

use std::{
	marker::PhantomData,
	sync::Arc,
};

use client::runtime_api::ApiExt;
use inherents::pool::InherentsPool;
use log::{debug, warn};
use primitives::ExecutionContext;
use runtime_primitives::{
	generic::BlockId,
	traits::{self, ProvideRuntimeApi},
};
use tokio::runtime::TaskExecutor;
use transaction_pool::txpool::{Pool, ChainApi};

mod api;

pub use offchain_primitives::OffchainWorkerApi;

/// An offchain workers manager.
#[derive(Debug)]
pub struct OffchainWorkers<C, Block: traits::Block> {
	client: Arc<C>,
	inherents_pool: Arc<InherentsPool<<Block as traits::Block>::Extrinsic>>,
	executor: TaskExecutor,
	_block: PhantomData<Block>,
}

impl<C, Block: traits::Block> OffchainWorkers<C, Block> {
	/// Creates new `OffchainWorkers`.
	pub fn new(
		client: Arc<C>,
		inherents_pool: Arc<InherentsPool<<Block as traits::Block>::Extrinsic>>,
		executor: TaskExecutor,
	) -> Self {
		Self {
			client,
			inherents_pool,
			executor,
			_block: PhantomData,
		}
	}
}

impl<C, Block> OffchainWorkers<C, Block> where
	Block: traits::Block,
	C: ProvideRuntimeApi,
	C::Api: OffchainWorkerApi<Block>,
{
	/// Start the offchain workers after given block.
	pub fn on_block_imported<A>(
		&self,
		number: &<Block::Header as traits::Header>::Number,
		pool: &Arc<Pool<A>>,
	) where
		A: ChainApi<Block=Block> + 'static,
	{
		let runtime = self.client.runtime_api();
		let at = BlockId::number(*number);
		let has_api = runtime.has_api::<OffchainWorkerApi<Block>>(&at);
		debug!("Checking offchain workers at {:?}: {:?}", at, has_api);

		if has_api.unwrap_or(false) {
			let (api, runner) = api::Api::new(pool.clone(), self.inherents_pool.clone(), at.clone());
			self.executor.spawn(runner.process());

			debug!("Running offchain workers at {:?}", at);
			let api = Box::new(api);
			runtime.offchain_worker_with_context(&at, ExecutionContext::OffchainWorker(api), *number).unwrap();
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use futures::Future;

	#[test]
	fn should_call_into_runtime_and_produce_extrinsic() {
		// given
		let _ = env_logger::try_init();
		let runtime = tokio::runtime::Runtime::new().unwrap();
		let client = Arc::new(test_client::new());
		let pool = Arc::new(Pool::new(Default::default(), ::transaction_pool::ChainApi::new(client.clone())));
		let inherents = Arc::new(InherentsPool::default());

		// when
		let offchain = OffchainWorkers::new(client, inherents.clone(), runtime.executor());
		offchain.on_block_imported(&0u64, &pool);

		// then
		runtime.shutdown_on_idle().wait().unwrap();
		assert_eq!(inherents.drain().len(), 1);
	}
}
