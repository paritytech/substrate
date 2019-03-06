// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Substrate service. Starts a thread that spins up the network, client, and extrinsic pool.
//! Manages communication between them.

#![warn(missing_docs)]

use std::{
	marker::PhantomData,
	sync::Arc,
};

use client::runtime_api::ApiExt;
use futures::Future;
use inherents::pool::InherentsPool;
use log::{info, debug, warn};
use parity_codec::Decode;
use primitives::{ExecutionContext, OffchainExt};
use runtime_primitives::{
	generic::BlockId,
	traits::{self, ProvideRuntimeApi},
};
use transaction_pool::txpool::{Pool, ChainApi};

pub use offchain_primitives::OffchainWorkerApi;

struct Api<A: ChainApi> {
	transaction_pool: Arc<Pool<A>>,
	inherents_pool: Arc<InherentsPool>,
	at: BlockId<A::Block>,
}

impl<A: ChainApi> OffchainExt for Api<A> {
	fn submit_extrinsic(&mut self, ext: Vec<u8>) {
		info!("Submitting to the pool: {:?}", ext);
		let xt = match Decode::decode(&mut &*ext) {
			Some(xt) => xt,
			None => {
				warn!("Unable to decode extrinsic: {:?}", ext);
				return
			},
		};

		// TODO [ToDr] Move to inherent data

		// TODO [ToDr] Call API recursively panics!
		match self.transaction_pool.submit_one(&self.at, xt) {
			Ok(hash) => debug!("[{:?}] Offchain transaction added to the pool.", hash),
			Err(err) => warn!("Incorrect offchain transaction: {:?}", err),
		}
	}
}

/// An offchain workers manager.
#[derive(Debug)]
pub struct OffchainWorkers<C, Block> {
	client: Arc<C>,
	inherents_pool: Arc<InherentsPool>,
	_block: PhantomData<Block>,
}

impl<C, Block> OffchainWorkers<C, Block> {
	/// Creates new `OffchainWorkers`.
	pub fn new(client: Arc<C>, inherents_pool: Arc<InherentsPool>) -> Self {
		Self {
			client,
			inherents_pool,
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
	) -> impl Future<Item = (), Error = ()> where
		A: ChainApi<Block=Block> + 'static,
	{
		let runtime = self.client.runtime_api();
		let at = BlockId::number(*number);
		debug!("Checking offchain workers at {:?}", at);

		if let Ok(true) = runtime.has_api::<OffchainWorkerApi<Block>>(&at) {
			debug!("Running offchain workers at {:?}", at);
			let api = Box::new(Api {
				transaction_pool: pool.clone(),
				inherents_pool: self.inherents_pool.clone(),
				at: at.clone(),
			});
			runtime.generate_extrinsics_with_context(&at, ExecutionContext::OffchainWorker(api), *number).unwrap();
		}
		return futures::future::ok(())
	}
}
