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
use futures::{Stream, Future, sync::mpsc};
use inherents::pool::InherentsPool;
use log::{info, debug, warn};
use parity_codec::Decode;
use primitives::{ExecutionContext, OffchainExt};
use runtime_primitives::{
	generic::BlockId,
	traits::{self, ProvideRuntimeApi, Extrinsic},
};
use tokio::runtime::TaskExecutor;
use transaction_pool::txpool::{Pool, ChainApi};

pub use offchain_primitives::OffchainWorkerApi;

enum ExtMessage {
	SubmitExtrinsic(Vec<u8>),
}

struct AsyncApi(mpsc::UnboundedSender<ExtMessage>);

impl OffchainExt for AsyncApi {
	fn submit_extrinsic(&mut self, ext: Vec<u8>) {
		let _ = self.0.unbounded_send(ExtMessage::SubmitExtrinsic(ext));
	}
}

struct Api<A: ChainApi> {
	receiver: Option<mpsc::UnboundedReceiver<ExtMessage>>,
	transaction_pool: Arc<Pool<A>>,
	inherents_pool: Arc<InherentsPool<<A::Block as traits::Block>::Extrinsic>>,
	at: BlockId<A::Block>,
}

impl<A: ChainApi> Api<A> {
	pub fn new(
		transaction_pool: Arc<Pool<A>>,
		inherents_pool: Arc<InherentsPool<<A::Block as traits::Block>::Extrinsic>>,
		at: BlockId<A::Block>,
	) -> (AsyncApi, Self) {
		let (tx, rx) = mpsc::unbounded();
		let api = Self {
			receiver: Some(rx),
			transaction_pool,
			inherents_pool,
			at,
		};
		(AsyncApi(tx), api)
	}

	pub fn process(mut self) -> impl Future<Item=(), Error=()> {
		let receiver = self.receiver.take().expect("Take invoked only once.");

		receiver.for_each(move |msg| {
			match msg {
				ExtMessage::SubmitExtrinsic(ext) => self.submit_extrinsic(ext),
			}
			Ok(())
		})
	}

	fn submit_extrinsic(&mut self, ext: Vec<u8>) {
		let xt = match <A::Block as traits::Block>::Extrinsic::decode(&mut &*ext) {
			Some(xt) => xt,
			None => {
				warn!("Unable to decode extrinsic: {:?}", ext);
				return
			},
		};

		info!("Submitting to the pool: {:?} (isSigned: {:?})", xt, xt.is_signed());
		match self.transaction_pool.submit_one(&self.at, xt.clone()) {
			Ok(hash) => debug!("[{:?}] Offchain transaction added to the pool.", hash),
			Err(_) => {
				debug!("Offchain inherent added to the pool.");
				self.inherents_pool.add(xt);
			},
		}
	}
}

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
		debug!("Checking offchain workers at {:?}", at);

		if let Ok(true) = runtime.has_api::<OffchainWorkerApi<Block>>(&at) {
			debug!("Running offchain workers at {:?}", at);
			let (api, runner) = Api::new(pool.clone(), self.inherents_pool.clone(), at.clone());
			self.executor.spawn(runner.process());

			let api = Box::new(api);
			runtime.generate_extrinsics_with_context(&at, ExecutionContext::OffchainWorker(api), *number).unwrap();
		}
	}
}

#[cfg(test)]
mod tests {
	#[test]
	fn should_insert_to_the_pool() {
		assert_eq!(true, false);
	}
}
