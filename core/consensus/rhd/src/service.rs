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

//! Consensus service.

/// Consensus service. A long running service that manages BFT agreement
/// the network.
use std::thread;
use std::time::{Duration, Instant};
use std::sync::Arc;

use client::{BlockchainEvents, BlockBody};
use futures::prelude::*;
use transaction_pool::txpool::{Pool as TransactionPool, ChainApi as PoolChainApi};
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, BlockNumberToHash};

use tokio::executor::current_thread::TaskExecutor as LocalThreadHandle;
use tokio::runtime::TaskExecutor as ThreadPoolHandle;
use tokio::runtime::current_thread::Runtime as LocalRuntime;
use tokio::timer::Interval;

use parking_lot::RwLock;
use consensus::{self, offline_tracker::OfflineTracker};

use super::{Network, ProposerFactory, AuthoringApi};
use {consensus, primitives, ed25519, error, BftService, LocalProposer};

const TIMER_DELAY_MS: u64 = 5000;
const TIMER_INTERVAL_MS: u64 = 500;

// spin up an instance of BFT agreement on the current thread's executor.
// panics if there is no current thread executor.
fn start_bft<F, C, Block>(
	header: <Block as BlockT>::Header,
	bft_service: Arc<BftService<Block, F, C>>,
) where
	F: consensus::Environment<Block> + 'static,
	C: consensus::BlockImport<Block> + consensus::Authorities<Block> + 'static,
	F::Error: ::std::fmt::Debug,
	<F::Proposer as consensus::Proposer<Block>>::Error: ::std::fmt::Display + Into<error::Error>,
	<F as consensus::Environment<Block>>::Proposer : LocalProposer<Block>,
	<F as consensus::Environment<Block>>::Error: ::std::fmt::Display,
	Block: BlockT,
{
	let mut handle = LocalThreadHandle::current();
	match bft_service.build_upon(&header) {
		Ok(Some(bft_work)) => if let Err(e) = handle.spawn_local(Box::new(bft_work)) {
		    warn!(target: "bft", "Couldn't initialize BFT agreement: {:?}", e);
		}
		Ok(None) => trace!(target: "bft", "Could not start agreement on top of {}", header.hash()),
		Err(e) => warn!(target: "bft", "BFT agreement error: {}", e),
 	}
}

/// Consensus service. Starts working when created.
pub struct Service {
	thread: Option<thread::JoinHandle<()>>,
	exit_signal: Option<::exit_future::Signal>,
}

impl Service {
	/// Create and start a new instance.
	pub fn new<A, P, C, N>(
		client: Arc<C>,
		api: Arc<A>,
		network: N,
		transaction_pool: Arc<TransactionPool<P>>,
		thread_pool: ThreadPoolHandle,
		key: ed25519::Pair,
		block_delay: u64,
	) -> Service
		where
			error::Error: From<<A as AuthoringApi>::Error>,
			A: AuthoringApi + BlockNumberToHash + 'static,
			P: PoolChainApi<Block = <A as AuthoringApi>::Block> + 'static,
			C: BlockchainEvents<<A as AuthoringApi>::Block>
				+ BlockBody<<A as AuthoringApi>::Block>
				+ consensus::SelectChain<<A as AuthoringApi>::Block>
				+ consensus::BlockImport<<A as AuthoringApi>::Block>
				+ consensus::Authorities<<A as AuthoringApi>::Block> + Send + Sync + 'static,
			primitives::H256: From<<<A as AuthoringApi>::Block as BlockT>::Hash>,
			<<A as AuthoringApi>::Block as BlockT>::Hash: PartialEq<primitives::H256> + PartialEq,
			N: Network<Block = <A as AuthoringApi>::Block> + Send + 'static,
	{

		let (signal, exit) = ::exit_future::signal();
		let thread = thread::spawn(move || {
			let mut runtime = LocalRuntime::new().expect("Could not create local runtime");
			let key = Arc::new(key);

			let factory = ProposerFactory {
				client: api.clone(),
				transaction_pool: transaction_pool.clone(),
				network,
				handle: thread_pool.clone(),
				offline: Arc::new(RwLock::new(OfflineTracker::new())),
				force_delay: block_delay,
			};
			let bft_service = Arc::new(BftService::new(client.clone(), key, factory));

			let notifications = {
				let client = client.clone();
				let bft_service = bft_service.clone();

				client.import_notification_stream().for_each(move |notification| {
					if notification.is_new_best {
						start_bft(notification.header, bft_service.clone());
					}
					Ok(())
				})
			};

			let interval = Interval::new(
				Instant::now() + Duration::from_millis(TIMER_DELAY_MS),
				Duration::from_millis(TIMER_INTERVAL_MS),
			);

			let mut prev_best = match client.best_block_header() {
				Ok(header) => header.hash(),
				Err(e) => {
					warn!("Cant's start consensus service. Error reading best block header: {:?}", e);
					return;
				}
			};

			let timed = {
				let c = client.clone();
				let s = bft_service.clone();

				interval.map_err(|e| debug!(target: "bft", "Timer error: {:?}", e)).for_each(move |_| {
					if let Ok(best_block) = c.best_block_header() {
						let hash = best_block.hash();

						if hash == prev_best {
							debug!(target: "bft", "Starting consensus round after a timeout");
							start_bft(best_block, s.clone());
						}
						prev_best = hash;
					}
					Ok(())
				})
			};

			runtime.spawn(notifications);
			runtime.spawn(timed);

			if let Err(e) = runtime.block_on(exit) {
				debug!("BFT event loop error {:?}", e);
			}
		});
		Service {
			thread: Some(thread),
			exit_signal: Some(signal),
		}
	}
}

impl Drop for Service {
	fn drop(&mut self) {
		if let Some(signal) = self.exit_signal.take() {
			signal.fire();
		}

		if let Some(thread) = self.thread.take() {
			thread.join().expect("The service thread has panicked");
		}
	}
}
