// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Consensus service.

/// Consensus service. A long runnung service that manages BFT agreement and parachain
/// candidate agreement over the network.

use std::thread;
use std::time::{Duration, Instant};
use std::sync::Arc;

use bft::{self, BftService};
use client::{BlockchainEvents, ChainHead};
use ed25519;
use futures::prelude::*;
use parking_lot::Mutex;
use polkadot_api::PolkadotApi;
use primitives::block::Header;
use runtime_support::Hashable;
use tokio_core::reactor;
use transaction_pool::TransactionPool;

use super::{Network, Collators, ProposerFactory};
use error;

const TIMER_DELAY_MS: u64 = 5000;
const TIMER_INTERVAL_MS: u64 = 500;

fn start_bft<F, C>(
	header: &Header,
	handle: reactor::Handle,
	bft_service: &BftService<F, C>,
) where
	F: bft::Environment + 'static,
	C: bft::BlockImport + bft::Authorities + 'static,
	<F as bft::Environment>::Error: ::std::fmt::Debug,
	<F::Proposer as bft::Proposer>::Error: ::std::fmt::Display + Into<error::Error>,
{
	match bft_service.build_upon(&header) {
		Ok(Some(bft)) => handle.spawn(bft),
		Ok(None) => {},
		Err(e) => debug!(target: "bft", "BFT agreement error: {:?}", e),
	}
}

/// Consensus service. Starts working when created.
pub struct Service {
	thread: Option<thread::JoinHandle<()>>,
	exit_signal: Option<::exit_future::Signal>,
}

impl Service {
	/// Create and start a new instance.
	pub fn new<C, N: Network + Collators + Send + 'static>(
		client: Arc<C>,
		network: N,
		transaction_pool: Arc<Mutex<TransactionPool>>,
		parachain_empty_duration: Duration,
		key: ed25519::Pair,
	) -> Service
		where
			C: BlockchainEvents + ChainHead + bft::BlockImport + bft::Authorities + PolkadotApi + Send + Sync + 'static,
			C::CheckedBlockId: Send + 'static,
			N::TableRouter: Send + 'static,
			<N::Collation as IntoFuture>::Future: Send + 'static,
	{
		let (signal, exit) = ::exit_future::signal();
		let thread = thread::spawn(move || {
			let mut core = reactor::Core::new().expect("tokio::Core could not be created");
			let key = Arc::new(key);

			let factory = ProposerFactory {
				client: client.clone(),
				transaction_pool: transaction_pool.clone(),
				collators: network.clone(),
				network,
				parachain_empty_duration,
				handle: core.handle(),
			};
			let bft_service = Arc::new(BftService::new(client.clone(), key, factory));

			let notifications = {
				let handle = core.handle();
				let client = client.clone();
				let bft_service = bft_service.clone();

				client.import_notification_stream().for_each(move |notification| {
					if notification.is_new_best {
						start_bft(&notification.header, handle.clone(), &*bft_service);
					}
					Ok(())
				})
			};

			let interval = reactor::Interval::new_at(
				Instant::now() + Duration::from_millis(TIMER_DELAY_MS),
				Duration::from_millis(TIMER_INTERVAL_MS),
				&core.handle(),
			).expect("it is always possible to create an interval with valid params");
			let mut prev_best = match client.best_block_header() {
				Ok(header) => header.blake2_256(),
				Err(e) => {
					warn!("Cant's start consensus service. Error reading best block header: {:?}", e);
					return;
				}
			};

			let timed = {
				let c = client.clone();
				let s = bft_service.clone();
				let handle = core.handle();

				interval.map_err(|e| debug!("Timer error: {:?}", e)).for_each(move |_| {
					if let Ok(best_block) = c.best_block_header() {
						let hash = best_block.blake2_256();
						if hash == prev_best {
							debug!("Starting consensus round after a timeout");
							start_bft(&best_block, handle.clone(), &*s);
						}
						prev_best = hash;
					}
					Ok(())
				})
			};

			core.handle().spawn(notifications);
			core.handle().spawn(timed);
			if let Err(e) = core.run(exit) {
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
