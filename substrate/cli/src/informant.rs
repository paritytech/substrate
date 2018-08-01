// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Console informant. Prints sync progress and block events. Runs on the calling thread.

use std::time::{Duration, Instant};
use futures::{Future, Stream};
use service::{Service, Components};
use tokio::runtime::TaskExecutor;
use tokio::timer::Interval;
use network::{SyncState, SyncProvider};
use client::BlockchainEvents;
use runtime_primitives::traits::{Header, As};
use substrate_extrinsic_pool::api::ExtrinsicPool;

const TIMER_INTERVAL_MS: u64 = 5000;

/// Spawn informant on the event loop
pub fn start<C>(service: &Service<C>, exit: ::exit_future::Exit, handle: TaskExecutor)
	where
		C: Components,
{
	let interval = Interval::new(Instant::now(), Duration::from_millis(TIMER_INTERVAL_MS));

	let network = service.network();
	let client = service.client();
	let txpool = service.extrinsic_pool();

	let display_notifications = interval.map_err(|e| debug!("Timer error: {:?}", e)).for_each(move |_| {
		let sync_status = network.status();

		if let Ok(best_block) = client.best_block_header() {
			let hash = best_block.hash();
			let num_peers = sync_status.num_peers;
			let status = match (sync_status.sync.state, sync_status.sync.best_seen_block) {
				(SyncState::Idle, _) => "Idle".into(),
				(SyncState::Downloading, None) => "Syncing".into(),
				(SyncState::Downloading, Some(n)) => format!("Syncing, target=#{}", n),
			};
			let txpool_status = txpool.light_status();
			let best_number: u64 = best_block.number().as_();
			info!(target: "substrate", "{} ({} peers), best: #{} ({})", status, sync_status.num_peers, best_number, hash);
			telemetry!("system.interval"; "status" => status, "peers" => num_peers, "height" => best_number, "best" => ?hash, "txcount" => txpool_status.transaction_count);
		} else {
			warn!("Error getting best block information");
		}
		Ok(())
	});

	let client = service.client();
	let display_block_import = client.import_notification_stream().for_each(|n| {
		info!(target: "substrate", "Imported #{} ({})", n.header.number(), n.hash);
		Ok(())
	});

	let txpool = service.extrinsic_pool();
	let display_txpool_import = txpool.import_notification_stream().for_each(move |_| {
		let status = txpool.light_status();
		telemetry!("txpool.import"; "mem_usage" => status.mem_usage, "count" => status.transaction_count, "sender" => status.senders);
		Ok(())
	});

	let informant_work = display_notifications.join3(display_block_import, display_txpool_import);
	handle.spawn(exit.until(informant_work).map(|_| ()));
}

