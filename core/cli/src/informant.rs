// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

use ansi_term::Colour;
use std::time::{Duration, Instant};
use futures::{Future, Stream};
use service::{Service, Components};
use tokio::runtime::TaskExecutor;
use tokio::timer::Interval;
use sysinfo::{get_current_pid, ProcessExt, System, SystemExt};
use network::{SyncState, SyncProvider};
use client::BlockchainEvents;
use runtime_primitives::traits::{Header, As};

const TIMER_INTERVAL_MS: u64 = 5000;

/// Spawn informant on the event loop
pub fn start<C>(service: &Service<C>, exit: ::exit_future::Exit, handle: TaskExecutor) where
	C: Components,
{
	let interval = Interval::new(Instant::now(), Duration::from_millis(TIMER_INTERVAL_MS));

	let network = service.network();
	let client = service.client();
	let txpool = service.transaction_pool();
	let mut last_number = None;

	let mut sys = System::new();
	let self_pid = get_current_pid();

	let display_notifications = interval.map_err(|e| debug!("Timer error: {:?}", e)).for_each(move |_| {
		let sync_status = network.status();

		if let Ok(best_block) = client.best_block_header() {
			let hash = best_block.hash();
			let num_peers = sync_status.num_peers;
			let best_number: u64 = best_block.number().as_();
			let speed = move || speed(best_number, last_number);
			let (status, target) = match (sync_status.sync.state, sync_status.sync.best_seen_block) {
				(SyncState::Idle, _) => ("Idle".into(), "".into()),
				(SyncState::Downloading, None) => (format!("Syncing{}", speed()), "".into()),
				(SyncState::Downloading, Some(n)) => (format!("Syncing{}", speed()), format!(", target=#{}", n)),
			};
			last_number = Some(best_number);
			let txpool_status = txpool.status();
			info!(
				target: "substrate",
				"{}{} ({} peers), best: #{} ({})",
				Colour::White.bold().paint(&status),
				target,
				Colour::White.bold().paint(format!("{}", sync_status.num_peers)),
				Colour::White.paint(format!("{}", best_number)),
				hash
			);

			// get cpu usage and memory usage of this process
			let (cpu_usage, memory) = if sys.refresh_process(self_pid) {
				let proc = sys.get_process(self_pid).expect("Above refresh_process succeeds, this should be Some(), qed");
				(proc.cpu_usage(), proc.memory())
			} else { (0.0, 0) };

			telemetry!(
				"system.interval";
				"status" => format!("{}{}", status, target),
				"peers" => num_peers,
				"height" => best_number,
				"best" => ?hash,
				"txcount" => txpool_status.ready,
				"cpu" => cpu_usage,
				"memory" => memory
			);
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

	let txpool = service.transaction_pool();
	let display_txpool_import = txpool.import_notification_stream().for_each(move |_| {
		let status = txpool.status();
		telemetry!("txpool.import"; "ready" => status.ready, "future" => status.future);
		Ok(())
	});

	let informant_work = display_notifications.join3(display_block_import, display_txpool_import);
	handle.spawn(exit.until(informant_work).map(|_| ()));
}

fn speed(best_number: u64, last_number: Option<u64>) -> String {
	let speed = match last_number {
		Some(num) => (best_number.saturating_sub(num) * 10_000 / TIMER_INTERVAL_MS) as f64,
		None => 0.0
	};

	if speed < 1.0 {
		"".into()
	} else {
		format!(" {:4.1} bps", speed / 10.0)
	}
}
