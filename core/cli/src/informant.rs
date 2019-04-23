// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use std::fmt;
use std::time;
use futures::{Future, Stream};
use service::{Service, Components};
use tokio::runtime::TaskExecutor;
use sysinfo::{get_current_pid, ProcessExt, System, SystemExt};
use network::{SyncState, SyncProvider};
use client::{backend::Backend, BlockchainEvents};
use substrate_telemetry::{telemetry, SUBSTRATE_INFO};
use log::{info, warn};

use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Header, As};

/// Spawn informant on the event loop
pub fn start<C>(service: &Service<C>, exit: ::exit_future::Exit, handle: TaskExecutor) where
	C: Components,
{
	let network = service.network();
	let client = service.client();
	let txpool = service.transaction_pool();
	let mut last_number = None;
	let mut last_update = time::Instant::now();

	let mut sys = System::new();
	let self_pid = get_current_pid();

	let display_notifications = network.status().for_each(move |sync_status| {

		if let Ok(info) = client.info() {
			let best_number: u64 = info.chain.best_number.as_();
			let best_hash = info.chain.best_hash;
			let num_peers = sync_status.num_peers;
			let speed = move || speed(best_number, last_number, last_update);
			last_update = time::Instant::now();
			let (status, target) = match (sync_status.sync.state, sync_status.sync.best_seen_block) {
				(SyncState::Idle, _) => ("Idle".into(), "".into()),
				(SyncState::Downloading, None) => (format!("Syncing{}", speed()), "".into()),
				(SyncState::Downloading, Some(n)) => (format!("Syncing{}", speed()), format!(", target=#{}", n)),
			};
			last_number = Some(best_number);
			let txpool_status = txpool.status();
			let finalized_number: u64 = info.chain.finalized_number.as_();
			let bandwidth_download = network.average_download_per_sec();
			let bandwidth_upload = network.average_upload_per_sec();
			info!(
				target: "substrate",
				"{}{} ({} peers), best: #{} ({}), finalized #{} ({}), ⬇ {} ⬆ {}",
				Colour::White.bold().paint(&status),
				target,
				Colour::White.bold().paint(format!("{}", sync_status.num_peers)),
				Colour::White.paint(format!("{}", best_number)),
				best_hash,
				Colour::White.paint(format!("{}", finalized_number)),
				info.chain.finalized_hash,
				TransferRateFormat(bandwidth_download),
				TransferRateFormat(bandwidth_upload),
			);

			let backend = (*client).backend();
			let used_state_cache_size = match backend.used_state_cache_size(){
				Some(size) => size,
				None => 0,
			};

			// get cpu usage and memory usage of this process
			let (cpu_usage, memory) = if sys.refresh_process(self_pid) {
				let proc = sys.get_process(self_pid).expect("Above refresh_process succeeds, this should be Some(), qed");
				(proc.cpu_usage(), proc.memory())
			} else { (0.0, 0) };

			let network_state = network.network_state();

			telemetry!(
				SUBSTRATE_INFO;
				"system.interval";
				"network_state" => network_state,
				"status" => format!("{}{}", status, target),
				"peers" => num_peers,
				"height" => best_number,
				"best" => ?best_hash,
				"txcount" => txpool_status.ready,
				"cpu" => cpu_usage,
				"memory" => memory,
				"finalized_height" => finalized_number,
				"finalized_hash" => ?info.chain.finalized_hash,
				"bandwidth_download" => bandwidth_download,
				"bandwidth_upload" => bandwidth_upload,
				"used_state_cache_size" => used_state_cache_size,
			);
		} else {
			warn!("Error getting best block information");
		}

		Ok(())
	});

	let client = service.client();
	let mut last = match client.info() {
		Ok(info) => Some((info.chain.best_number, info.chain.best_hash)),
		Err(e) => { warn!("Error getting best block information: {:?}", e); None }
	};

	let display_block_import = client.import_notification_stream().for_each(move |n| {
		// detect and log reorganizations.
		if let Some((ref last_num, ref last_hash)) = last {
			if n.header.parent_hash() != last_hash {
				let tree_route = ::client::blockchain::tree_route(
					client.backend().blockchain(),
					BlockId::Hash(last_hash.clone()),
					BlockId::Hash(n.hash),
				);

				match tree_route {
					Ok(ref t) if !t.retracted().is_empty() => info!(
						"Reorg from #{},{} to #{},{}, common ancestor #{},{}",
						last_num, last_hash,
						n.header.number(), n.hash,
						t.common_block().number, t.common_block().hash,
					),
					Ok(_) => {},
					Err(e) => warn!("Error computing tree route: {}", e),
				}
			}
		}

		last = Some((n.header.number().clone(), n.hash.clone()));

		info!(target: "substrate", "Imported #{} ({})", n.header.number(), n.hash);
		Ok(())
	});

	let txpool = service.transaction_pool();
	let display_txpool_import = txpool.import_notification_stream().for_each(move |_| {
		let status = txpool.status();
		telemetry!(SUBSTRATE_INFO; "txpool.import"; "ready" => status.ready, "future" => status.future);
		Ok(())
	});

	let informant_work = display_notifications.join3(display_block_import, display_txpool_import);
	handle.spawn(exit.until(informant_work).map(|_| ()));
}

fn speed(best_number: u64, last_number: Option<u64>, last_update: time::Instant) -> String {
	let since_last_millis = last_update.elapsed().as_secs() * 1000;
	let since_last_subsec_millis = last_update.elapsed().subsec_millis() as u64;
	let speed = match last_number {
		Some(num) => (best_number.saturating_sub(num) * 10_000 / (since_last_millis + since_last_subsec_millis)) as f64,
		None => 0.0
	};

	if speed < 1.0 {
		"".into()
	} else {
		format!(" {:4.1} bps", speed / 10.0)
	}
}

/// Contains a number of bytes per second. Implements `fmt::Display` and shows this number of bytes
/// per second in a nice way.
struct TransferRateFormat(u64);
impl fmt::Display for TransferRateFormat {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		// Special case 0.
		if self.0 == 0 {
			return write!(f, "0")
		}

		// Under 0.1 kiB, display plain bytes.
		if self.0 < 100 {
			return write!(f, "{} B/s", self.0)
		}

		// Under 1.0 MiB/sec, display the value in kiB/sec.
		if self.0 < 1024 * 1024 {
			return write!(f, "{:.1}kiB/s", self.0 as f64 / 1024.0)
		}

		write!(f, "{:.1}MiB/s", self.0 as f64 / (1024.0 * 1024.0))
	}
}
