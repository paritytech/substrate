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
use network::SyncState;
use client::{backend::Backend, BlockchainEvents};
use log::{info, warn};

use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{Header, SaturatedConversion};

/// Spawn informant on the event loop
#[deprecated(note = "Please use informant::build instead, and then create the task manually")]
pub fn start<C>(service: &Service<C>, exit: ::exit_future::Exit, handle: TaskExecutor) where
	C: Components,
{
	handle.spawn(exit.until(build(service)).map(|_| ()));
}

/// Creates an informant in the form of a `Future` that must be polled regularly.
pub fn build<C>(service: &Service<C>) -> impl Future<Item = (), Error = ()>
where C: Components {
	let network = service.network();
	let client = service.client();
	let mut last_number = None;
	let mut last_update = time::Instant::now();

	let display_notifications = network.status().for_each(move |sync_status| {

		let info = client.info();
		let best_number = info.chain.best_number.saturated_into::<u64>();
		let best_hash = info.chain.best_hash;
		let speed = move || speed(best_number, last_number, last_update);
		last_update = time::Instant::now();
		let (status, target) = match (sync_status.sync.state, sync_status.sync.best_seen_block) {
			(SyncState::Idle, _) => ("Idle".into(), "".into()),
			(SyncState::Downloading, None) => (format!("Syncing{}", speed()), "".into()),
			(SyncState::Downloading, Some(n)) => (format!("Syncing{}", speed()), format!(", target=#{}", n)),
		};
		last_number = Some(best_number);
		let finalized_number: u64 = info.chain.finalized_number.saturated_into::<u64>();
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

		Ok(())
	});

	let client = service.client();
	let mut last = {
		let info = client.info();
		Some((info.chain.best_number, info.chain.best_hash))
	};

	let display_block_import = client.import_notification_stream().for_each(move |n| {
		// detect and log reorganizations.
		if let Some((ref last_num, ref last_hash)) = last {
			if n.header.parent_hash() != last_hash {
				let tree_route = ::client::blockchain::tree_route(
					#[allow(deprecated)]
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

	display_notifications.join(display_block_import)
		.map(|((), ())| ())
}

fn speed(best_number: u64, last_number: Option<u64>, last_update: time::Instant) -> String {
	let since_last_millis = last_update.elapsed().as_secs() * 1000;
	let since_last_subsec_millis = last_update.elapsed().subsec_millis() as u64;
	let speed = last_number
		.and_then(|num|
			(best_number.saturating_sub(num) * 10_000).checked_div(since_last_millis + since_last_subsec_millis))
		.map_or(0.0, |s| s as f64);

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
