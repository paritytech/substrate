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

use ansi_term::Colour;
use client::ClientInfo;
use log::info;
use network::SyncState;
use runtime_primitives::traits::{Block as BlockT, SaturatedConversion};
use service::NetworkStatus;
use std::{fmt, marker::PhantomData, time};

/// State of the informant display system.
pub struct InformantDisplay<B: BlockT> {
	/// Head of chain block number from the last time `display` has been called.
	/// `None` if `display` has never been called.
	// TODO: use `NumberFor<B>` instead of `u64`
	// https://github.com/paritytech/substrate/issues/2652
	last_number: Option<u64>,
	/// The last time `display` or `new` has been called.
	last_update: time::Instant,
	marker: PhantomData<B>,
}

impl<B: BlockT> InformantDisplay<B> {
	/// Builds a new informant display system.
	pub fn new() -> InformantDisplay<B> {
		InformantDisplay {
			last_number: None,
			last_update: time::Instant::now(),
			marker: PhantomData,
		}
	}

	/// Displays the informant by calling `info!`.
	pub fn display(&mut self, info: &ClientInfo<B>, net_status: NetworkStatus<B>) {
		let best_number = info.chain.best_number.saturated_into::<u64>();
		let best_hash = info.chain.best_hash;
		let speed = speed(best_number, self.last_number, self.last_update);
		self.last_update = time::Instant::now();
		let (status, target) = match (net_status.sync_state, net_status.best_seen_block) {
			(SyncState::Idle, _) => ("Idle".into(), "".into()),
			(SyncState::Downloading, None) => (format!("Syncing{}", speed), "".into()),
			(SyncState::Downloading, Some(n)) => (format!("Syncing{}", speed), format!(", target=#{}", n)),
		};
		self.last_number = Some(best_number);
		let finalized_number: u64 = info.chain.finalized_number.saturated_into::<u64>();
		info!(
			target: "substrate",
			"{}{} ({} peers), best: #{} ({}), finalized #{} ({}), ⬇ {} ⬆ {}",
			Colour::White.bold().paint(&status),
			target,
			Colour::White.bold().paint(format!("{}", net_status.num_connected_peers)),
			Colour::White.paint(format!("{}", best_number)),
			best_hash,
			Colour::White.paint(format!("{}", finalized_number)),
			info.chain.finalized_hash,
			TransferRateFormat(net_status.average_download_per_sec),
			TransferRateFormat(net_status.average_upload_per_sec),
		);
	}
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
