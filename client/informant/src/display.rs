// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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
use sc_client_api::ClientInfo;
use log::info;
use sc_network::SyncState;
use sp_runtime::traits::{Block as BlockT, CheckedDiv, NumberFor, Zero, Saturating};
use sc_service::NetworkStatus;
use std::{convert::{TryFrom, TryInto}, fmt};
use wasm_timer::Instant;
use crate::OutputFormat;

/// State of the informant display system.
///
/// This is the system that handles the line that gets regularly printed and that looks something
/// like:
///
/// > Syncing  5.4 bps, target=#531028 (4 peers), best: #90683 (0x4ca8…51b8),
/// >  finalized #360 (0x6f24…a38b), ⬇ 5.5kiB/s ⬆ 0.9kiB/s
///
/// # Usage
///
/// Call `InformantDisplay::new` to initialize the state, then regularly call `display` with the
/// information to display.
///
pub struct InformantDisplay<B: BlockT> {
	/// Head of chain block number from the last time `display` has been called.
	/// `None` if `display` has never been called.
	last_number: Option<NumberFor<B>>,
	/// The last time `display` or `new` has been called.
	last_update: Instant,
	/// The format to print output in.
	format: OutputFormat,
}

impl<B: BlockT> InformantDisplay<B> {
	/// Builds a new informant display system.
	pub fn new(format: OutputFormat) -> InformantDisplay<B> {
		InformantDisplay {
			last_number: None,
			last_update: Instant::now(),
			format,
		}
	}

	/// Displays the informant by calling `info!`.
	pub fn display(&mut self, info: &ClientInfo<B>, net_status: NetworkStatus<B>) {
		let best_number = info.chain.best_number;
		let best_hash = info.chain.best_hash;
		let finalized_number = info.chain.finalized_number;
		let num_connected_peers = net_status.num_connected_peers;
		let speed = speed::<B>(best_number, self.last_number, self.last_update);
		self.last_update = Instant::now();
		self.last_number = Some(best_number);

		let (status, target) = match (net_status.sync_state, net_status.best_seen_block) {
			(SyncState::Idle, _) => ("💤 Idle".into(), "".into()),
			(SyncState::Downloading, None) => (format!("⚙️  Preparing{}", speed), "".into()),
			(SyncState::Downloading, Some(n)) => (format!("⚙️  Syncing{}", speed), format!(", target=#{}", n)),
		};

		if self.format == OutputFormat::Coloured {
			info!(
				target: "substrate",
				"{}{} ({} peers), best: #{} ({}), finalized #{} ({}), {} {}",
				Colour::White.bold().paint(&status),
				target,
				Colour::White.bold().paint(format!("{}", num_connected_peers)),
				Colour::White.bold().paint(format!("{}", best_number)),
				best_hash,
				Colour::White.bold().paint(format!("{}", finalized_number)),
				info.chain.finalized_hash,
				Colour::Green.paint(format!("⬇ {}", TransferRateFormat(net_status.average_download_per_sec))),
				Colour::Red.paint(format!("⬆ {}", TransferRateFormat(net_status.average_upload_per_sec))),
			);
		} else {
			info!(
				target: "substrate",
				"{}{} ({} peers), best: #{} ({}), finalized #{} ({}), ⬇ {} ⬆ {}",
				status,
				target,
				num_connected_peers,
				best_number,
				best_hash,
				finalized_number,
				info.chain.finalized_hash,
				TransferRateFormat(net_status.average_download_per_sec),
				TransferRateFormat(net_status.average_upload_per_sec),
			);
		}
	}
}

/// Calculates `(best_number - last_number) / (now - last_update)` and returns a `String`
/// representing the speed of import.
fn speed<B: BlockT>(
	best_number: NumberFor<B>,
	last_number: Option<NumberFor<B>>,
	last_update: Instant
) -> String {
	// Number of milliseconds elapsed since last time.
	let elapsed_ms = {
		let elapsed = last_update.elapsed();
		let since_last_millis = elapsed.as_secs() * 1000;
		let since_last_subsec_millis = elapsed.subsec_millis() as u64;
		since_last_millis + since_last_subsec_millis
	};

	// Number of blocks that have been imported since last time.
	let diff = match last_number {
		None => return String::new(),
		Some(n) => best_number.saturating_sub(n)
	};

	if let Ok(diff) = TryInto::<u128>::try_into(diff) {
		// If the number of blocks can be converted to a regular integer, then it's easy: just
		// do the math and turn it into a `f64`.
		let speed = diff.saturating_mul(10_000).checked_div(u128::from(elapsed_ms))
			.map_or(0.0, |s| s as f64) / 10.0;
		format!(" {:4.1} bps", speed)

	} else {
		// If the number of blocks can't be converted to a regular integer, then we need a more
		// algebraic approach and we stay within the realm of integers.
		let one_thousand = NumberFor::<B>::from(1_000);
		let elapsed = NumberFor::<B>::from(
			<u32 as TryFrom<_>>::try_from(elapsed_ms).unwrap_or(u32::max_value())
		);

		let speed = diff.saturating_mul(one_thousand).checked_div(&elapsed)
			.unwrap_or_else(Zero::zero);
		format!(" {} bps", speed)
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
