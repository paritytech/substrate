// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Console informant. Prints sync progress and block events. Runs on the calling thread.

use ansi_term::Colour;
use futures::prelude::*;
use log::{info, trace, warn};
use parity_util_mem::MallocSizeOf;
use sc_client_api::{BlockchainEvents, UsageProvider};
use sc_network::{network_state::NetworkState, NetworkStatus};
use sp_blockchain::HeaderMetadata;
use sp_runtime::traits::{Block as BlockT, Header};
use sp_transaction_pool::TransactionPool;
use sp_utils::{status_sinks, mpsc::tracing_unbounded};
use std::{fmt::Display, sync::Arc, time::Duration, collections::VecDeque};

mod display;

/// The format to print telemetry output in.
#[derive(Clone, Debug)]
pub struct OutputFormat {
	/// Enable color output in logs. True by default.
	pub enable_color: bool,
	/// Defines the informant's prefix for the logs. An empty string by default.
	///
	/// By default substrate will show logs without a prefix. Example:
	///
	/// ```text
	/// 2020-05-28 15:11:06 ✨ Imported #2 (0xc21c…2ca8)
	/// 2020-05-28 15:11:07 💤 Idle (0 peers), best: #2 (0xc21c…2ca8), finalized #0 (0x7299…e6df), ⬇ 0 ⬆ 0
	/// ```
	///
	/// But you can define a prefix by setting this string. This will output:
	///
	/// ```text
	/// 2020-05-28 15:11:06 ✨ [Prefix] Imported #2 (0xc21c…2ca8)
	/// 2020-05-28 15:11:07 💤 [Prefix] Idle (0 peers), best: #2 (0xc21c…2ca8), finalized #0 (0x7299…e6df), ⬇ 0 ⬆ 0
	/// ```
	pub prefix: String,
}

impl Default for OutputFormat {
	fn default() -> Self {
		Self {
			enable_color: true,
			prefix: String::new(),
		}
	}
}

/// Marker trait for a type that implements `TransactionPool` and `MallocSizeOf` on `not(target_os = "unknown")`.
#[cfg(target_os = "unknown")]
pub trait TransactionPoolAndMaybeMallogSizeOf: TransactionPool {}

/// Marker trait for a type that implements `TransactionPool` and `MallocSizeOf` on `not(target_os = "unknown")`.
#[cfg(not(target_os = "unknown"))]
pub trait TransactionPoolAndMaybeMallogSizeOf: TransactionPool + MallocSizeOf {}

#[cfg(target_os = "unknown")]
impl<T: TransactionPool> TransactionPoolAndMaybeMallogSizeOf for T {}

#[cfg(not(target_os = "unknown"))]
impl<T: TransactionPool + MallocSizeOf> TransactionPoolAndMaybeMallogSizeOf for T {}

/// Builds the informant and returns a `Future` that drives the informant.
pub fn build<B: BlockT, C>(
	client: Arc<C>,
	network_status_sinks: Arc<status_sinks::StatusSinks<(NetworkStatus<B>, NetworkState)>>,
	pool: Arc<impl TransactionPoolAndMaybeMallogSizeOf>,
	format: OutputFormat,
) -> impl futures::Future<Output = ()>
where
	C: UsageProvider<B> + HeaderMetadata<B> + BlockchainEvents<B>,
	<C as HeaderMetadata<B>>::Error: Display,
{
	let mut display = display::InformantDisplay::new(format.clone());

	let client_1 = client.clone();
	let (network_status_sink, network_status_stream) = tracing_unbounded("mpsc_network_status");
	network_status_sinks.push(Duration::from_millis(5000), network_status_sink);

	let display_notifications = network_status_stream
		.for_each(move |(net_status, _)| {
			let info = client_1.usage_info();
			if let Some(ref usage) = info.usage {
				trace!(target: "usage", "Usage statistics: {}", usage);
			} else {
				trace!(
					target: "usage",
					"Usage statistics not displayed as backend does not provide it",
				)
			}
			#[cfg(not(target_os = "unknown"))]
			trace!(
				target: "usage",
				"Subsystems memory [txpool: {} kB]",
				parity_util_mem::malloc_size(&*pool) / 1024,
			);
			display.display(&info, net_status);
			future::ready(())
		});

	future::join(
		display_notifications,
		display_block_import(client, format.prefix),
	).map(|_| ())
}

fn display_block_import<B: BlockT, C>(
	client: Arc<C>,
	prefix: String,
) -> impl Future<Output = ()>
where
	C: UsageProvider<B> + HeaderMetadata<B> + BlockchainEvents<B>,
	<C as HeaderMetadata<B>>::Error: Display,
{
	let mut last_best = {
		let info = client.usage_info();
		Some((info.chain.best_number, info.chain.best_hash))
	};

	// Hashes of the last blocks we have seen at import.
	let mut last_blocks = VecDeque::new();
	let max_blocks_to_track = 100;

	client.import_notification_stream().for_each(move |n| {
		// detect and log reorganizations.
		if let Some((ref last_num, ref last_hash)) = last_best {
			if n.header.parent_hash() != last_hash && n.is_new_best  {
				let maybe_ancestor = sp_blockchain::lowest_common_ancestor(
					&*client,
					last_hash.clone(),
					n.hash,
				);

				match maybe_ancestor {
					Ok(ref ancestor) if ancestor.hash != *last_hash => info!(
						"♻️  {}Reorg on #{},{} to #{},{}, common ancestor #{},{}",
						prefix,
						Colour::Red.bold().paint(format!("{}", last_num)), last_hash,
						Colour::Green.bold().paint(format!("{}", n.header.number())), n.hash,
						Colour::White.bold().paint(format!("{}", ancestor.number)), ancestor.hash,
					),
					Ok(_) => {},
					Err(e) => warn!("Error computing tree route: {}", e),
				}
			}
		}

		if n.is_new_best {
			last_best = Some((n.header.number().clone(), n.hash.clone()));
		}


		// If we already printed a message for a given block recently,
		// we should not print it again.
		if !last_blocks.contains(&n.hash) {
			last_blocks.push_back(n.hash.clone());

			if last_blocks.len() > max_blocks_to_track {
				last_blocks.pop_front();
			}

			info!(
				target: "substrate",
				"✨ {}Imported #{} ({})",
				prefix,
				Colour::White.bold().paint(format!("{}", n.header.number())),
				n.hash,
			);
		}

		future::ready(())
	})
}
