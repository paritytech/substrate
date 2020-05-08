// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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
use sc_client_api::{BlockchainEvents, UsageProvider};
use futures::prelude::*;
use log::{info, warn, trace};
use sp_runtime::traits::Header;
use sc_service::AbstractService;
use std::time::Duration;

mod display;

/// The format to print telemetry output in.
#[derive(PartialEq)]
pub enum OutputFormat {
	Coloured,
	Plain,
}

/// Creates an informant in the form of a `Future` that must be polled regularly.
pub fn build(service: &impl AbstractService, format: OutputFormat) -> impl futures::Future<Output = ()> {
	let client = service.client();
	let pool = service.transaction_pool();

	let mut display = display::InformantDisplay::new(format);

	let display_notifications = service
		.network_status(Duration::from_millis(5000))
		.for_each(move |(net_status, _)| {
			let info = client.usage_info();
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

	let client = service.client();
	let mut last_best = {
		let info = client.usage_info();
		Some((info.chain.best_number, info.chain.best_hash))
	};

	let display_block_import = client.import_notification_stream().for_each(move |n| {
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
						"♻️  Reorg on #{},{} to #{},{}, common ancestor #{},{}",
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

		info!(target: "substrate", "✨ Imported #{} ({})", Colour::White.bold().paint(format!("{}", n.header.number())), n.hash);
		future::ready(())
	});

	future::join(
		display_notifications,
		display_block_import
	).map(|_| ())
}
