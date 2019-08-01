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

use client::{backend::Backend, BlockchainEvents};
use futures::{Future, Stream};
use futures03::{StreamExt as _, TryStreamExt as _};
use log::{info, warn};
use sr_primitives::{generic::BlockId, traits::Header};
use service::{Service, Components};
use tokio::runtime::TaskExecutor;

mod display;

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
	let client = service.client();

	let mut display = display::InformantDisplay::new();

	let display_notifications = service.network_status().for_each(move |(net_status, _)| {
		let info = client.info();
		display.display(&info, net_status);
		Ok(())
	});

	let client = service.client();
	let mut last_best = {
		let info = client.info();
		Some((info.chain.best_number, info.chain.best_hash))
	};

	let display_block_import = client.import_notification_stream().map(|v| Ok::<_, ()>(v)).compat().for_each(move |n| {
		// detect and log reorganizations.
		if let Some((ref last_num, ref last_hash)) = last_best {
			if n.header.parent_hash() != last_hash && n.is_new_best  {
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

		if n.is_new_best {
			last_best = Some((n.header.number().clone(), n.hash.clone()));
		}

		info!(target: "substrate", "Imported #{} ({})", n.header.number(), n.hash);
		Ok(())
	});

	display_notifications.join(display_block_import)
		.map(|((), ())| ())
}
