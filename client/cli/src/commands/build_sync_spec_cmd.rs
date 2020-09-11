// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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

use crate::error;
use crate::params::{SharedParams, NetworkParams};
use crate::CliConfiguration;
use log::info;
use sc_network::config::build_multiaddr;
use sc_service::{config::{MultiaddrWithPeerId, NetworkConfiguration}, ChainSpec};
use structopt::StructOpt;
use std::io::Write;
use std::sync::Arc;
use sp_runtime::traits::Block as BlockT;
use sc_service::chain_ops::build_light_sync_state;
use sc_service::NetworkStatusSinks;
use futures::{FutureExt, StreamExt};
use futures::future::ready;

/// The `build-sync-spec` command used to build a chain spec that contains a light client state
/// so that light clients can sync faster.
#[derive(Debug, StructOpt)]
pub struct BuildSyncSpecCmd {
	/// Force raw genesis storage output.
	#[structopt(long = "raw")]
	pub raw: bool,

	/// Sync the chain using a full client first.
	#[structopt(long)]
	pub sync_first: bool,

	/// Disable adding the default bootnode to the specification.
	///
	/// By default the `/ip4/127.0.0.1/tcp/30333/p2p/NODE_PEER_ID` bootnode is added to the
	/// specification when no bootnode exists.
	#[structopt(long = "disable-default-bootnode")]
	pub disable_default_bootnode: bool,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub network_params: NetworkParams,
}

impl BuildSyncSpecCmd {
	/// Run the build-sync-spec command
	pub async fn run<B, CL>(
		&self,
		mut spec: Box<dyn ChainSpec>,
		network_config: NetworkConfiguration,
		client: Arc<CL>,
		network_status_sinks: NetworkStatusSinks<B>,
	) -> error::Result<()>
		where
			B: BlockT,
			CL: sp_blockchain::HeaderBackend<B>,
	{
        if self.sync_first {
            network_status_sinks.status_stream(std::time::Duration::from_secs(1)).filter(|status| {
                ready(status.sync_state == sc_network::SyncState::Idle && status.num_sync_peers > 0)
            }).into_future().map(drop).await;
        }

        let light_sync_state = build_light_sync_state(client)?;
        spec.set_light_sync_state(light_sync_state.to_serializable());

		info!("Building chain spec");
		let raw_output = self.raw;

		if spec.boot_nodes().is_empty() && !self.disable_default_bootnode {
			let keys = network_config.node_key.into_keypair()?;
			let peer_id = keys.public().into_peer_id();
			let addr = MultiaddrWithPeerId {
				multiaddr: build_multiaddr![Ip4([127, 0, 0, 1]), Tcp(30333u16)],
				peer_id,
			};
			spec.add_boot_node(addr)
		}

		let json = sc_service::chain_ops::build_spec(&*spec, raw_output)?;
		if std::io::stdout().write_all(json.as_bytes()).is_err() {
			let _ = std::io::stderr().write_all(b"Error writing to stdout\n");
		}
		Ok(())
	}
}

impl CliConfiguration for BuildSyncSpecCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn network_params(&self) -> Option<&NetworkParams> {
		Some(&self.network_params)
	}
}
