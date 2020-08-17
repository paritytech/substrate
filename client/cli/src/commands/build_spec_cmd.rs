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
use crate::Role;
use log::info;
use sc_network::config::build_multiaddr;
use sc_service::{config::{MultiaddrWithPeerId, NetworkConfiguration}, ChainSpec};
use structopt::StructOpt;
use std::io::Write;
use std::sync::Arc;
use sp_runtime::traits::Block as BlockT;
use sc_service::chain_ops::{MaybeChtRootStorageProvider, build_light_sync_state};
use sc_service::NetworkStatusSinks;
use futures::stream::StreamExt;
use futures::future::ready;

/// The `build-spec` command used to build a specification.
#[derive(Debug, StructOpt)]
pub struct BuildSpecCmd {
	/// Force raw genesis storage output.
	#[structopt(long = "raw")]
	pub raw: bool,

	/// Sync the chain using a light client, and export the state in the chain spec so that other
	/// light clients can sync faster.
	#[structopt(long = "export-sync-state")]
	pub export_sync_state: bool,

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

impl BuildSpecCmd {
	/// Run the build-spec command
	pub fn run(
		&self,
		mut spec: Box<dyn ChainSpec>,
		network_config: NetworkConfiguration,
	) -> error::Result<()> {
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

	/// Sync the light client, export the sync state and run the command as per normal.
	pub async fn run_export_sync_state<B, CL, BA>(
		&self,
		mut spec: Box<dyn ChainSpec>,
		network_config: NetworkConfiguration,
		client: Arc<CL>,
		backend: Arc<BA>,
		network_status_sinks: NetworkStatusSinks<B>,
	) -> error::Result<()>
		where
			B: BlockT,
			CL: sp_blockchain::HeaderBackend<B>,
			BA: MaybeChtRootStorageProvider<B>,
	{
		network_status_sinks.network_status(std::time::Duration::from_secs(1)).take_while(|(status, _)| {
			ready(if status.sync_state == sc_network::SyncState::Idle && status.num_sync_peers > 0 {
				false
			} else {
				true
			})
		}).for_each(|_| ready(())).await;

		let light_sync_state = build_light_sync_state(client, backend)?;
		spec.set_light_sync_state(light_sync_state.to_serializable());

		self.run(spec, network_config)
	}
}

impl CliConfiguration for BuildSpecCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn network_params(&self) -> Option<&NetworkParams> {
		Some(&self.network_params)
	}

	fn role(&self, _is_dev: bool) -> error::Result<Role> {
		Ok(Role::Light)
	}
}
