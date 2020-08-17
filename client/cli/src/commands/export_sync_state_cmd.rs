// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
use sc_service::ChainSpec;
use structopt::StructOpt;
use std::io::Write;
use std::sync::Arc;
use std::task::Poll;
use sp_runtime::traits::Block as BlockT;

/// Export the chain spec containing a state to sync the light client.
#[derive(Debug, StructOpt)]
pub struct ExportSyncStateCmd {
	/// Force raw genesis storage output in the chain spec.
	#[structopt(long = "raw")]
	pub raw: bool,
	
	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub network_params: NetworkParams,
}

impl ExportSyncStateCmd {
	/// Run the `export-sync-state` command
	pub async fn run<B, CL, BA, SO>(
		&self,
		mut spec: Box<dyn ChainSpec>,
		client: Arc<CL>,
		backend: Arc<BA>,
		mut sync_oracle: SO,
	) -> error::Result<()>
		where
			B: BlockT,
			CL: sp_blockchain::HeaderBackend<B>,
			BA: sc_service::MaybeChtRootStorageProvider<B>,
			SO: sp_consensus::SyncOracle,
	{
		futures::future::poll_fn(|_| {
			match sync_oracle.is_major_syncing() || sync_oracle.is_offline() {
				true => Poll::Pending,
				false => Poll::Ready(())
			}
		}).await;

		info!("Building chain spec");

		let light_sync_state = sc_service::build_light_sync_state(client, backend)
			.map_err(|err| err.to_string())?;

		spec.set_light_sync_state(light_sync_state.to_serializable());

		let json = sc_service::chain_ops::build_spec(&*spec, self.raw)?;
		if std::io::stdout().write_all(json.as_bytes()).is_err() {
			let _ = std::io::stderr().write_all(b"Error writing to stdout\n");
		}
		Ok(())
	}
}

impl CliConfiguration for ExportSyncStateCmd {
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
