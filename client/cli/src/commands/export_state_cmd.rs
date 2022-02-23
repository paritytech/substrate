// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use crate::{
	error,
	params::{BlockNumberOrHash, DatabaseParams, PruningParams, SharedParams},
	CliConfiguration,
};
use clap::Parser;
use log::info;
use sc_client_api::{StorageProvider, UsageProvider};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use std::{fmt::Debug, io::Write, str::FromStr, sync::Arc};

/// The `export-state` command used to export the state of a given block into
/// a chain spec.
#[derive(Debug, Clone, Parser)]
pub struct ExportStateCmd {
	/// Block hash or number.
	#[clap(value_name = "HASH or NUMBER")]
	pub input: Option<BlockNumberOrHash>,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub pruning_params: PruningParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub database_params: DatabaseParams,
}

impl ExportStateCmd {
	/// Run the `export-state` command
	pub async fn run<B, BA, C>(
		&self,
		client: Arc<C>,
		mut input_spec: Box<dyn sc_service::ChainSpec>,
	) -> error::Result<()>
	where
		B: BlockT,
		C: UsageProvider<B> + StorageProvider<B, BA>,
		BA: sc_client_api::backend::Backend<B>,
		B::Hash: FromStr,
		<B::Hash as FromStr>::Err: Debug,
		<<B::Header as HeaderT>::Number as FromStr>::Err: Debug,
	{
		info!("Exporting raw state...");
		let block_id = self.input.as_ref().map(|b| b.parse()).transpose()?;
		let raw_state = sc_service::chain_ops::export_raw_state(client, block_id)?;
		input_spec.set_storage(raw_state);

		info!("Generating new chain spec...");
		let json = sc_service::chain_ops::build_spec(&*input_spec, true)?;
		if std::io::stdout().write_all(json.as_bytes()).is_err() {
			let _ = std::io::stderr().write_all(b"Error writing to stdout\n");
		}
		Ok(())
	}
}

impl CliConfiguration for ExportStateCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn pruning_params(&self) -> Option<&PruningParams> {
		Some(&self.pruning_params)
	}

	fn database_params(&self) -> Option<&DatabaseParams> {
		Some(&self.database_params)
	}
}
