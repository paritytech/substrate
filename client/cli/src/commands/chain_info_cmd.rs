// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use crate::{CliConfiguration, DatabaseParams, PruningParams, Result as CliResult, SharedParams};
use parity_scale_codec::{Decode, Encode};
use sc_client_api::{backend::Backend as BackendT, blockchain::HeaderBackend};
use sp_blockchain::Info;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use std::{fmt::Debug, io};

/// The `chain-info` subcommand used to output db meta columns information.
#[derive(Debug, Clone, clap::Parser)]
pub struct ChainInfoCmd {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub pruning_params: PruningParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub database_params: DatabaseParams,
}

/// Serializable `chain-info` subcommand output.
#[derive(Clone, Eq, PartialEq, Debug, Encode, Decode, serde::Serialize)]
struct ChainInfo<B: BlockT> {
	/// Best block hash.
	best_hash: B::Hash,
	/// Best block number.
	best_number: <<B as BlockT>::Header as HeaderT>::Number,
	/// Genesis block hash.
	genesis_hash: B::Hash,
	/// The head of the finalized chain.
	finalized_hash: B::Hash,
	/// Last finalized block number.
	finalized_number: <<B as BlockT>::Header as HeaderT>::Number,
}

impl<B: BlockT> From<Info<B>> for ChainInfo<B> {
	fn from(info: Info<B>) -> Self {
		ChainInfo::<B> {
			best_hash: info.best_hash,
			best_number: info.best_number,
			genesis_hash: info.genesis_hash,
			finalized_hash: info.finalized_hash,
			finalized_number: info.finalized_number,
		}
	}
}

impl ChainInfoCmd {
	/// Run the `chain-info` subcommand
	pub fn run<B>(&self, config: &sc_service::Configuration) -> CliResult<()>
	where
		B: BlockT,
	{
		let db_config = sc_client_db::DatabaseSettings {
			state_cache_size: config.state_cache_size,
			state_cache_child_ratio: config.state_cache_child_ratio.map(|v| (v, 100)),
			state_pruning: config.state_pruning.clone(),
			source: config.database.clone(),
			blocks_pruning: config.blocks_pruning,
		};
		let backend = sc_service::new_db_backend::<B>(db_config)?;
		let info: ChainInfo<B> = backend.blockchain().info().into();
		let mut out = io::stdout();
		serde_json::to_writer_pretty(&mut out, &info)
			.map_err(|e| format!("Error writing JSON: {}", e))?;
		Ok(())
	}
}

impl CliConfiguration for ChainInfoCmd {
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
