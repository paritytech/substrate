// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

use parity_scale_codec::{Decode, Encode};
use crate::{CliConfiguration, PruningParams, Result as CliResult, SharedParams};
use sc_client_api::{backend::Backend as BackendT, blockchain::HeaderBackend};
use sc_client_db::Backend;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use std::{fmt::Debug, io, sync::Arc};

/// The `blockchain-info` subcommand used to output db meta columns information.
#[derive(Debug, Clone, clap::Parser)]
pub struct BlockchainInfoCmd {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub pruning_params: PruningParams,

	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,
}

/// Serializable `blockchain-info` subcommand output.
#[derive(Clone, Eq, PartialEq, Debug, Encode, Decode, serde::Serialize)]
struct BlockchainInfo<B: BlockT> {
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

impl BlockchainInfoCmd {
	/// Run the `blockchain-info` subcommand
	pub async fn run<B>(&self, backend: Arc<Backend<B>>) -> CliResult<()>
	where
		B: BlockT,
	{
		let blockchain_info = backend.blockchain().info();
		let info = BlockchainInfo::<B> {
			best_hash: blockchain_info.best_hash,
			best_number: blockchain_info.best_number,
			genesis_hash: blockchain_info.genesis_hash,
			finalized_hash: blockchain_info.finalized_hash,
			finalized_number: blockchain_info.finalized_number,
		};
		let mut out = io::stdout();
		serde_json::to_writer_pretty(&mut out, &info).map_err(|e| format!("Error writing JSON: {}", e))?;
		Ok(())
	}
}

impl CliConfiguration for BlockchainInfoCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn pruning_params(&self) -> Option<&PruningParams> {
		Some(&self.pruning_params)
	}
}
