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
use crate::params::{GenericNumber, PruningParams, SharedParams};
use crate::CliConfiguration;
use sc_service::chain_ops::revert_chain;
use sp_runtime::traits::{Block as BlockT, Header as HeaderT};
use std::fmt::Debug;
use std::str::FromStr;
use std::sync::Arc;
use structopt::StructOpt;
use sc_client_api::{Backend, UsageProvider};

/// The `revert` command used revert the chain to a previous state.
#[derive(Debug, StructOpt)]
pub struct RevertCmd {
	/// Number of blocks to revert.
	#[structopt(default_value = "256")]
	pub num: GenericNumber,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub pruning_params: PruningParams,
}

impl RevertCmd {
	/// Run the revert command
	pub async fn run<B, BA, C>(
		&self,
		client: Arc<C>,
		backend: Arc<BA>,
	) -> error::Result<()>
	where
		B: BlockT,
		BA: Backend<B>,
		C: UsageProvider<B>,
		<<<B as BlockT>::Header as HeaderT>::Number as FromStr>::Err: Debug,
	{
		let blocks = self.num.parse()?;
		revert_chain(client, backend, blocks)?;

		Ok(())
	}
}

impl CliConfiguration for RevertCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn pruning_params(&self) -> Option<&PruningParams> {
		Some(&self.pruning_params)
	}
}
