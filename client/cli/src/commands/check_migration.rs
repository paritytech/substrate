// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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
	params::{PruningParams, SharedParams},
	CliConfiguration,
};
use sc_client_api::MigrationStateBackend;
use std::{fmt::Debug, sync::Arc};
use structopt::StructOpt;

/// The `check-migration` command used to check migration status.
#[derive(Debug, StructOpt, Clone)]
pub struct CheckMigrationCmd {
	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub pruning_params: PruningParams,

	#[allow(missing_docs)]
	#[structopt(flatten)]
	pub shared_params: SharedParams,
}

impl CheckMigrationCmd {
	/// Run the state migration check command.
	pub async fn run<C>(&self, client: Arc<C>) -> error::Result<()>
	where
		C: MigrationStateBackend + Send + Sync + 'static,
	{
		let start = std::time::Instant::now();
		let (nb_top, nb_child) = client.remaining_key_to_migrate()?;
		println!("Remaining {} keys in top storage.", nb_top);
		println!("Remaining {} keys in all children storage.", nb_child);
		println!("Completed in {} ms.", start.elapsed().as_millis());

		Ok(())
	}
}

impl CliConfiguration for CheckMigrationCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}

	fn pruning_params(&self) -> Option<&PruningParams> {
		Some(&self.pruning_params)
	}
}
