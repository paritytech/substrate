// Copyright 2020 Parity Technologies (UK) Ltd.
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

use structopt::StructOpt;
use sc_service::{Configuration, PruningMode};

use crate::error;

/// Parameters to define the pruning mode
#[derive(Debug, StructOpt, Clone)]
pub struct PruningParams {
	/// Specify the state pruning mode, a number of blocks to keep or 'archive'.
	///
	/// Default is to keep all block states if the node is running as a
	/// validator (i.e. 'archive'), otherwise state is only kept for the last
	/// 256 blocks.
	#[structopt(long = "pruning", value_name = "PRUNING_MODE")]
	pub pruning: Option<String>,
}

impl PruningParams {
	/// Put block pruning CLI params into `config` object.
	pub fn update_config(
		&self,
		mut config: &mut Configuration,
		role: sc_service::Roles,
		unsafe_pruning: bool,
	) -> error::Result<()> {
		// by default we disable pruning if the node is an authority (i.e.
		// `ArchiveAll`), otherwise we keep state for the last 256 blocks. if the
		// node is an authority and pruning is enabled explicitly, then we error
		// unless `unsafe_pruning` is set.
		config.pruning = match &self.pruning {
			Some(ref s) if s == "archive" => PruningMode::ArchiveAll,
			None if role == sc_service::Roles::AUTHORITY => PruningMode::ArchiveAll,
			None => PruningMode::default(),
			Some(s) => {
				if role == sc_service::Roles::AUTHORITY && !unsafe_pruning {
					return Err(error::Error::Input(
						"Validators should run with state pruning disabled (i.e. archive). \
						You can ignore this check with `--unsafe-pruning`.".to_string()
					));
				}

				PruningMode::keep_blocks(s.parse()
					.map_err(|_| error::Error::Input("Invalid pruning mode specified".to_string()))?
				)
			},
		};

		Ok(())
	}
}
