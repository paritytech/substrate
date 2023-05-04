// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
use clap::Args;
use sc_service::{BlocksPruning, PruningMode};

/// Parameters to define the pruning mode
#[derive(Debug, Clone, Args)]
pub struct PruningParams {
	/// Specify the state pruning mode.
	/// This mode specifies when the block's state (ie, storage)
	/// should be pruned (ie, removed) from the database.
	/// This setting can only be set on the first creation of the database. Every subsequent run
	/// will load the pruning mode from the database and will error if the stored mode doesn't
	/// match this CLI value. It is fine to drop this CLI flag for subsequent runs.
	/// Possible values:
	///  - archive: Keep the state of all blocks.
	///  - 'archive-canonical' Keep only the state of finalized blocks.
	///  - number Keep the state of the last number of finalized blocks.
	/// [default: 256]
	#[arg(alias = "pruning", long, value_name = "PRUNING_MODE")]
	pub state_pruning: Option<DatabasePruningMode>,

	/// Specify the blocks pruning mode.
	/// This mode specifies when the block's body (including justifications)
	/// should be pruned (ie, removed) from the database.
	/// Possible values:
	///  - 'archive' Keep all blocks.
	///  - 'archive-canonical' Keep only finalized blocks.
	///  - number
	///  Keep the last `number` of finalized blocks.
	#[arg(
		alias = "keep-blocks",
		long,
		value_name = "PRUNING_MODE",
		default_value = "archive-canonical"
	)]
	pub blocks_pruning: DatabasePruningMode,
}

impl PruningParams {
	/// Get the pruning value from the parameters
	pub fn state_pruning(&self) -> error::Result<Option<PruningMode>> {
		Ok(self.state_pruning.map(|v| v.into()))
	}

	/// Get the block pruning value from the parameters
	pub fn blocks_pruning(&self) -> error::Result<BlocksPruning> {
		Ok(self.blocks_pruning.into())
	}
}

/// Specifies the pruning mode of the database.
///
/// This specifies when the block's data (either state via `--state-pruning`
/// or body via `--blocks-pruning`) should be pruned (ie, removed) from
/// the database.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum DatabasePruningMode {
	/// Keep the data of all blocks.
	Archive,
	/// Keep only the data of finalized blocks.
	ArchiveCanonical,
	/// Keep the data of the last number of finalized blocks.
	Custom(u32),
}

impl std::str::FromStr for DatabasePruningMode {
	type Err = String;

	fn from_str(input: &str) -> Result<Self, Self::Err> {
		match input {
			"archive" => Ok(Self::Archive),
			"archive-canonical" => Ok(Self::ArchiveCanonical),
			bc => bc
				.parse()
				.map_err(|_| "Invalid pruning mode specified".to_string())
				.map(Self::Custom),
		}
	}
}

impl Into<PruningMode> for DatabasePruningMode {
	fn into(self) -> PruningMode {
		match self {
			DatabasePruningMode::Archive => PruningMode::ArchiveAll,
			DatabasePruningMode::ArchiveCanonical => PruningMode::ArchiveCanonical,
			DatabasePruningMode::Custom(n) => PruningMode::blocks_pruning(n),
		}
	}
}

impl Into<BlocksPruning> for DatabasePruningMode {
	fn into(self) -> BlocksPruning {
		match self {
			DatabasePruningMode::Archive => BlocksPruning::KeepAll,
			DatabasePruningMode::ArchiveCanonical => BlocksPruning::KeepFinalized,
			DatabasePruningMode::Custom(n) => BlocksPruning::Some(n),
		}
	}
}
