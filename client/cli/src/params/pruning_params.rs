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

use crate::error;
use clap::Args;
use sc_service::{BlocksPruning, PruningMode};

/// Parameters to define the pruning mode
#[derive(Debug, Clone, PartialEq, Args)]
pub struct PruningParams {
	/// Specify the state pruning mode.
	///
	/// This mode specifies when the block's state (ie, storage)
	/// should be pruned (ie, removed) from the database.
	///
	/// Options available:
	///   'archive'            Keep the state of all blocks.
	///   'archive-canonical'  Keep only the state of finalized (canonical) blocks.
	///   [number]             Keep the state of the last number of finalized (canonical) blocks.
	///
	/// The default option is to keep the last 256 blocks (number == 256).
	#[arg(alias = "pruning", long, value_name = "PRUNING_MODE")]
	pub state_pruning: Option<String>,
	/// Specify the blocks pruning mode.
	///
	/// This mode specifies when the block's body (including justifications)
	/// should be pruned (ie, removed) from the database.
	///
	/// Options available:
	///   'archive'            Keep all blocks.
	///   'archive-canonical'  Keep only finalized (canonical) blocks.
	///   [number]             Keep the last number of finalized (canonical) blocks.
	///
	/// The default option is 'archive-canonical'.
	#[arg(alias = "keep-blocks", long, value_name = "COUNT")]
	pub blocks_pruning: Option<String>,
}

impl PruningParams {
	/// Get the pruning value from the parameters
	pub fn state_pruning(&self) -> error::Result<Option<PruningMode>> {
		self.state_pruning
			.as_ref()
			.map(|s| match s.as_str() {
				"archive" => Ok(PruningMode::ArchiveAll),
				"archive-canonical" => Ok(PruningMode::ArchiveCanonical),
				bc => bc
					.parse()
					.map_err(|_| {
						error::Error::Input("Invalid state pruning mode specified".to_string())
					})
					.map(PruningMode::blocks_pruning),
			})
			.transpose()
	}

	/// Get the block pruning value from the parameters
	pub fn blocks_pruning(&self) -> error::Result<BlocksPruning> {
		match self.blocks_pruning.as_ref() {
			Some(bp) => match bp.as_str() {
				"archive" => Ok(BlocksPruning::KeepAll),
				"archive-canonical" => Ok(BlocksPruning::KeepFinalized),
				bc => bc
					.parse()
					.map_err(|_| {
						error::Error::Input("Invalid blocks pruning mode specified".to_string())
					})
					.map(BlocksPruning::Some),
			},
			None => Ok(BlocksPruning::KeepFinalized),
		}
	}
}
