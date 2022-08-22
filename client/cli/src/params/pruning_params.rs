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
	/// Specify the state pruning mode, a number of blocks to keep or 'archive'.
	///
	/// Default is to keep only the last 256 blocks,
	/// otherwise, the state can be kept for all of the blocks (i.e 'archive'),
	/// or for all of the canonical blocks (i.e 'archive-canonical').
	#[clap(alias = "pruning", long, value_name = "PRUNING_MODE")]
	pub state_pruning: Option<String>,
	/// Specify the number of finalized blocks to keep in the database.
	///
	/// Default is to keep all blocks.
	///
	/// NOTE: only finalized blocks are subject for removal!
	#[clap(alias = "keep-blocks", long, value_name = "COUNT")]
	pub blocks_pruning: Option<u32>,
}

impl PruningParams {
	/// Get the pruning value from the parameters
	pub fn state_pruning(&self) -> error::Result<Option<PruningMode>> {
		self.state_pruning
			.as_ref()
			.map(|s| match s.as_str() {
				"archive" => Ok(PruningMode::ArchiveAll),
				bc => bc
					.parse()
					.map_err(|_| error::Error::Input("Invalid pruning mode specified".to_string()))
					.map(PruningMode::blocks_pruning),
			})
			.transpose()
	}

	/// Get the block pruning value from the parameters
	pub fn blocks_pruning(&self) -> error::Result<BlocksPruning> {
		Ok(match self.blocks_pruning {
			Some(n) => BlocksPruning::Some(n),
			None => BlocksPruning::All,
		})
	}
}
