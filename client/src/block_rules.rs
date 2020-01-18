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

//! Client fixed specification rules

use std::collections::{HashMap, HashSet};

use sp_runtime::{
	traits::{Block as BlockT, NumberFor, BlockHashFor},
};

use sc_client_api::{ForkBlocks, BadBlocks};

/// Specification rules lookup result.
pub enum LookupResult<B: BlockT> {
	/// Specification rules do not contain any special rules about this block
	NotSpecial,
	/// The bock is known to be bad and should not be imported
	KnownBad,
	/// There is a fork expected to different fork
	ExpectedForkTo(BlockHashFor<B>)
}

/// Block special rules.
///
/// This holds known bad blocks and known good forks, and
/// usually part of the chain spec.
pub struct BlockRules<B: BlockT> {
	bad: HashSet<BlockHashFor<B>>,
	forks: HashMap<NumberFor<B>, BlockHashFor<B>>,
}

impl<B: BlockT> BlockRules<B> {
	/// New block rules with provided black and white lists.
	pub fn new(
		fork_blocks: ForkBlocks<B>,
		bad_blocks: BadBlocks<B>,
	) -> Self {
		Self {
			bad: bad_blocks.unwrap_or(HashSet::new()),
			forks: fork_blocks.unwrap_or(vec![]).into_iter().collect(),
		}
	}

	pub fn lookup(&self, number: NumberFor<B>, hash: &BlockHashFor<B>) -> LookupResult<B> {
		if let Some(hash_for_height) = self.forks.get(&number) {
			if hash_for_height != hash {
				return LookupResult::ExpectedForkTo(hash_for_height.clone());
			}
		}

		if self.bad.contains(hash) {
			return LookupResult::KnownBad;
		}

		LookupResult::NotSpecial
	}
}