// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Tool for creating the genesis block.

use sp_runtime::traits::{Block as BlockT, Hash as HashT, Header as HeaderT, Zero};

/// Create a genesis block, given the initial storage.
pub fn construct_genesis_block<Block: BlockT>(state_root: Block::Hash) -> Block {
	let extrinsics_root = <<<Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(
		Vec::new(),
		sp_runtime::StateVersion::V0,
	);

	Block::new(
		<<Block as BlockT>::Header as HeaderT>::new(
			Zero::zero(),
			extrinsics_root,
			state_root,
			Default::default(),
			Default::default(),
		),
		Default::default(),
	)
}
