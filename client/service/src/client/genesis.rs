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

//! Tool for creating the genesis block.

use sc_client_api::{backend::Backend, BlockImportOperation};
use sc_executor::RuntimeVersionOf;
use sp_core::storage::Storage;
use sp_runtime::{
	traits::{Block as BlockT, Hash as HashT, Header as HeaderT, Zero},
	BuildStorage,
};
use std::{marker::PhantomData, sync::Arc};

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

/// Trait for building the genesis block.
pub trait BuildGenesisBlock<Block: BlockT> {
	/// The import operation used to import the genesis block into the backend.
	type BlockImportOperation;

	/// Returns the built genesis block along with the block import operation
	/// after setting the genesis storage.
	fn build_genesis_block(self) -> sp_blockchain::Result<(Block, Self::BlockImportOperation)>;
}

/// Default genesis block builder in Substrate.
pub struct GenesisBlockBuilder<Block: BlockT, B, E> {
	genesis_storage: Storage,
	commit_genesis_state: bool,
	backend: Arc<B>,
	executor: E,
	_phantom: PhantomData<Block>,
}

impl<Block: BlockT, B: Backend<Block>, E: RuntimeVersionOf> GenesisBlockBuilder<Block, B, E> {
	/// Constructs a new instance of [`GenesisBlockBuilder`].
	pub fn new(
		build_genesis_storage: &dyn BuildStorage,
		commit_genesis_state: bool,
		backend: Arc<B>,
		executor: E,
	) -> sp_blockchain::Result<Self> {
		let genesis_storage =
			build_genesis_storage.build_storage().map_err(sp_blockchain::Error::Storage)?;
		Ok(Self {
			genesis_storage,
			commit_genesis_state,
			backend,
			executor,
			_phantom: PhantomData::<Block>,
		})
	}
}

impl<Block: BlockT, B: Backend<Block>, E: RuntimeVersionOf> BuildGenesisBlock<Block>
	for GenesisBlockBuilder<Block, B, E>
{
	type BlockImportOperation = <B as Backend<Block>>::BlockImportOperation;

	fn build_genesis_block(self) -> sp_blockchain::Result<(Block, Self::BlockImportOperation)> {
		let Self { genesis_storage, commit_genesis_state, backend, executor, _phantom } = self;

		let genesis_state_version =
			crate::resolve_state_version_from_wasm(&genesis_storage, &executor)?;
		let mut op = backend.begin_operation()?;
		let state_root =
			op.set_genesis_state(genesis_storage, commit_genesis_state, genesis_state_version)?;
		let genesis_block = construct_genesis_block::<Block>(state_root);

		Ok((genesis_block, op))
	}
}
