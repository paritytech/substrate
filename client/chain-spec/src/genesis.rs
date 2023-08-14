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

use std::{collections::hash_map::DefaultHasher, marker::PhantomData, sync::Arc};

use sc_client_api::{backend::Backend, BlockImportOperation};
use sc_executor::RuntimeVersionOf;
use sp_core::storage::{well_known_keys, StateVersion, Storage};
use sp_runtime::{
	traits::{Block as BlockT, Hash as HashT, Header as HeaderT, Zero},
	BuildStorage,
};

/// Return the state version given the genesis storage and executor.
pub fn resolve_state_version_from_wasm<E>(
	storage: &Storage,
	executor: &E,
) -> sp_blockchain::Result<StateVersion>
where
	E: RuntimeVersionOf,
{
	if let Some(wasm) = storage.top.get(well_known_keys::CODE) {
		let mut ext = sp_state_machine::BasicExternalities::new_empty(); // just to read runtime version.

		let code_fetcher = sp_core::traits::WrappedRuntimeCode(wasm.as_slice().into());
		let runtime_code = sp_core::traits::RuntimeCode {
			code_fetcher: &code_fetcher,
			heap_pages: None,
			hash: {
				use std::hash::{Hash, Hasher};
				let mut state = DefaultHasher::new();
				wasm.hash(&mut state);
				state.finish().to_le_bytes().to_vec()
			},
		};
		let runtime_version = RuntimeVersionOf::runtime_version(executor, &mut ext, &runtime_code)
			.map_err(|e| sp_blockchain::Error::VersionInvalid(e.to_string()))?;
		Ok(runtime_version.state_version())
	} else {
		Err(sp_blockchain::Error::VersionInvalid(
			"Runtime missing from initial storage, could not read state version.".to_string(),
		))
	}
}

/// Create a genesis block, given the initial storage.
pub fn construct_genesis_block<Block: BlockT>(
	state_root: Block::Hash,
	state_version: StateVersion,
) -> Block {
	let extrinsics_root = <<<Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(
		Vec::new(),
		state_version,
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

		let genesis_state_version = resolve_state_version_from_wasm(&genesis_storage, &executor)?;
		let mut op = backend.begin_operation()?;
		let state_root =
			op.set_genesis_state(genesis_storage, commit_genesis_state, genesis_state_version)?;
		let genesis_block = construct_genesis_block::<Block>(state_root, genesis_state_version);

		Ok((genesis_block, op))
	}
}
