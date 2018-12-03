// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Client testing utilities.

#![warn(missing_docs)]

extern crate parity_codec as codec;
extern crate substrate_primitives as primitives;
extern crate sr_primitives as runtime_primitives;
#[macro_use] extern crate substrate_executor as executor;

pub extern crate substrate_client as client;
pub extern crate substrate_keyring as keyring;
pub extern crate substrate_test_runtime as runtime;
pub extern crate substrate_consensus_common as consensus;
extern crate substrate_state_machine as state_machine;

pub mod client_ext;
pub mod trait_tests;
mod block_builder_ext;

pub use client_ext::TestClient;
pub use block_builder_ext::BlockBuilderExt;
pub use client::blockchain;
pub use client::backend;
pub use executor::NativeExecutor;

use std::sync::Arc;
use primitives::Blake2Hasher;
use runtime_primitives::StorageMap;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, Hash as HashT};
use runtime::genesismap::{GenesisConfig, additional_storage_with_genesis};
use keyring::Keyring;

mod local_executor {
	#![allow(missing_docs)]
	use super::runtime;
	// TODO: change the macro and pass in the `BlakeHasher` that dispatch needs from here instead
	native_executor_instance!(pub LocalExecutor, runtime::api::dispatch, runtime::native_version, include_bytes!("../../test-runtime/wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm"));
}

/// Native executor used for tests.
pub use local_executor::LocalExecutor;

/// Test client database backend.
pub type Backend = client::in_mem::Backend<runtime::Block, Blake2Hasher>;

/// Test client executor.
pub type Executor = client::LocalCallExecutor<
	Backend,
	executor::NativeExecutor<LocalExecutor>,
>;

/// Creates new client instance used for tests.
pub fn new() -> client::Client<Backend, Executor, runtime::Block, runtime::RuntimeApi> {
	new_with_backend(Arc::new(Backend::new()), false)
}

/// Creates new test client instance that suports changes trie creation.
pub fn new_with_changes_trie() -> client::Client<Backend, Executor, runtime::Block, runtime::RuntimeApi> {
	new_with_backend(Arc::new(Backend::new()), true)
}

/// Creates new client instance used for tests with an explicitely provided backend.
/// This is useful for testing backend implementations.
pub fn new_with_backend<B>(
	backend: Arc<B>,
	support_changes_trie: bool
) -> client::Client<B, client::LocalCallExecutor<B, executor::NativeExecutor<LocalExecutor>>, runtime::Block, runtime::RuntimeApi>
	where
		B: backend::LocalBackend<runtime::Block, Blake2Hasher>,
{
	let executor = NativeExecutor::new();
	client::new_with_backend(backend, executor, genesis_storage(support_changes_trie)).unwrap()
}

fn genesis_config(support_changes_trie: bool) -> GenesisConfig {
	GenesisConfig::new(support_changes_trie, vec![
		Keyring::Alice.to_raw_public().into(),
		Keyring::Bob.to_raw_public().into(),
		Keyring::Charlie.to_raw_public().into(),
	], 1000)
}

fn genesis_storage(support_changes_trie: bool) -> StorageMap {
	let mut storage = genesis_config(support_changes_trie).genesis_map();
	let state_root = <<<runtime::Block as BlockT>::Header as HeaderT>::Hashing as HashT>::trie_root(storage.clone().into_iter());
	let block: runtime::Block = client::genesis::construct_genesis_block(state_root);
	storage.extend(additional_storage_with_genesis(&block));
	storage
}
