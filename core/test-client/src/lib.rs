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

// tag::description[]
//! Client testing utilities.
// end::description[]

#![warn(missing_docs)]

extern crate rhododendron;
extern crate substrate_bft as bft;
extern crate parity_codec as codec;
extern crate substrate_primitives as primitives;
extern crate srml_support as runtime_support;
extern crate sr_primitives as runtime_primitives;
#[macro_use] extern crate substrate_executor as executor;
extern crate hash_db;

pub extern crate substrate_client as client;
pub extern crate substrate_keyring as keyring;
pub extern crate substrate_test_runtime as runtime;

pub mod client_ext;
pub mod trait_tests;
mod block_builder_ext;

use std::sync::Arc;

pub use client_ext::TestClient;
pub use block_builder_ext::BlockBuilderExt;
pub use client::blockchain;
pub use client::backend;
pub use executor::NativeExecutor;

use primitives::Blake2Hasher;
use runtime_primitives::StorageMap;
use runtime::genesismap::{GenesisConfig, additional_storage_with_genesis};
use keyring::Keyring;

mod local_executor {
	#![allow(missing_docs)]
	use super::runtime;
	// TODO: change the macro and pass in the `BlakeHasher` that dispatch needs from here instead
	native_executor_instance!(pub LocalExecutor, runtime::api::dispatch, runtime::VERSION, include_bytes!("../../test-runtime/wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm"));
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
pub fn new() -> client::Client<Backend, Executor, runtime::Block> {
	new_with_backend(Arc::new(Backend::new()))
}

/// Creates new client instance used for tests with an explicitely provided backend.
/// This is useful for testing backend implementations.
pub fn new_with_backend<B>(backend: Arc<B>) -> client::Client<B, client::LocalCallExecutor<B, executor::NativeExecutor<LocalExecutor>>, runtime::Block>
	where
		B: backend::LocalBackend<runtime::Block, Blake2Hasher>,
{
	let executor = NativeExecutor::new();
	client::new_with_backend(backend, executor, genesis_storage()).unwrap()
}

fn genesis_config() -> GenesisConfig {
	GenesisConfig::new_simple(vec![
		Keyring::Alice.to_raw_public().into(),
		Keyring::Bob.to_raw_public().into(),
		Keyring::Charlie.to_raw_public().into(),
	], 1000)
}

fn genesis_storage() -> StorageMap {
	let mut storage = genesis_config().genesis_map();
	let block: runtime::Block = client::genesis::construct_genesis_block(&storage);
	storage.extend(additional_storage_with_genesis(&block));
	storage
}
