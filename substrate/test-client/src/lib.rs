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

extern crate rhododendron;
extern crate substrate_bft as bft;
extern crate substrate_codec as codec;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_support as runtime_support;
extern crate substrate_runtime_primitives as runtime_primitives;
#[macro_use] extern crate substrate_executor as executor;
extern crate hashdb;

pub extern crate substrate_client as client;
pub extern crate substrate_keyring as keyring;
pub extern crate substrate_test_runtime as runtime;

mod client_ext;
mod block_builder_ext;

pub use client_ext::TestClient;
pub use block_builder_ext::BlockBuilderExt;

use primitives::{KeccakHasher, RlpCodec};

mod local_executor {
	#![allow(missing_docs)]
	use super::runtime;
	// TODO: change the macro and pass in the `BlakeHasher` that dispatch needs from here instead
	native_executor_instance!(pub LocalExecutor, runtime::api::dispatch, runtime::VERSION, include_bytes!("../../test-runtime/wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm"));
}

/// Native executor used for tests.
pub use local_executor::LocalExecutor;

/// Test client database backend.
pub type Backend = client::in_mem::Backend<runtime::Block, KeccakHasher, RlpCodec>;

/// Test client executor.
pub type Executor = client::LocalCallExecutor<
	Backend,
	executor::NativeExecutor<LocalExecutor>,
>;

/// Creates new client instance used for tests.
pub fn new() -> client::Client<Backend, Executor, runtime::Block> {
	TestClient::new_for_tests()
}
