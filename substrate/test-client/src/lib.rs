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

extern crate substrate_bft as bft;
extern crate substrate_codec as codec;
extern crate substrate_keyring as keyring;
extern crate substrate_primitives as primitives;
extern crate substrate_runtime_support as runtime_support;
#[macro_use] extern crate substrate_executor as executor;

pub extern crate substrate_test_runtime as runtime;
pub extern crate substrate_client as client;

mod client_ext;

pub use client_ext::TestClient;

mod native_executor {
	#![allow(missing_docs)]
	use super::runtime;

	native_executor_instance!(pub NativeExecutor, runtime::api::dispatch, include_bytes!("../../test-runtime/wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm"));
}

/// Native executor used for tests.
pub use self::native_executor::NativeExecutor;

/// Test client database backend.
pub type Backend = client::in_mem::Backend;

/// Test client executor.
pub type Executor = executor::NativeExecutor<NativeExecutor>;

/// Creates new client instance used for tests.
pub fn new() -> client::Client<Backend, Executor> {
	TestClient::new_for_tests()
}
