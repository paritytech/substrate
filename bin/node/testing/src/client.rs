// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Utilites to build a `TestClient` for `node-runtime`.

use sp_runtime::BuildStorage;

/// Re-export test-client utilities.
pub use test_client::*;

/// Call executor for `node-runtime` `TestClient`.
pub type Executor = sc_executor::NativeExecutor<node_executor::Executor>;

/// Default backend type.
pub type Backend = client_db::Backend<node_primitives::Block>;

/// Test client type.
pub type Client = client::Client<
	Backend,
	client::LocalCallExecutor<Backend, Executor>,
	node_primitives::Block,
	node_runtime::RuntimeApi,
>;

/// Genesis configuration parameters for `TestClient`.
#[derive(Default)]
pub struct GenesisParameters {
	support_changes_trie: bool,
}

impl test_client::GenesisInit for GenesisParameters {
	fn genesis_storage(&self) -> (StorageOverlay, ChildrenStorageOverlay) {
		crate::genesis::config(self.support_changes_trie, None).build_storage().unwrap()
	}
}

/// A `test-runtime` extensions to `TestClientBuilder`.
pub trait TestClientBuilderExt: Sized {
	/// Create test client builder.
	fn new() -> Self;

	/// Build the test client.
	fn build(self) -> Client;
}

impl TestClientBuilderExt for test_client::TestClientBuilder<
	client::LocalCallExecutor<Backend, Executor>,
	Backend,
	GenesisParameters,
> {
	fn new() -> Self{
		Self::default()
	}

	fn build(self) -> Client {
		self.build_with_native_executor(None).0
	}
}


