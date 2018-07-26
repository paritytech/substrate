// Copyright 2017 Parity Technologies (UK) Ltd.
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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.?

//! Service configuration.

use std::net::SocketAddr;
use extrinsic_pool;
use chain_spec::ChainSpec;
pub use client::ExecutionStrategy;
pub use network::Roles;
pub use network::NetworkConfiguration;
pub use client_db::PruningMode;
use runtime_primitives::BuildStorage;
use serde::{Serialize, de::DeserializeOwned};
use target_info::Target;

/// Service configuration.
pub struct Configuration<C, G: Serialize + DeserializeOwned + BuildStorage> {
	/// Implementation name
	pub impl_name: &'static str,
	/// Implementation version
	pub impl_version: &'static str,
	/// Git commit if any.
	pub impl_commit: &'static str,
	/// Node roles.
	pub roles: Roles,
	/// Extrinsic pool configuration.
	pub extrinsic_pool: extrinsic_pool::txpool::Options,
	/// Network configuration.
	pub network: NetworkConfiguration,
	/// Path to key files.
	pub keystore_path: String,
	/// Path to the database.
	pub database_path: String,
	/// Pruning settings.
	pub pruning: PruningMode,
	/// Additional key seeds.
	pub keys: Vec<String>,
	/// Chain configuration.
	pub chain_spec: ChainSpec<G>,
	/// Custom configuration.
	pub custom: C,
	/// Telemetry server URL, optional - only `Some` if telemetry reporting is enabled
	pub telemetry: Option<String>,
	/// Node name.
	pub name: String,
	/// Execution strategy.
	pub execution_strategy: ExecutionStrategy,
	/// Minimum number of heap pages to allocate for Wasm execution.
	pub min_heap_pages: usize,
	/// Maximum number of heap pages to allocate for Wasm execution.
	pub max_heap_pages: usize,
	/// RPC over HTTP binding address. `None` if disabled.
	pub rpc_http: Option<SocketAddr>,
	/// RPC over Websockets binding address. `None` if disabled.
	pub rpc_ws: Option<SocketAddr>,
	/// Telemetry service URL. `None` if disabled.
	pub telemetry_url: Option<String>,
}

impl<C: Default, G: Serialize + DeserializeOwned + BuildStorage> Configuration<C, G> {
	/// Create default config for given chain spec.
	pub fn default_with_spec(chain_spec: ChainSpec<G>) -> Self {
		let mut configuration = Configuration {
			impl_name: "parity-substrate",
			impl_version: "0.0.0",
			impl_commit: "",
			chain_spec,
			name: Default::default(),
			roles: Roles::FULL,
			extrinsic_pool: Default::default(),
			network: Default::default(),
			keystore_path: Default::default(),
			database_path: Default::default(),
			keys: Default::default(),
			custom: Default::default(),
			telemetry: Default::default(),
			pruning: PruningMode::default(),
			execution_strategy: ExecutionStrategy::Both,
			min_heap_pages: 8,
			max_heap_pages: 1024,
			rpc_http: None,
			rpc_ws: None,
			telemetry_url: None,
		};
		configuration.network.boot_nodes = configuration.chain_spec.boot_nodes().to_vec();
		configuration.telemetry_url = configuration.chain_spec.telemetry_url().map(str::to_owned);
		configuration
	}

	/// Returns platform info
	pub fn platform() -> String {
		let env = Target::env();
		let env_dash = if env.is_empty() { "" } else { "-" };
		format!("{}-{}{}{}", Target::arch(), Target::os(), env_dash, env)
	}

	/// Returns full version string.
	pub fn full_version(&self) -> String {
		let commit_dash = if self.impl_commit.is_empty() { "" } else { "-" };
		format!("{}{}{}-{}", self.impl_version, commit_dash, self.impl_commit, Self::platform())
	}

	/// Implementation id and version.
	pub fn client_id(&self) -> String {
		format!("{}/v{}", self.impl_name, self.full_version())
	}
}
