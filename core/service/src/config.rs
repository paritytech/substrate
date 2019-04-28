// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Service configuration.

use std::net::SocketAddr;
use transaction_pool;
use crate::chain_spec::ChainSpec;
pub use client::ExecutionStrategies;
pub use client_db::PruningMode;
pub use network::config::{NetworkConfiguration, Roles};
use runtime_primitives::BuildStorage;
use serde::{Serialize, de::DeserializeOwned};
use target_info::Target;
use tel::TelemetryEndpoints;

/// Service configuration.
#[derive(Clone)]
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
	pub transaction_pool: transaction_pool::txpool::Options,
	/// Network configuration.
	pub network: NetworkConfiguration,
	/// Path to key files.
	pub keystore_path: String,
	/// Path to the database.
	pub database_path: String,
	/// Cache Size for internal database in MiB
	pub database_cache_size: Option<u32>,
	/// Size of internal state cache in Bytes
	pub state_cache_size: usize,
	/// Pruning settings.
	pub pruning: PruningMode,
	/// Additional key seeds.
	pub keys: Vec<String>,
	/// Chain configuration.
	pub chain_spec: ChainSpec<G>,
	/// Custom configuration.
	pub custom: C,
	/// Node name.
	pub name: String,
	/// Execution strategies.
	pub execution_strategies: ExecutionStrategies,
	/// RPC over HTTP binding address. `None` if disabled.
	pub rpc_http: Option<SocketAddr>,
	/// RPC over Websockets binding address. `None` if disabled.
	pub rpc_ws: Option<SocketAddr>,
	/// CORS settings for HTTP & WS servers. `None` if all origins are allowed.
	pub rpc_cors: Option<Vec<String>>,
	/// Telemetry service URL. `None` if disabled.
	pub telemetry_endpoints: Option<TelemetryEndpoints>,
	/// The default number of 64KB pages to allocate for Wasm execution
	pub default_heap_pages: Option<u64>,
	/// Should offchain workers be executed.
	pub offchain_worker: bool,
	/// Enable authoring even when offline.
	pub force_authoring: bool,
	/// Disable GRANDPA when running in validator mode
	pub disable_grandpa: bool,
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
			transaction_pool: Default::default(),
			network: Default::default(),
			keystore_path: Default::default(),
			database_path: Default::default(),
			database_cache_size: Default::default(),
			state_cache_size: Default::default(),
			keys: Default::default(),
			custom: Default::default(),
			pruning: PruningMode::default(),
			execution_strategies: Default::default(),
			rpc_http: None,
			rpc_ws: None,
			rpc_cors: Some(vec![]),
			telemetry_endpoints: None,
			default_heap_pages: None,
			offchain_worker: Default::default(),
			force_authoring: false,
			disable_grandpa: false,
		};
		configuration.network.boot_nodes = configuration.chain_spec.boot_nodes().to_vec();

		configuration.telemetry_endpoints = configuration.chain_spec.telemetry_endpoints().clone();

		configuration
	}

	/// Returns full version string of this configuration.
	pub fn full_version(&self) -> String {
		full_version_from_strs(self.impl_version, self.impl_commit)
	}

	/// Implementation id and version.
	pub fn client_id(&self) -> String {
		format!("{}/v{}", self.impl_name, self.full_version())
	}
}

/// Returns platform info
pub fn platform() -> String {
	let env = Target::env();
	let env_dash = if env.is_empty() { "" } else { "-" };
	format!("{}-{}{}{}", Target::arch(), Target::os(), env_dash, env)
}

/// Returns full version string, using supplied version and commit.
pub fn full_version_from_strs(impl_version: &str, impl_commit: &str) -> String {
	let commit_dash = if impl_commit.is_empty() { "" } else { "-" };
	format!("{}{}{}-{}", impl_version, commit_dash, impl_commit, platform())
}

