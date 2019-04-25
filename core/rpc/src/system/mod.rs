// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Substrate system API.

pub mod error;

mod helpers;
#[cfg(test)]
mod tests;

use std::sync::Arc;
use jsonrpc_derive::rpc;
use network;
use runtime_primitives::traits::{self, Header as HeaderT};

use self::error::Result;
pub use self::helpers::{Properties, SystemInfo, Health, PeerInfo};

/// Substrate system RPC API
#[rpc]
pub trait SystemApi<Hash, Number> {
	/// Get the node's implementation name. Plain old string.
	#[rpc(name = "system_name")]
	fn system_name(&self) -> Result<String>;

	/// Get the node implementation's version. Should be a semver string.
	#[rpc(name = "system_version")]
	fn system_version(&self) -> Result<String>;

	/// Get the chain's type. Given as a string identifier.
	#[rpc(name = "system_chain")]
	fn system_chain(&self) -> Result<String>;

	/// Get a custom set of properties as a JSON object, defined in the chain spec.
	#[rpc(name = "system_properties")]
	fn system_properties(&self) -> Result<Properties>;

	/// Return health status of the node.
	///
	/// Node is considered healthy if it is:
	/// - connected to some peers (unless running in dev mode)
	/// - not performing a major sync
	#[rpc(name = "system_health")]
	fn system_health(&self) -> Result<Health>;

	/// Returns currently connected peers
	#[rpc(name = "system_peers")]
	fn system_peers(&self) -> Result<Vec<PeerInfo<Hash, Number>>>;

	/// Returns current state of the network.
	///
	/// **Warning**: This API is not stable.
	// TODO: make this stable and move structs https://github.com/paritytech/substrate/issues/1890
	#[rpc(name = "system_networkState")]
	fn system_network_state(&self) -> Result<network::NetworkState>;
}

/// System API implementation
pub struct System<B: traits::Block> {
	info: SystemInfo,
	sync: Arc<network::SyncProvider<B>>,
	should_have_peers: bool,
}

impl<B: traits::Block> System<B> {
	/// Creates new `System` given the `SystemInfo`.
	pub fn new(
		info: SystemInfo,
		sync: Arc<network::SyncProvider<B>>,
		should_have_peers: bool,
	) -> Self {
		System {
			info,
			should_have_peers,
			sync,
		}
	}
}

impl<B: traits::Block> SystemApi<B::Hash, <B::Header as HeaderT>::Number> for System<B> {
	fn system_name(&self) -> Result<String> {
		Ok(self.info.impl_name.clone())
	}

	fn system_version(&self) -> Result<String> {
		Ok(self.info.impl_version.clone())
	}

	fn system_chain(&self) -> Result<String> {
		Ok(self.info.chain_name.clone())
	}

	fn system_properties(&self) -> Result<Properties> {
		Ok(self.info.properties.clone())
	}

	fn system_health(&self) -> Result<Health> {
		Ok(Health {
			peers: self.sync.peers().len(),
			is_syncing: self.sync.is_major_syncing(),
			should_have_peers: self.should_have_peers,
		})
	}

	fn system_peers(&self) -> Result<Vec<PeerInfo<B::Hash, <B::Header as HeaderT>::Number>>> {
		Ok(self.sync.peers().into_iter().map(|(peer_id, p)| PeerInfo {
			peer_id: peer_id.to_base58(),
			roles: format!("{:?}", p.roles),
			protocol_version: p.protocol_version,
			best_hash: p.best_hash,
			best_number: p.best_number,
		}).collect())
	}

	fn system_network_state(&self) -> Result<network::NetworkState> {
		Ok(self.sync.network_state())
	}
}
