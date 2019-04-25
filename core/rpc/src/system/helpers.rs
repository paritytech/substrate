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

//! Substrate system API helpers.

use std::fmt;
use serde_derive::{Serialize};
use serde_json::{Value, map::Map};

/// Node properties
pub type Properties = Map<String, Value>;

/// Running node's static details.
#[derive(Clone, Debug)]
pub struct SystemInfo {
	/// Implementation name.
	pub impl_name: String,
	/// Implementation version.
	pub impl_version: String,
	/// Chain name.
	pub chain_name: String,
	/// A custom set of properties defined in the chain spec.
	pub properties: Properties,
}

/// Health struct returned by the RPC
#[derive(Debug, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct Health {
	/// Number of connected peers
	pub peers: usize,
	/// Is the node syncing
	pub is_syncing: bool,
	/// Should this node have any peers
	///
	/// Might be false for local chains or when running without discovery.
	pub should_have_peers: bool,
}

/// Network Peer information
#[derive(Debug, PartialEq, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct PeerInfo<Hash, Number> {
	/// Peer ID
	pub peer_id: String,
	/// Roles
	pub roles: String,
	/// Protocol version
	pub protocol_version: u32,
	/// Peer best block hash
	pub best_hash: Hash,
	/// Peer best block number
	pub best_number: Number,
}

impl fmt::Display for Health {
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		write!(fmt, "{} peers ({})", self.peers, if self.is_syncing {
			"syncing"
		} else { "idle" })
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn should_serialize_health() {
		assert_eq!(
			::serde_json::to_string(&Health {
				peers: 1,
				is_syncing: false,
				should_have_peers: true,
			}).unwrap(),
			r#"{"peers":1,"isSyncing":false,"shouldHavePeers":true}"#,
		);
	}

	#[test]
	fn should_serialize_peer_info() {
		assert_eq!(
			::serde_json::to_string(&PeerInfo {
				peer_id: "2".into(),
				roles: "a".into(),
				protocol_version: 2,
				best_hash: 5u32,
				best_number: 6u32,
			}).unwrap(),
			r#"{"peerId":"2","roles":"a","protocolVersion":2,"bestHash":5,"bestNumber":6}"#,
		);
	}
}
