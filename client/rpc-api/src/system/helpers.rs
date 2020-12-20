// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! Substrate system API helpers.

use std::fmt;
use serde::{Serialize, Deserialize};
use sp_chain_spec::{Properties, ChainType};

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
	/// The type of this chain.
	pub chain_type: ChainType,
}

/// Health struct returned by the RPC
#[derive(Debug, PartialEq, Serialize, Deserialize)]
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

impl fmt::Display for Health {
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		write!(fmt, "{} peers ({})", self.peers, if self.is_syncing {
			"syncing"
		} else { "idle" })
	}
}

/// Network Peer information
#[derive(Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct PeerInfo<Hash, Number> {
	/// Peer ID
	pub peer_id: String,
	/// Roles
	pub roles: String,
	/// Peer best block hash
	pub best_hash: Hash,
	/// Peer best block number
	pub best_number: Number,
}

/// The role the node is running as
#[derive(Debug, PartialEq, Serialize, Deserialize)]
pub enum NodeRole {
	/// The node is a full node
	Full,
	/// The node is a light client
	LightClient,
	/// The node is an authority
	Authority,
	/// The node is a sentry
	Sentry,
}

/// The state of the syncing of the node.
#[derive(Debug, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SyncState<Number> {
	/// Height of the block at which syncing started.
	pub starting_block: Number,
	/// Height of the current best block of the node.
	pub current_block: Number,
	/// Height of the highest block learned from the network. Missing if no block is known yet.
	#[serde(default = "Default::default", skip_serializing_if = "Option::is_none")]
	pub highest_block: Option<Number>,
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
				best_hash: 5u32,
				best_number: 6u32,
			}).unwrap(),
			r#"{"peerId":"2","roles":"a","bestHash":5,"bestNumber":6}"#,
		);
	}

	#[test]
	fn should_serialize_sync_state() {
		assert_eq!(
			::serde_json::to_string(&SyncState {
				starting_block: 12u32,
				current_block: 50u32,
				highest_block: Some(128u32),
			}).unwrap(),
			r#"{"startingBlock":12,"currentBlock":50,"highestBlock":128}"#,
		);

		assert_eq!(
			::serde_json::to_string(&SyncState {
				starting_block: 12u32,
				current_block: 50u32,
				highest_block: None,
			}).unwrap(),
			r#"{"startingBlock":12,"currentBlock":50}"#,
		);
	}
}
