// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

use std::collections::BTreeMap;
use network::NodeId;
use primitives::block::{HeaderHash, ExtrinsicHash, Number as BlockNumber};
use config::Role;

/// Reported sync state.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum SyncState {
	/// Initial sync is complete, keep-up sync is active.
	Idle,
	/// Actively catching up with the chain.
	Downloading
}

/// Syncing status and statistics
#[derive(Clone)]
pub struct SyncStatus {
	/// Current global sync state.
	pub state: SyncState,
	/// Target sync block number.
	pub best_seen_block: Option<BlockNumber>,
}

/// Syncing status and statistics
#[derive(Clone)]
pub struct ProtocolStatus {
	/// Sync status.
	pub sync: SyncStatus,
	/// Total number of connected peers
	pub num_peers: usize,
	/// Total number of active peers.
	pub num_active_peers: usize,
}

/// Peer protocol information.
#[derive(Debug)]
pub struct ProtocolPeerInfo {
	/// Roles
	pub roles: Role,
	/// Protocol version
	pub protocol_version: u32,
	/// Peer best block hash
	pub best_hash: HeaderHash,
	/// Peer best block number
	pub best_number: BlockNumber,
}

/// Peer connection information
#[derive(Debug)]
pub struct PeerInfo {
	/// Public node id
	pub id: Option<String>,
	/// Node client ID
	pub client_version: String,
	/// Capabilities
	pub capabilities: Vec<String>,
	/// Remote endpoint address
	pub remote_address: String,
	/// Local endpoint address
	pub local_address: String,
	/// Dot protocol info.
	pub dot_info: Option<ProtocolPeerInfo>,
}

/// Transaction stats
#[derive(Debug)]
pub struct TransactionStats {
	/// Block number where this TX was first seen.
	pub first_seen: u64,
	/// Peers it was propagated to.
	pub propagated_to: BTreeMap<NodeId, usize>,
}

/// Sync status
pub trait SyncProvider: Send + Sync {
	/// Get sync status
	fn status(&self) -> ProtocolStatus;
	/// Get peers information
	fn peers(&self) -> Vec<PeerInfo>;
	/// Get this node id if available.
	fn node_id(&self) -> Option<String>;
	/// Returns propagation count for pending transactions.
	fn transactions_stats(&self) -> BTreeMap<ExtrinsicHash, TransactionStats>;
}
