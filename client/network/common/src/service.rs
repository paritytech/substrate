// This file is part of Substrate.
//
// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.
//
// If you read this, you are very thorough, congratulations.

use crate::sync::{warp::WarpSyncProgress, StateDownloadProgress, SyncState};
pub use libp2p::{identity::error::SigningError, kad::record::Key as KademliaKey};
use libp2p::{Multiaddr, PeerId};
use sc_peerset::ReputationChange;
pub use signature::Signature;
use sp_runtime::traits::{Block as BlockT, NumberFor};
use std::{borrow::Cow, collections::HashSet, future::Future, pin::Pin, sync::Arc};

mod signature;

/// Signer with network identity
pub trait NetworkSigner {
	/// Signs the message with the `KeyPair` that defined the local `PeerId`.
	fn sign_with_local_identity(&self, msg: impl AsRef<[u8]>) -> Result<Signature, SigningError>;
}

impl<T> NetworkSigner for Arc<T>
where
	T: ?Sized,
	T: NetworkSigner,
{
	fn sign_with_local_identity(&self, msg: impl AsRef<[u8]>) -> Result<Signature, SigningError> {
		T::sign_with_local_identity(self, msg)
	}
}

/// Get value network provider.
pub trait NetworkKVProvider {
	/// Start getting a value from the DHT.
	fn get_value(&self, key: &KademliaKey);

	/// Start putting a value in the DHT.
	fn put_value(&self, key: KademliaKey, value: Vec<u8>);
}

impl<T> NetworkKVProvider for Arc<T>
where
	T: ?Sized,
	T: NetworkKVProvider,
{
	fn get_value(&self, key: &KademliaKey) {
		T::get_value(self, key)
	}

	fn put_value(&self, key: KademliaKey, value: Vec<u8>) {
		T::put_value(self, key, value)
	}
}

/// Provides an ability to set a fork sync request for a particular block.
pub trait NetworkSyncForkRequest<BlockHash, BlockNumber> {
	/// Notifies the sync service to try and sync the given block from the given
	/// peers.
	///
	/// If the given vector of peers is empty then the underlying implementation
	/// should make a best effort to fetch the block from any peers it is
	/// connected to (NOTE: this assumption will change in the future #3629).
	fn set_sync_fork_request(&self, peers: Vec<PeerId>, hash: BlockHash, number: BlockNumber);
}

impl<T, BlockHash, BlockNumber> NetworkSyncForkRequest<BlockHash, BlockNumber> for Arc<T>
where
	T: ?Sized,
	T: NetworkSyncForkRequest<BlockHash, BlockNumber>,
{
	fn set_sync_fork_request(&self, peers: Vec<PeerId>, hash: BlockHash, number: BlockNumber) {
		T::set_sync_fork_request(self, peers, hash, number)
	}
}

/// Overview status of the network.
#[derive(Clone)]
pub struct NetworkStatus<B: BlockT> {
	/// Current global sync state.
	pub sync_state: SyncState,
	/// Target sync block number.
	pub best_seen_block: Option<NumberFor<B>>,
	/// Number of peers participating in syncing.
	pub num_sync_peers: u32,
	/// Total number of connected peers
	pub num_connected_peers: usize,
	/// Total number of active peers.
	pub num_active_peers: usize,
	/// The total number of bytes received.
	pub total_bytes_inbound: u64,
	/// The total number of bytes sent.
	pub total_bytes_outbound: u64,
	/// State sync in progress.
	pub state_sync: Option<StateDownloadProgress>,
	/// Warp sync in progress.
	pub warp_sync: Option<WarpSyncProgress<B>>,
}

/// Provides high-level status information about network.
#[async_trait::async_trait]
pub trait NetworkStatusProvider<Block: BlockT> {
	/// High-level network status information.
	///
	/// Returns an error if the `NetworkWorker` is no longer running.
	async fn status(&self) -> Result<NetworkStatus<Block>, ()>;
}

// Manual implementation to avoid extra boxing here
impl<T, Block: BlockT> NetworkStatusProvider<Block> for Arc<T>
where
	T: ?Sized,
	T: NetworkStatusProvider<Block>,
{
	fn status<'life0, 'async_trait>(
		&'life0 self,
	) -> Pin<Box<dyn Future<Output = Result<NetworkStatus<Block>, ()>> + Send + 'async_trait>>
	where
		'life0: 'async_trait,
		Self: 'async_trait,
	{
		T::status(self)
	}
}

/// Provides low-level API for manipulating network peers.
pub trait NetworkPeers {
	/// Report a given peer as either beneficial (+) or costly (-) according to the
	/// given scalar.
	fn report_peer(&self, who: PeerId, cost_benefit: ReputationChange);

	/// Disconnect from a node as soon as possible.
	///
	/// This triggers the same effects as if the connection had closed itself spontaneously.
	///
	/// See also [`NetworkPeers::remove_from_peers_set`], which has the same effect but also
	/// prevents the local node from re-establishing an outgoing substream to this peer until it
	/// is added again.
	fn disconnect_peer(&self, who: PeerId, protocol: Cow<'static, str>);

	/// Connect to unreserved peers and allow unreserved peers to connect for syncing purposes.
	fn accept_unreserved_peers(&self);

	/// Disconnect from unreserved peers and deny new unreserved peers to connect for syncing
	/// purposes.
	fn deny_unreserved_peers(&self);

	/// Adds a `PeerId` and its address as reserved. The string should encode the address
	/// and peer ID of the remote node.
	///
	/// Returns an `Err` if the given string is not a valid multiaddress
	/// or contains an invalid peer ID (which includes the local peer ID).
	fn add_reserved_peer(&self, peer: String) -> Result<(), String>;

	/// Removes a `PeerId` from the list of reserved peers.
	fn remove_reserved_peer(&self, peer_id: PeerId);

	/// Sets the reserved set of a protocol to the given set of peers.
	///
	/// Each `Multiaddr` must end with a `/p2p/` component containing the `PeerId`. It can also
	/// consist of only `/p2p/<peerid>`.
	///
	/// The node will start establishing/accepting connections and substreams to/from peers in this
	/// set, if it doesn't have any substream open with them yet.
	///
	/// Note however, if a call to this function results in less peers on the reserved set, they
	/// will not necessarily get disconnected (depending on available free slots in the peer set).
	/// If you want to also disconnect those removed peers, you will have to call
	/// `remove_from_peers_set` on those in addition to updating the reserved set. You can omit
	/// this step if the peer set is in reserved only mode.
	///
	/// Returns an `Err` if one of the given addresses is invalid or contains an
	/// invalid peer ID (which includes the local peer ID).
	fn set_reserved_peers(
		&self,
		protocol: Cow<'static, str>,
		peers: HashSet<Multiaddr>,
	) -> Result<(), String>;

	/// Add peers to a peer set.
	///
	/// Each `Multiaddr` must end with a `/p2p/` component containing the `PeerId`. It can also
	/// consist of only `/p2p/<peerid>`.
	///
	/// Returns an `Err` if one of the given addresses is invalid or contains an
	/// invalid peer ID (which includes the local peer ID).
	fn add_peers_to_reserved_set(
		&self,
		protocol: Cow<'static, str>,
		peers: HashSet<Multiaddr>,
	) -> Result<(), String>;

	/// Remove peers from a peer set.
	fn remove_peers_from_reserved_set(&self, protocol: Cow<'static, str>, peers: Vec<PeerId>);

	/// Add a peer to a set of peers.
	///
	/// If the set has slots available, it will try to open a substream with this peer.
	///
	/// Each `Multiaddr` must end with a `/p2p/` component containing the `PeerId`. It can also
	/// consist of only `/p2p/<peerid>`.
	///
	/// Returns an `Err` if one of the given addresses is invalid or contains an
	/// invalid peer ID (which includes the local peer ID).
	fn add_to_peers_set(
		&self,
		protocol: Cow<'static, str>,
		peers: HashSet<Multiaddr>,
	) -> Result<(), String>;

	/// Remove peers from a peer set.
	///
	/// If we currently have an open substream with this peer, it will soon be closed.
	fn remove_from_peers_set(&self, protocol: Cow<'static, str>, peers: Vec<PeerId>);

	/// Returns the number of peers we're connected to.
	fn num_connected(&self) -> usize;
}

// Manual implementation to avoid extra boxing here
impl<T> NetworkPeers for Arc<T>
where
	T: ?Sized,
	T: NetworkPeers,
{
	fn report_peer(&self, who: PeerId, cost_benefit: ReputationChange) {
		T::report_peer(self, who, cost_benefit)
	}

	fn disconnect_peer(&self, who: PeerId, protocol: Cow<'static, str>) {
		T::disconnect_peer(self, who, protocol)
	}

	fn accept_unreserved_peers(&self) {
		T::accept_unreserved_peers(self)
	}

	fn deny_unreserved_peers(&self) {
		T::deny_unreserved_peers(self)
	}

	fn add_reserved_peer(&self, peer: String) -> Result<(), String> {
		T::add_reserved_peer(self, peer)
	}

	fn remove_reserved_peer(&self, peer_id: PeerId) {
		T::remove_reserved_peer(self, peer_id)
	}

	fn set_reserved_peers(
		&self,
		protocol: Cow<'static, str>,
		peers: HashSet<Multiaddr>,
	) -> Result<(), String> {
		T::set_reserved_peers(self, protocol, peers)
	}

	fn add_peers_to_reserved_set(
		&self,
		protocol: Cow<'static, str>,
		peers: HashSet<Multiaddr>,
	) -> Result<(), String> {
		T::add_peers_to_reserved_set(self, protocol, peers)
	}

	fn remove_peers_from_reserved_set(&self, protocol: Cow<'static, str>, peers: Vec<PeerId>) {
		T::remove_peers_from_reserved_set(self, protocol, peers)
	}

	fn add_to_peers_set(
		&self,
		protocol: Cow<'static, str>,
		peers: HashSet<Multiaddr>,
	) -> Result<(), String> {
		T::add_to_peers_set(self, protocol, peers)
	}

	fn remove_from_peers_set(&self, protocol: Cow<'static, str>, peers: Vec<PeerId>) {
		T::remove_from_peers_set(self, protocol, peers)
	}

	fn num_connected(&self) -> usize {
		T::num_connected(self)
	}
}
