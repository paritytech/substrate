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
use libp2p::PeerId;
pub use libp2p::{identity::error::SigningError, kad::record::Key as KademliaKey};
pub use signature::Signature;
use sp_runtime::traits::{Block as BlockT, NumberFor};
use std::{future::Future, pin::Pin, sync::Arc};

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
