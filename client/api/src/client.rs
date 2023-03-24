// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! A set of APIs supported by the client along with their primitives.

use sp_consensus::BlockOrigin;
use sp_core::storage::StorageKey;
use sp_runtime::{
	generic::SignedBlock,
	traits::{Block as BlockT, NumberFor},
	Justifications,
};
use std::{collections::HashSet, fmt, sync::Arc};

use crate::{blockchain::Info, notifications::StorageEventStream, FinalizeSummary, ImportSummary};

use sc_transaction_pool_api::ChainEvent;
use sc_utils::mpsc::{TracingUnboundedReceiver, TracingUnboundedSender};
use sp_blockchain;

/// Type that implements `futures::Stream` of block import events.
pub type ImportNotifications<Block> = TracingUnboundedReceiver<BlockImportNotification<Block>>;

/// A stream of block finality notifications.
pub type FinalityNotifications<Block> = TracingUnboundedReceiver<FinalityNotification<Block>>;

/// Expected hashes of blocks at given heights.
///
/// This may be used as chain spec extension to set trusted checkpoints, i.e.
/// the client will refuse to import a block with a different hash at the given
/// height.
pub type ForkBlocks<Block> = Option<Vec<(NumberFor<Block>, <Block as BlockT>::Hash)>>;

/// Known bad block hashes.
///
/// This may be used as chain spec extension to filter out known, unwanted forks.
pub type BadBlocks<Block> = Option<HashSet<<Block as BlockT>::Hash>>;

/// Figure out the block type for a given type (for now, just a `Client`).
pub trait BlockOf {
	/// The type of the block.
	type Type: BlockT;
}

/// A source of blockchain events.
pub trait BlockchainEvents<Block: BlockT> {
	/// Get block import event stream.
	///
	/// Not guaranteed to be fired for every imported block, only fired when the node
	/// has synced to the tip or there is a re-org. Use `every_import_notification_stream()`
	/// if you want a notification of every imported block regardless.
	fn import_notification_stream(&self) -> ImportNotifications<Block>;

	/// Get a stream of every imported block.
	fn every_import_notification_stream(&self) -> ImportNotifications<Block>;

	/// Get a stream of finality notifications. Not guaranteed to be fired for every
	/// finalized block.
	fn finality_notification_stream(&self) -> FinalityNotifications<Block>;

	/// Get storage changes event stream.
	///
	/// Passing `None` as `filter_keys` subscribes to all storage changes.
	fn storage_changes_notification_stream(
		&self,
		filter_keys: Option<&[StorageKey]>,
		child_filter_keys: Option<&[(StorageKey, Option<Vec<StorageKey>>)]>,
	) -> sp_blockchain::Result<StorageEventStream<Block::Hash>>;
}

/// List of operations to be performed on storage aux data.
/// First tuple element is the encoded data key.
/// Second tuple element is the encoded optional data to write.
/// If `None`, the key and the associated data are deleted from storage.
pub type AuxDataOperations = Vec<(Vec<u8>, Option<Vec<u8>>)>;

/// Callback invoked before committing the operations created during block import.
/// This gives the opportunity to perform auxiliary pre-commit actions and optionally
/// enqueue further storage write operations to be atomically performed on commit.
pub type OnImportAction<Block> =
	Box<dyn (Fn(&BlockImportNotification<Block>) -> AuxDataOperations) + Send>;

/// Callback invoked before committing the operations created during block finalization.
/// This gives the opportunity to perform auxiliary pre-commit actions and optionally
/// enqueue further storage write operations to be atomically performed on commit.
pub type OnFinalityAction<Block> =
	Box<dyn (Fn(&FinalityNotification<Block>) -> AuxDataOperations) + Send>;

/// Interface to perform auxiliary actions before committing a block import or
/// finality operation.
pub trait PreCommitActions<Block: BlockT> {
	/// Actions to be performed on block import.
	fn register_import_action(&self, op: OnImportAction<Block>);

	/// Actions to be performed on block finalization.
	fn register_finality_action(&self, op: OnFinalityAction<Block>);
}

/// Interface for fetching block data.
pub trait BlockBackend<Block: BlockT> {
	/// Get block body by ID. Returns `None` if the body is not stored.
	fn block_body(
		&self,
		hash: Block::Hash,
	) -> sp_blockchain::Result<Option<Vec<<Block as BlockT>::Extrinsic>>>;

	/// Get all indexed transactions for a block,
	/// including renewed transactions.
	///
	/// Note that this will only fetch transactions
	/// that are indexed by the runtime with `storage_index_transaction`.
	fn block_indexed_body(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<Vec<Vec<u8>>>>;

	/// Get full block by hash.
	fn block(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<SignedBlock<Block>>>;

	/// Get block status by block hash.
	fn block_status(&self, hash: Block::Hash) -> sp_blockchain::Result<sp_consensus::BlockStatus>;

	/// Get block justifications for the block with the given hash.
	fn justifications(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<Justifications>>;

	/// Get block hash by number.
	fn block_hash(&self, number: NumberFor<Block>) -> sp_blockchain::Result<Option<Block::Hash>>;

	/// Get single indexed transaction by content hash.
	///
	/// Note that this will only fetch transactions
	/// that are indexed by the runtime with `storage_index_transaction`.
	fn indexed_transaction(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<Vec<u8>>>;

	/// Check if transaction index exists.
	fn has_indexed_transaction(&self, hash: Block::Hash) -> sp_blockchain::Result<bool> {
		Ok(self.indexed_transaction(hash)?.is_some())
	}

	/// Tells whether the current client configuration requires full-sync mode.
	fn requires_full_sync(&self) -> bool;
}

/// Provide a list of potential uncle headers for a given block.
pub trait ProvideUncles<Block: BlockT> {
	/// Gets the uncles of the block with `target_hash` going back `max_generation` ancestors.
	fn uncles(
		&self,
		target_hash: Block::Hash,
		max_generation: NumberFor<Block>,
	) -> sp_blockchain::Result<Vec<Block::Header>>;
}

/// Client info
#[derive(Debug)]
pub struct ClientInfo<Block: BlockT> {
	/// Best block hash.
	pub chain: Info<Block>,
	/// Usage info, if backend supports this.
	pub usage: Option<UsageInfo>,
}

/// A wrapper to store the size of some memory.
#[derive(Default, Clone, Debug, Copy)]
pub struct MemorySize(usize);

impl MemorySize {
	/// Creates `Self` from the given `bytes` size.
	pub fn from_bytes(bytes: usize) -> Self {
		Self(bytes)
	}

	/// Returns the memory size as bytes.
	pub fn as_bytes(self) -> usize {
		self.0
	}
}

impl fmt::Display for MemorySize {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		if self.0 < 1024 {
			write!(f, "{} bytes", self.0)
		} else if self.0 < 1024 * 1024 {
			write!(f, "{:.2} KiB", self.0 as f64 / 1024f64)
		} else if self.0 < 1024 * 1024 * 1024 {
			write!(f, "{:.2} MiB", self.0 as f64 / (1024f64 * 1024f64))
		} else {
			write!(f, "{:.2} GiB", self.0 as f64 / (1024f64 * 1024f64 * 1024f64))
		}
	}
}

/// Memory statistics for client instance.
#[derive(Default, Clone, Debug)]
pub struct MemoryInfo {
	/// Size of state cache.
	pub state_cache: MemorySize,
	/// Size of backend database cache.
	pub database_cache: MemorySize,
}

/// I/O statistics for client instance.
#[derive(Default, Clone, Debug)]
pub struct IoInfo {
	/// Number of transactions.
	pub transactions: u64,
	/// Total bytes read from disk.
	pub bytes_read: u64,
	/// Total bytes written to disk.
	pub bytes_written: u64,
	/// Total key writes to disk.
	pub writes: u64,
	/// Total key reads from disk.
	pub reads: u64,
	/// Average size of the transaction.
	pub average_transaction_size: u64,
	/// State reads (keys)
	pub state_reads: u64,
	/// State reads (keys) from cache.
	pub state_reads_cache: u64,
	/// State reads (keys)
	pub state_writes: u64,
	/// State write (keys) already cached.
	pub state_writes_cache: u64,
	/// State write (trie nodes) to backend db.
	pub state_writes_nodes: u64,
}

/// Usage statistics for running client instance.
///
/// Returning backend determines the scope of these stats,
/// but usually it is either from service start or from previous
/// gathering of the statistics.
#[derive(Default, Clone, Debug)]
pub struct UsageInfo {
	/// Memory statistics.
	pub memory: MemoryInfo,
	/// I/O statistics.
	pub io: IoInfo,
}

impl fmt::Display for UsageInfo {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(
			f,
			"caches: ({} state, {} db overlay), \
			 i/o: ({} tx, {} write, {} read, {} avg tx, {}/{} key cache reads/total, {} trie nodes writes)",
			self.memory.state_cache,
			self.memory.database_cache,
			self.io.transactions,
			self.io.bytes_written,
			self.io.bytes_read,
			self.io.average_transaction_size,
			self.io.state_reads_cache,
			self.io.state_reads,
			self.io.state_writes_nodes,
		)
	}
}

/// Sends a message to the pinning-worker once dropped to unpin a block in the backend.
#[derive(Debug)]
pub struct UnpinHandleInner<Block: BlockT> {
	/// Hash of the block pinned by this handle
	hash: Block::Hash,
	unpin_worker_sender: TracingUnboundedSender<Block::Hash>,
}

impl<Block: BlockT> UnpinHandleInner<Block> {
	/// Create a new [`UnpinHandleInner`]
	pub fn new(
		hash: Block::Hash,
		unpin_worker_sender: TracingUnboundedSender<Block::Hash>,
	) -> Self {
		Self { hash, unpin_worker_sender }
	}
}

impl<Block: BlockT> Drop for UnpinHandleInner<Block> {
	fn drop(&mut self) {
		if let Err(err) = self.unpin_worker_sender.unbounded_send(self.hash) {
			log::debug!(target: "db", "Unable to unpin block with hash: {}, error: {:?}", self.hash, err);
		};
	}
}

/// Keeps a specific block pinned while the handle is alive.
/// Once the last handle instance for a given block is dropped, the
/// block is unpinned in the [`Backend`](crate::backend::Backend::unpin_block).
#[derive(Debug, Clone)]
pub struct UnpinHandle<Block: BlockT>(Arc<UnpinHandleInner<Block>>);

impl<Block: BlockT> UnpinHandle<Block> {
	/// Create a new [`UnpinHandle`]
	pub fn new(
		hash: Block::Hash,
		unpin_worker_sender: TracingUnboundedSender<Block::Hash>,
	) -> UnpinHandle<Block> {
		UnpinHandle(Arc::new(UnpinHandleInner::new(hash, unpin_worker_sender)))
	}

	/// Hash of the block this handle is unpinning on drop
	pub fn hash(&self) -> Block::Hash {
		self.0.hash
	}
}

/// Summary of an imported block
#[derive(Clone, Debug)]
pub struct BlockImportNotification<Block: BlockT> {
	/// Imported block header hash.
	pub hash: Block::Hash,
	/// Imported block origin.
	pub origin: BlockOrigin,
	/// Imported block header.
	pub header: Block::Header,
	/// Is this the new best block.
	pub is_new_best: bool,
	/// Tree route from old best to new best parent.
	///
	/// If `None`, there was no re-org while importing.
	pub tree_route: Option<Arc<sp_blockchain::TreeRoute<Block>>>,
	/// Handle to unpin the block this notification is for
	unpin_handle: UnpinHandle<Block>,
}

impl<Block: BlockT> BlockImportNotification<Block> {
	/// Create new notification
	pub fn new(
		hash: Block::Hash,
		origin: BlockOrigin,
		header: Block::Header,
		is_new_best: bool,
		tree_route: Option<Arc<sp_blockchain::TreeRoute<Block>>>,
		unpin_worker_sender: TracingUnboundedSender<Block::Hash>,
	) -> Self {
		Self {
			hash,
			origin,
			header,
			is_new_best,
			tree_route,
			unpin_handle: UnpinHandle::new(hash, unpin_worker_sender),
		}
	}

	/// Consume this notification and extract the unpin handle.
	///
	/// Note: Only use this if you want to keep the block pinned in the backend.
	pub fn into_unpin_handle(self) -> UnpinHandle<Block> {
		self.unpin_handle
	}
}

/// Summary of a finalized block.
#[derive(Clone, Debug)]
pub struct FinalityNotification<Block: BlockT> {
	/// Finalized block header hash.
	pub hash: Block::Hash,
	/// Finalized block header.
	pub header: Block::Header,
	/// Path from the old finalized to new finalized parent (implicitly finalized blocks).
	///
	/// This maps to the range `(old_finalized, new_finalized)`.
	pub tree_route: Arc<[Block::Hash]>,
	/// Stale branches heads.
	pub stale_heads: Arc<[Block::Hash]>,
	/// Handle to unpin the block this notification is for
	unpin_handle: UnpinHandle<Block>,
}

impl<B: BlockT> TryFrom<BlockImportNotification<B>> for ChainEvent<B> {
	type Error = ();

	fn try_from(n: BlockImportNotification<B>) -> Result<Self, ()> {
		if n.is_new_best {
			Ok(Self::NewBestBlock { hash: n.hash, tree_route: n.tree_route })
		} else {
			Err(())
		}
	}
}

impl<B: BlockT> From<FinalityNotification<B>> for ChainEvent<B> {
	fn from(n: FinalityNotification<B>) -> Self {
		Self::Finalized { hash: n.hash, tree_route: n.tree_route }
	}
}

impl<Block: BlockT> FinalityNotification<Block> {
	/// Create finality notification from finality summary.
	pub fn from_summary(
		mut summary: FinalizeSummary<Block>,
		unpin_worker_sender: TracingUnboundedSender<Block::Hash>,
	) -> FinalityNotification<Block> {
		let hash = summary.finalized.pop().unwrap_or_default();
		FinalityNotification {
			hash,
			header: summary.header,
			tree_route: Arc::from(summary.finalized),
			stale_heads: Arc::from(summary.stale_heads),
			unpin_handle: UnpinHandle::new(hash, unpin_worker_sender),
		}
	}

	/// Consume this notification and extract the unpin handle.
	///
	/// Note: Only use this if you want to keep the block pinned in the backend.
	pub fn into_unpin_handle(self) -> UnpinHandle<Block> {
		self.unpin_handle
	}
}

impl<Block: BlockT> BlockImportNotification<Block> {
	/// Create finality notification from finality summary.
	pub fn from_summary(
		summary: ImportSummary<Block>,
		unpin_worker_sender: TracingUnboundedSender<Block::Hash>,
	) -> BlockImportNotification<Block> {
		let hash = summary.hash;
		BlockImportNotification {
			hash,
			origin: summary.origin,
			header: summary.header,
			is_new_best: summary.is_new_best,
			tree_route: summary.tree_route.map(Arc::new),
			unpin_handle: UnpinHandle::new(hash, unpin_worker_sender),
		}
	}
}
