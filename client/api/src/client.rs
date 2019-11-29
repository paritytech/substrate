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

//! A set of APIs supported by the client along with their primitives.

use std::collections::HashMap;
use futures::channel::mpsc;
use primitives::storage::StorageKey;
use sr_primitives::{
    traits::{Block as BlockT, NumberFor},
    generic::BlockId
};
use consensus::BlockOrigin;

use crate::blockchain::Info;
use crate::notifications::StorageEventStream;
use sp_blockchain;

/// Type that implements `futures::Stream` of block import events.
pub type ImportNotifications<Block> = mpsc::UnboundedReceiver<BlockImportNotification<Block>>;

/// A stream of block finality notifications.
pub type FinalityNotifications<Block> = mpsc::UnboundedReceiver<FinalityNotification<Block>>;

/// Expected hashes of blocks at given heights.
///
/// This may be used as chain spec extension to filter out known, unwanted forks.
pub type ForkBlocks<Block> = Option<HashMap<NumberFor<Block>, <Block as BlockT>::Hash>>;

/// Figure out the block type for a given type (for now, just a `Client`).
pub trait BlockOf {
	/// The type of the block.
	type Type: BlockT;
}

/// A source of blockchain events.
pub trait BlockchainEvents<Block: BlockT> {
	/// Get block import event stream. Not guaranteed to be fired for every
	/// imported block.
	fn import_notification_stream(&self) -> ImportNotifications<Block>;

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

/// Fetch block body by ID.
pub trait BlockBody<Block: BlockT> {
	/// Get block body by ID. Returns `None` if the body is not stored.
	fn block_body(&self,
		id: &BlockId<Block>
	) -> sp_blockchain::Result<Option<Vec<<Block as BlockT>::Extrinsic>>>;
}

/// Provide a list of potential uncle headers for a given block.
pub trait ProvideUncles<Block: BlockT> {
	/// Gets the uncles of the block with `target_hash` going back `max_generation` ancestors.
	fn uncles(&self, target_hash: Block::Hash, max_generation: NumberFor<Block>)
		-> sp_blockchain::Result<Vec<Block::Header>>;
}

/// Client info
#[derive(Debug)]
pub struct ClientInfo<Block: BlockT> {
	/// Best block hash.
	pub chain: Info<Block>,
	/// State Cache Size currently used by the backend
	pub used_state_cache_size: Option<usize>,
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
	/// List of retracted blocks ordered by block number.
	pub retracted: Vec<Block::Hash>,
}

/// Summary of a finalized block.
#[derive(Clone, Debug)]
pub struct FinalityNotification<Block: BlockT> {
	/// Imported block header hash.
	pub hash: Block::Hash,
	/// Imported block header.
	pub header: Block::Header,
}
