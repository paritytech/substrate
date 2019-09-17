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

//! Handling epoch changes in BABE.
//!
//! This exposes the `SharedEpochChanges`, which is a wrapper around a
//! persistent DAG superimposed over the forks of the blockchain.

use std::sync::Arc;
use babe_primitives::{Epoch, SlotNumber};
use fork_tree::ForkTree;
use parking_lot::{Mutex, MutexGuard};
use sr_primitives::traits::{Block as BlockT, NumberFor};
use codec::{Encode, Decode};
use client::error::Error as ClientError;
use client::utils as client_utils;
use client::blockchain::HeaderBackend;
use primitives::H256;

/// A builder for `is_descendent_of` functions.
pub trait IsDescendentOfBuilder<Block: BlockT> {
	/// The error returned by the function.
	type Error: std::error::Error;
	/// A function that can tell you if the second parameter is a descendent of
	/// the first.
	type IsDescendentOf: Fn(&Block::Hash, &Block::Hash) -> Result<bool, Self::Error>;

	/// Build an `is_descendent_of` function.
	///
	/// The `current` parameter can be `Some` with the details a fresh block whose
	/// details aren't yet stored, but its parent is.
	///
	/// The format of `current` when `Some` is `(current, current_parent)`.
	fn build_is_descendent_of(&self, current: Option<(Block::Hash, Block::Hash)>)
		-> Self::IsDescendentOf;
}

// TODO: relying on Hash = H256 is awful.
// https://github.com/paritytech/substrate/issues/3624
impl<'a, Block: BlockT<Hash=H256>, T> IsDescendentOfBuilder<Block> for &'a T
	where T: HeaderBackend<Block>
{
	type Error = ClientError;
	type IsDescendentOf = Box<dyn Fn(&H256, &H256) -> Result<bool, ClientError> + 'a>;

	fn build_is_descendent_of(&self, current: Option<(H256, H256)>)
		-> Self::IsDescendentOf
	{
		Box::new(client_utils::is_descendent_of(*self, current))
	}
}

/// Tree of all epoch changes across all *seen* forks. Data stored in tree is
/// the hash and block number of the block signaling the epoch change, and the
/// epoch that was signalled at that block.
#[derive(Clone, Encode, Decode)]
pub struct EpochChanges<Block: BlockT> {
	inner: ForkTree<Block::Hash, NumberFor<Block>, Epoch>,
}

// create a fake header hash which hasn't been included in the chain.
fn fake_head_hash<H: AsRef<[u8]> + AsMut<[u8]> + Clone>(parent_hash: &H) -> H {
	let mut h = parent_hash.clone();
	// dirty trick: flip the first bit of the parent hash to create a hash
	// which has not been in the chain before (assuming a strong hash function).
	h.as_mut()[0] ^= 0b10000000;
	h
}

impl<Block: BlockT> EpochChanges<Block> {
	/// Create a new epoch-change tracker.
	fn new() -> Self {
		EpochChanges { inner: ForkTree::new() }
	}

	/// Prune out finalized epochs, except for the ancestor of the finalized block.
	pub fn prune_finalized<D: IsDescendentOfBuilder<Block>>(
		&mut self,
		descendent_of_builder: D,
		_hash: &Block::Hash,
		_number: NumberFor<Block>,
	) -> Result<(), fork_tree::Error<D::Error>> {
		let _is_descendent_of = descendent_of_builder
			.build_is_descendent_of(None);

		// TODO:
		// prune any epochs which could not be _live_ as of the children of the
		// finalized block.
		// i.e. re-root the fork tree to the earliest ancestor of (hash, number)
		// where epoch.start_slot + epoch.duration >= slot(hash)

		Ok(())
	}

	/// Finds the epoch for a child of the given block, assuming the given slot number.
	pub fn epoch_for_child_of<D: IsDescendentOfBuilder<Block>>(
		&mut self,
		descendent_of_builder: D,
		parent_hash: &Block::Hash,
		parent_number: NumberFor<Block>,
		slot_number: SlotNumber,
	) -> Result<Option<Epoch>, fork_tree::Error<D::Error>> {
		use sr_primitives::traits::One;

		// find_node_where will give you the node in the fork-tree which is an ancestor
		// of the `parent_hash` by default. if the last epoch was signalled at the parent_hash,
		// then it won't be returned. we need to create a new fake chain head hash which
		// "descends" from our parent-hash.
		let fake_head_hash = fake_head_hash(parent_hash);

		let is_descendent_of = descendent_of_builder
			.build_is_descendent_of(Some((fake_head_hash, *parent_hash)));

		self.inner.find_node_where(
			&fake_head_hash,
			&(parent_number + One::one()),
			&is_descendent_of,
			&|epoch| epoch.start_slot <= slot_number,
		)
			.map(|n| n.map(|n| n.data.clone()))
	}

	/// Import a new epoch-change, signalled at the given block.
	pub fn import<D: IsDescendentOfBuilder<Block>>(
		&mut self,
		descendent_of_builder: D,
		hash: Block::Hash,
		number: NumberFor<Block>,
		epoch: Epoch,
	) -> Result<(), fork_tree::Error<D::Error>> {
		let is_descendent_of = descendent_of_builder
			.build_is_descendent_of(None);

		self.inner.import(
			hash,
			number,
			epoch,
			&is_descendent_of,
		).map(|_| ())
	}
}

/// A shared epoch changes tree.
#[derive(Clone)]
pub struct SharedEpochChanges<Block: BlockT> {
	inner: Arc<Mutex<EpochChanges<Block>>>,
}

impl<Block: BlockT> SharedEpochChanges<Block> {
	/// Create a new instance of the `SharedEpochChanges`.
	pub fn new() -> Self {
		SharedEpochChanges {
			inner: Arc::new(Mutex::new(EpochChanges::<Block>::new()))
		}
	}

	/// Lock the shared epoch changes,
	pub fn lock(&self) -> MutexGuard<EpochChanges<Block>> {
		self.inner.lock()
	}
}

impl<Block: BlockT> From<EpochChanges<Block>> for SharedEpochChanges<Block> {
	fn from(epoch_changes: EpochChanges<Block>) -> Self {
		SharedEpochChanges {
			inner: Arc::new(Mutex::new(epoch_changes))
		}
	}
}
