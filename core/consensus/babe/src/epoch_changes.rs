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
use sr_primitives::traits::{Block as BlockT, NumberFor, One, Zero};
use codec::{Encode, Decode};
use client::error::Error as ClientError;
use client::utils as client_utils;
use client::blockchain::HeaderBackend;
use primitives::H256;
use std::ops::Add;

/// A builder for `is_descendent_of` functions.
pub trait IsDescendentOfBuilder<Hash> {
	/// The error returned by the function.
	type Error: std::error::Error;
	/// A function that can tell you if the second parameter is a descendent of
	/// the first.
	type IsDescendentOf: Fn(&Hash, &Hash) -> Result<bool, Self::Error>;

	/// Build an `is_descendent_of` function.
	///
	/// The `current` parameter can be `Some` with the details a fresh block whose
	/// details aren't yet stored, but its parent is.
	///
	/// The format of `current` when `Some` is `(current, current_parent)`.
	fn build_is_descendent_of(&self, current: Option<(Hash, Hash)>)
		-> Self::IsDescendentOf;
}

/// Produce a descendent query object given the client.
pub(crate) fn descendent_query<H, Block>(client: &H) -> HeaderBackendDescendentBuilder<&H, Block> {
	HeaderBackendDescendentBuilder(client, std::marker::PhantomData)
}

/// Wrapper to get around unconstrained type errors when implementing
/// `IsDescendentOfBuilder` for header backends.
pub(crate) struct HeaderBackendDescendentBuilder<H, Block>(H, std::marker::PhantomData<Block>);

// TODO: relying on Hash = H256 is awful.
// https://github.com/paritytech/substrate/issues/3624
impl<'a, H, Block> IsDescendentOfBuilder<H256>
	for HeaderBackendDescendentBuilder<&'a H, Block> where
	H: HeaderBackend<Block>,
	Block: BlockT<Hash = H256>,
{
	type Error = ClientError;
	type IsDescendentOf = Box<dyn Fn(&H256, &H256) -> Result<bool, ClientError> + 'a>;

	fn build_is_descendent_of(&self, current: Option<(H256, H256)>)
		-> Self::IsDescendentOf
	{
		Box::new(client_utils::is_descendent_of(self.0, current))
	}
}

/// Tree of all epoch changes across all *seen* forks. Data stored in tree is
/// the hash and block number of the block signaling the epoch change, and the
/// epoch that was signalled at that block.
#[derive(Clone, Encode, Decode)]
pub struct EpochChanges<Hash, Number> {
	inner: ForkTree<Hash, Number, Epoch>,
}

// create a fake header hash which hasn't been included in the chain.
fn fake_head_hash<H: AsRef<[u8]> + AsMut<[u8]> + Clone>(parent_hash: &H) -> H {
	let mut h = parent_hash.clone();
	// dirty trick: flip the first bit of the parent hash to create a hash
	// which has not been in the chain before (assuming a strong hash function).
	h.as_mut()[0] ^= 0b10000000;
	h
}

impl<Hash, Number> EpochChanges<Hash, Number> where
	Hash: PartialEq + AsRef<[u8]> + AsMut<[u8]> + Copy,
	Number: Ord + One + Zero + Add<Output=Number> + Copy,
{
	/// Create a new epoch-change tracker.
	fn new() -> Self {
		EpochChanges { inner: ForkTree::new() }
	}

	/// Prune out finalized epochs, except for the ancestor of the finalized block.
	pub fn prune_finalized<D: IsDescendentOfBuilder<Hash>>(
		&mut self,
		descendent_of_builder: D,
		_hash: &Hash,
		_number: Number,
	) -> Result<(), fork_tree::Error<D::Error>> {
		let _is_descendent_of = descendent_of_builder
			.build_is_descendent_of(None);

		// TODO:
		// https://github.com/paritytech/substrate/issues/3651
		//
		// prune any epochs which could not be _live_ as of the children of the
		// finalized block.
		// i.e. re-root the fork tree to the oldest ancestor of (hash, number)
		// where epoch.start_slot + epoch.duration >= slot(hash)

		Ok(())
	}

	/// Finds the epoch for a child of the given block, assuming the given slot number.
	pub fn epoch_for_child_of<D: IsDescendentOfBuilder<Hash>, G>(
		&mut self,
		descendent_of_builder: D,
		parent_hash: &Hash,
		parent_number: Number,
		slot_number: SlotNumber,
		make_genesis: G,
	) -> Result<Option<Epoch>, fork_tree::Error<D::Error>>
		where G: FnOnce(SlotNumber) -> Epoch
	{
		// find_node_where will give you the node in the fork-tree which is an ancestor
		// of the `parent_hash` by default. if the last epoch was signalled at the parent_hash,
		// then it won't be returned. we need to create a new fake chain head hash which
		// "descends" from our parent-hash.
		let fake_head_hash = fake_head_hash(parent_hash);

		let is_descendent_of = descendent_of_builder
			.build_is_descendent_of(Some((fake_head_hash, *parent_hash)));

		if parent_number == Zero::zero() {
			// need to insert the genesis epoch.
			let genesis_epoch = make_genesis(slot_number);
			let res = self.inner.import(
				*parent_hash,
				parent_number,
				genesis_epoch.clone(),
				&is_descendent_of,
			);

			match res {
				Ok(_) | Err(fork_tree::Error::Duplicate) => {},
				Err(e) => return Err(e),
			}

			return Ok(Some(genesis_epoch))
		}


		self.inner.find_node_where(
			&fake_head_hash,
			&(parent_number + One::one()),
			&is_descendent_of,
			&|epoch| epoch.start_slot <= slot_number,
		)
			.map(|n| n.map(|n| n.data.clone()))
	}

	/// Import a new epoch-change, signalled at the given block.
	///
	/// This assumes that the given block is prospective (i.e. has not been
	/// imported yet), but its parent has. This is why the parent hash needs
	/// to be provided.
	pub fn import<D: IsDescendentOfBuilder<Hash>>(
		&mut self,
		descendent_of_builder: D,
		hash: Hash,
		number: Number,
		parent_hash: Hash,
		epoch: Epoch,
	) -> Result<(), fork_tree::Error<D::Error>> {
		let is_descendent_of = descendent_of_builder
			.build_is_descendent_of(Some((hash, parent_hash)));

		let res = self.inner.import(
			hash,
			number,
			epoch,
			&is_descendent_of,
		);

		match res {
			Ok(_) | Err(fork_tree::Error::Duplicate) => Ok(()),
			Err(e) => Err(e),
		}
	}
}

pub type EpochChangesFor<Block> = EpochChanges<<Block as BlockT>::Hash, NumberFor<Block>>;

/// A shared epoch changes tree.
#[derive(Clone)]
pub struct SharedEpochChanges<Block: BlockT> {
	inner: Arc<Mutex<EpochChangesFor<Block>>>,
}

impl<Block: BlockT> SharedEpochChanges<Block> {
	/// Create a new instance of the `SharedEpochChanges`.
	pub fn new() -> Self {
		SharedEpochChanges {
			inner: Arc::new(Mutex::new(EpochChanges::<_, _>::new()))
		}
	}

	/// Lock the shared epoch changes,
	pub fn lock(&self) -> MutexGuard<EpochChangesFor<Block>> {
		self.inner.lock()
	}
}

impl<Block: BlockT> From<EpochChangesFor<Block>> for SharedEpochChanges<Block> {
	fn from(epoch_changes: EpochChangesFor<Block>) -> Self {
		SharedEpochChanges {
			inner: Arc::new(Mutex::new(epoch_changes))
		}
	}
}

// TODO: write tests within the scope of this module.
//
// 1. mock up an `IsDescendentOfBuilder`. Don't use the `Client` - these tests should be
// minimal and focused.
//
// 2. test that epochs can indeed change between blocks by observing one result before
// epoch end slot and another after
//
// 3. Test that this always gives you the right epoch based on the fork you're on.
#[cfg(test)]
mod tests {
	use super::*;

	#[derive(Debug, PartialEq)]
	pub struct TestError;

	impl std::fmt::Display for TestError {
		fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
			write!(f, "TestError")
		}
	}

	impl std::error::Error for TestError {}

	impl<'a, F: 'a , H: 'a + PartialEq> IsDescendentOfBuilder<H> for &'a F
		where F: Fn(&H, &H) -> Result<bool, TestError>
	{
		type Error = TestError;
		type IsDescendentOf = Box<dyn Fn(&H, &H) -> Result<bool, TestError> + 'a>;

		fn build_is_descendent_of(&self, current: Option<(H, H)>)
			-> Self::IsDescendentOf
		{
			let f = *self;
			Box::new(move |base, head| {
				let mut head = head;
				if let Some((ref c_parent, ref c_head)) = current {
					if head == c_head {
						if base == c_parent {
							return Ok(true);
						} else {
							head = c_parent;
						}
					}
				}

				f(base, head)
			})
		}
	}

	type Hash = [u8; 1];

	#[test]
	fn genesis_epoch_is_inserted_and_persisted() {
		//
		// A - B
		//  \
		//   — C
		//
		let is_descendent_of = |base: &Hash, block: &Hash| -> Result<bool, TestError> {
			match (base, *block) {
				(b"A", b) => Ok(b == *b"B" || b == *b"C" || b == *b"D"),
				(b"B", b) | (b"C", b) => Ok(b == *b"D"),
				(b"0", _) => Ok(true),
				_ => Ok(false),
			}
		};

		let make_genesis = |slot| Epoch {
			epoch_index: 0,
			start_slot: slot,
			duration: 100,
			authorities: Vec::new(),
			randomness: [0; 32],
		};

		let mut epoch_changes = EpochChanges::new();
		let genesis_epoch = epoch_changes.epoch_for_child_of(
			&is_descendent_of,
			b"0",
			0,
			10101,
			&make_genesis,
		).unwrap().unwrap();

		assert_eq!(genesis_epoch, make_genesis(10101));

		let block_in_genesis_epoch = epoch_changes.epoch_for_child_of(
			&is_descendent_of,
			b"A",
			1,
			10102,
			&make_genesis,
		).unwrap().unwrap();

		assert_eq!(block_in_genesis_epoch, genesis_epoch);
	}
}
