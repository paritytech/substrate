// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Generic utilities for epoch-based consensus engines.

use std::{sync::Arc, ops::Add};
use parking_lot::Mutex;
use codec::{Encode, Decode};
use fork_tree::ForkTree;
use sc_client_api::utils::is_descendent_of;
use sp_blockchain::{HeaderMetadata, HeaderBackend, Error as ClientError};
use sp_runtime::traits::{Block as BlockT, NumberFor, One, Zero};

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
pub fn descendent_query<H, Block>(client: &H) -> HeaderBackendDescendentBuilder<&H, Block> {
	HeaderBackendDescendentBuilder(client, std::marker::PhantomData)
}

/// Wrapper to get around unconstrained type errors when implementing
/// `IsDescendentOfBuilder` for header backends.
pub struct HeaderBackendDescendentBuilder<H, Block>(H, std::marker::PhantomData<Block>);

impl<'a, H, Block> IsDescendentOfBuilder<Block::Hash>
	for HeaderBackendDescendentBuilder<&'a H, Block> where
	H: HeaderBackend<Block> + HeaderMetadata<Block, Error=ClientError>,
	Block: BlockT,
{
	type Error = ClientError;
	type IsDescendentOf = Box<dyn Fn(&Block::Hash, &Block::Hash) -> Result<bool, ClientError> + 'a>;

	fn build_is_descendent_of(&self, current: Option<(Block::Hash, Block::Hash)>)
		-> Self::IsDescendentOf
	{
		Box::new(is_descendent_of(self.0, current))
	}
}

/// Epoch data, distinguish whether it is genesis or not.
pub trait Epoch {
	/// Descriptor for the next epoch.
	type NextEpochDescriptor;
	/// Type of the slot number.
	type SlotNumber: Ord;

	/// Increment the epoch data, using the next epoch descriptor.
	fn increment(&self, descriptor: Self::NextEpochDescriptor) -> Self;

	/// Produce the "end slot" of the epoch. This is NOT inclusive to the epoch,
	/// i.e. the slots covered by the epoch are `self.start_slot() .. self.end_slot()`.
	fn end_slot(&self) -> Self::SlotNumber;
	/// Produce the "start slot" of the epoch.
	fn start_slot(&self) -> Self::SlotNumber;
}

/// An unimported genesis epoch.
pub struct UnimportedGenesisEpoch<Epoch>(Epoch);

/// The viable epoch under which a block can be verified.
///
/// If this is the first non-genesis block in the chain, then it will
/// hold an `UnimportedGenesis` epoch.
pub enum ViableEpoch<Epoch> {
	/// Genesis viable epoch data.
	Genesis(UnimportedGenesisEpoch<Epoch>),
	/// Regular viable epoch data.
	Regular(Epoch),
}

impl<Epoch> From<Epoch> for ViableEpoch<Epoch> {
	fn from(epoch: Epoch) -> ViableEpoch<Epoch> {
		ViableEpoch::Regular(epoch)
	}
}

impl<Epoch> AsRef<Epoch> for ViableEpoch<Epoch> {
	fn as_ref(&self) -> &Epoch {
		match *self {
			ViableEpoch::Genesis(UnimportedGenesisEpoch(ref e)) => e,
			ViableEpoch::Regular(ref e) => e,
		}
	}
}

impl<Epoch> ViableEpoch<Epoch> where
	Epoch: crate::Epoch + Clone,
{
	/// Extract the underlying epoch, disregarding the fact that a genesis
	/// epoch may be unimported.
	pub fn into_inner(self) -> Epoch {
		match self {
			ViableEpoch::Genesis(UnimportedGenesisEpoch(e)) => e,
			ViableEpoch::Regular(e) => e,
		}
	}

	/// Increment the epoch, yielding an `IncrementedEpoch` to be imported
	/// into the fork-tree.
	pub fn increment(
		&self,
		next_descriptor: Epoch::NextEpochDescriptor
	) -> IncrementedEpoch<Epoch> {
		let next = self.as_ref().increment(next_descriptor);
		let to_persist = match *self {
			ViableEpoch::Genesis(UnimportedGenesisEpoch(ref epoch_0)) =>
				PersistedEpoch::Genesis(epoch_0.clone(), next),
			ViableEpoch::Regular(_) => PersistedEpoch::Regular(next),
		};

		IncrementedEpoch(to_persist)
	}
}

/// The data type encoded on disk.
#[derive(Clone, Encode, Decode)]
pub enum PersistedEpoch<Epoch> {
	/// Genesis persisted epoch data. epoch_0, epoch_1.
	Genesis(Epoch, Epoch),
	/// Regular persisted epoch data. epoch_n.
	Regular(Epoch),
}

/// A fresh, incremented epoch to import into the underlying fork-tree.
///
/// Create this with `ViableEpoch::increment`.
#[must_use = "Freshly-incremented epoch must be imported with `EpochChanges::import`"]
pub struct IncrementedEpoch<Epoch>(PersistedEpoch<Epoch>);

impl<Epoch> AsRef<Epoch> for IncrementedEpoch<Epoch> {
	fn as_ref(&self) -> &Epoch {
		match self.0 {
			PersistedEpoch::Genesis(_, ref epoch_1) => epoch_1,
			PersistedEpoch::Regular(ref epoch_n) => epoch_n,
		}
	}
}

/// Tree of all epoch changes across all *seen* forks. Data stored in tree is
/// the hash and block number of the block signaling the epoch change, and the
/// epoch that was signalled at that block.
///
/// The first epoch, epoch_0, is special cased by saying that it starts at
/// slot number of the first block in the chain. When bootstrapping a chain,
/// there can be multiple competing block #1s, so we have to ensure that the overlayed
/// DAG doesn't get confused.
///
/// The first block of every epoch should be producing a descriptor for the next
/// epoch - this is checked in higher-level code. So the first block of epoch_0 contains
/// a descriptor for epoch_1. We special-case these and bundle them together in the
/// same DAG entry, pinned to a specific block #1.
///
/// Further epochs (epoch_2, ..., epoch_n) each get their own entry.
#[derive(Clone, Encode, Decode)]
pub struct EpochChanges<Hash, Number, Epoch> {
	inner: ForkTree<Hash, Number, PersistedEpoch<Epoch>>,
}

// create a fake header hash which hasn't been included in the chain.
fn fake_head_hash<H: AsRef<[u8]> + AsMut<[u8]> + Clone>(parent_hash: &H) -> H {
	let mut h = parent_hash.clone();
	// dirty trick: flip the first bit of the parent hash to create a hash
	// which has not been in the chain before (assuming a strong hash function).
	h.as_mut()[0] ^= 0b10000000;
	h
}

impl<Hash, Number, Epoch> Default for EpochChanges<Hash, Number, Epoch> where
	Hash: PartialEq,
	Number: Ord,
{
	fn default() -> Self {
		EpochChanges { inner: ForkTree::new() }
	}
}

impl<Hash, Number, Epoch> EpochChanges<Hash, Number, Epoch> where
	Hash: PartialEq + AsRef<[u8]> + AsMut<[u8]> + Copy,
	Number: Ord + One + Zero + Add<Output=Number> + Copy,
	Epoch: crate::Epoch + Clone,
{
	/// Create a new epoch change.
	pub fn new() -> Self {
		Self::default()
	}

	/// Rebalances the tree of epoch changes so that it is sorted by length of
	/// fork (longest fork first).
	pub fn rebalance(&mut self) {
		self.inner.rebalance()
	}

	/// Prune out finalized epochs, except for the ancestor of the finalized
	/// block. The given slot should be the slot number at which the finalized
	/// block was authored.
	pub fn prune_finalized<D: IsDescendentOfBuilder<Hash>>(
		&mut self,
		descendent_of_builder: D,
		hash: &Hash,
		number: Number,
		slot: Epoch::SlotNumber,
	) -> Result<(), fork_tree::Error<D::Error>> {
		let is_descendent_of = descendent_of_builder
			.build_is_descendent_of(None);

		let predicate = |epoch: &PersistedEpoch<Epoch>| match *epoch {
			PersistedEpoch::Genesis(_, ref epoch_1) =>
				slot >= epoch_1.end_slot(),
			PersistedEpoch::Regular(ref epoch_n) =>
				slot >= epoch_n.end_slot(),
		};

		// prune any epochs which could not be _live_ as of the children of the
		// finalized block, i.e. re-root the fork tree to the oldest ancestor of
		// (hash, number) where epoch.end_slot() >= finalized_slot
		self.inner.prune(
			hash,
			&number,
			&is_descendent_of,
			&predicate,
		)?;

		Ok(())
	}

	/// Finds the epoch for a child of the given block, assuming the given slot number.
	///
	/// If the returned epoch is an `UnimportedGenesis` epoch, it should be imported into the
	/// tree.
	pub fn epoch_for_child_of<D: IsDescendentOfBuilder<Hash>, G>(
		&self,
		descendent_of_builder: D,
		parent_hash: &Hash,
		parent_number: Number,
		slot_number: Epoch::SlotNumber,
		make_genesis: G,
	) -> Result<Option<ViableEpoch<Epoch>>, fork_tree::Error<D::Error>>
		where G: FnOnce(Epoch::SlotNumber) -> Epoch
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
			return Ok(Some(ViableEpoch::Genesis(UnimportedGenesisEpoch(genesis_epoch))));
		}

		// We want to find the deepest node in the tree which is an ancestor
		// of our block and where the start slot of the epoch was before the
		// slot of our block. The genesis special-case doesn't need to look
		// at epoch_1 -- all we're doing here is figuring out which node
		// we need.
		let predicate = |epoch: &PersistedEpoch<Epoch>| match *epoch {
			PersistedEpoch::Genesis(ref epoch_0, _) =>
				epoch_0.start_slot() <= slot_number,
			PersistedEpoch::Regular(ref epoch_n) =>
				epoch_n.start_slot() <= slot_number,
		};

		self.inner.find_node_where(
			&fake_head_hash,
			&(parent_number + One::one()),
			&is_descendent_of,
			&predicate,
		)
			.map(|n| n.map(|node| ViableEpoch::Regular(match node.data {
				// Ok, we found our node.
				// and here we figure out which of the internal epochs
				// of a genesis node to use based on their start slot.
				PersistedEpoch::Genesis(ref epoch_0, ref epoch_1) =>
					if epoch_1.start_slot() <= slot_number {
						epoch_1.clone()
					} else {
						epoch_0.clone()
					},
				PersistedEpoch::Regular(ref epoch_n) => epoch_n.clone(),
			})))
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
		epoch: IncrementedEpoch<Epoch>,
	) -> Result<(), fork_tree::Error<D::Error>> {
		let is_descendent_of = descendent_of_builder
			.build_is_descendent_of(Some((hash, parent_hash)));

		let res = self.inner.import(
			hash,
			number,
			epoch.0,
			&is_descendent_of,
		);

		match res {
			Ok(_) | Err(fork_tree::Error::Duplicate) => Ok(()),
			Err(e) => Err(e),
		}
	}

	/// Return the inner fork tree.
	pub fn tree(&self) -> &ForkTree<Hash, Number, PersistedEpoch<Epoch>> {
		&self.inner
	}
}

/// Type alias to produce the epoch-changes tree from a block type.
pub type EpochChangesFor<Block, Epoch> = EpochChanges<<Block as BlockT>::Hash, NumberFor<Block>, Epoch>;

/// A shared epoch changes tree.
pub type SharedEpochChanges<Block, Epoch> = Arc<Mutex<EpochChangesFor<Block, Epoch>>>;

#[cfg(test)]
mod tests {
	use super::*;
	use super::Epoch as EpochT;

	#[derive(Debug, PartialEq)]
	pub struct TestError;

	impl std::fmt::Display for TestError {
		fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
			write!(f, "TestError")
		}
	}

	impl std::error::Error for TestError {}

	impl<'a, F: 'a , H: 'a + PartialEq + std::fmt::Debug> IsDescendentOfBuilder<H> for &'a F
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

				if let Some((ref c_head, ref c_parent)) = current {
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
	type SlotNumber = u64;

	#[derive(Debug, Clone, Eq, PartialEq)]
	struct Epoch {
		start_slot: SlotNumber,
		duration: SlotNumber,
	}

	impl EpochT for Epoch {
		type NextEpochDescriptor = ();
		type SlotNumber = SlotNumber;

		fn increment(&self, _: ()) -> Self {
			Epoch {
				start_slot: self.start_slot + self.duration,
				duration: self.duration,
			}
		}

		fn end_slot(&self) -> SlotNumber {
			self.start_slot + self.duration
		}

		fn start_slot(&self) -> SlotNumber {
			self.start_slot
		}
	}

	#[test]
	fn genesis_epoch_is_created_but_not_imported() {
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
			start_slot: slot,
			duration: 100,
		};

		let epoch_changes = EpochChanges::new();
		let genesis_epoch = epoch_changes.epoch_for_child_of(
			&is_descendent_of,
			b"0",
			0,
			10101,
			&make_genesis,
		).unwrap().unwrap();

		match genesis_epoch {
			ViableEpoch::Genesis(_) => {},
			_ => panic!("should be unimported genesis"),
		};
		assert_eq!(genesis_epoch.as_ref(), &make_genesis(10101));

		let genesis_epoch_2 = epoch_changes.epoch_for_child_of(
			&is_descendent_of,
			b"0",
			0,
			10102,
			&make_genesis,
		).unwrap().unwrap();

		match genesis_epoch_2 {
			ViableEpoch::Genesis(_) => {},
			_ => panic!("should be unimported genesis"),
		};
		assert_eq!(genesis_epoch_2.as_ref(), &make_genesis(10102));
	}

	#[test]
	fn epoch_changes_between_blocks() {
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
			start_slot: slot,
			duration: 100,
		};

		let mut epoch_changes = EpochChanges::new();
		let genesis_epoch = epoch_changes.epoch_for_child_of(
			&is_descendent_of,
			b"0",
			0,
			100,
			&make_genesis,
		).unwrap().unwrap();

		assert_eq!(genesis_epoch.as_ref(), &make_genesis(100));

		let import_epoch_1 = genesis_epoch.increment(());
		let epoch_1 = import_epoch_1.as_ref().clone();

		epoch_changes.import(
			&is_descendent_of,
			*b"A",
			1,
			*b"0",
			import_epoch_1,
		).unwrap();
		let genesis_epoch = genesis_epoch.into_inner();

		assert!(is_descendent_of(b"0", b"A").unwrap());

		let end_slot = genesis_epoch.end_slot();
		assert_eq!(end_slot, epoch_1.start_slot);

		{
			// x is still within the genesis epoch.
			let x = epoch_changes.epoch_for_child_of(
				&is_descendent_of,
				b"A",
				1,
				end_slot - 1,
				&make_genesis,
			).unwrap().unwrap().into_inner();

			assert_eq!(x, genesis_epoch);
		}

		{
			// x is now at the next epoch, because the block is now at the
			// start slot of epoch 1.
			let x = epoch_changes.epoch_for_child_of(
				&is_descendent_of,
				b"A",
				1,
				end_slot,
				&make_genesis,
			).unwrap().unwrap().into_inner();

			assert_eq!(x, epoch_1);
		}

		{
			// x is now at the next epoch, because the block is now after
			// start slot of epoch 1.
			let x = epoch_changes.epoch_for_child_of(
				&is_descendent_of,
				b"A",
				1,
				epoch_1.end_slot() - 1,
				&make_genesis,
			).unwrap().unwrap().into_inner();

			assert_eq!(x, epoch_1);
		}
	}

	#[test]
	fn two_block_ones_dont_conflict() {
		//     X - Y
		//   /
		// 0 - A - B
		//
		let is_descendent_of = |base: &Hash, block: &Hash| -> Result<bool, TestError> {
			match (base, *block) {
				(b"A", b) => Ok(b == *b"B"),
				(b"X", b) => Ok(b == *b"Y"),
				(b"0", _) => Ok(true),
				_ => Ok(false),
			}
		};

		let duration = 100;

		let make_genesis = |slot| Epoch {
			start_slot: slot,
			duration,
		};

		let mut epoch_changes = EpochChanges::new();
		let next_descriptor = ();

		// insert genesis epoch for A
		{
			let genesis_epoch_a = epoch_changes.epoch_for_child_of(
				&is_descendent_of,
				b"0",
				0,
				100,
				&make_genesis,
			).unwrap().unwrap();

			epoch_changes.import(
				&is_descendent_of,
				*b"A",
				1,
				*b"0",
				genesis_epoch_a.increment(next_descriptor.clone()),
			).unwrap();

		}

		// insert genesis epoch for X
		{
			let genesis_epoch_x = epoch_changes.epoch_for_child_of(
				&is_descendent_of,
				b"0",
				0,
				1000,
				&make_genesis,
			).unwrap().unwrap();

			epoch_changes.import(
				&is_descendent_of,
				*b"X",
				1,
				*b"0",
				genesis_epoch_x.increment(next_descriptor.clone()),
			).unwrap();
		}

		// now check that the genesis epochs for our respective block 1s
		// respect the chain structure.
		{
			let epoch_for_a_child = epoch_changes.epoch_for_child_of(
				&is_descendent_of,
				b"A",
				1,
				101,
				&make_genesis,
			).unwrap().unwrap();

			assert_eq!(epoch_for_a_child.into_inner(), make_genesis(100));

			let epoch_for_x_child = epoch_changes.epoch_for_child_of(
				&is_descendent_of,
				b"X",
				1,
				1001,
				&make_genesis,
			).unwrap().unwrap();

			assert_eq!(epoch_for_x_child.into_inner(), make_genesis(1000));

			let epoch_for_x_child_before_genesis = epoch_changes.epoch_for_child_of(
				&is_descendent_of,
				b"X",
				1,
				101,
				&make_genesis,
			).unwrap();

			// even though there is a genesis epoch at that slot, it's not in
			// this chain.
			assert!(epoch_for_x_child_before_genesis.is_none());
		}
	}
}
