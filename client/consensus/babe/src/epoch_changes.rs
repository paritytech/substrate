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
use babe_primitives::{Epoch, SlotNumber, NextEpochDescriptor};
use fork_tree::ForkTree;
use parking_lot::{Mutex, MutexGuard};
use sr_primitives::traits::{Block as BlockT, NumberFor, One, Zero};
use codec::{Encode, Decode};
use client_api::utils::is_descendent_of;
use sp_blockchain::{HeaderMetadata, HeaderBackend, Error as ClientError};
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
	H: HeaderBackend<Block> + HeaderMetadata<Block, Error=ClientError>,
	Block: BlockT<Hash = H256>,
{
	type Error = ClientError;
	type IsDescendentOf = Box<dyn Fn(&H256, &H256) -> Result<bool, ClientError> + 'a>;

	fn build_is_descendent_of(&self, current: Option<(H256, H256)>)
		-> Self::IsDescendentOf
	{
		Box::new(is_descendent_of(self.0, current))
	}
}

/// An unimported genesis epoch.
pub struct UnimportedGenesis(Epoch);

/// The viable epoch under which a block can be verified.
///
/// If this is the first non-genesis block in the chain, then it will
/// hold an `UnimportedGenesis` epoch.
pub enum ViableEpoch {
	Genesis(UnimportedGenesis),
	Regular(Epoch),
}

impl From<Epoch> for ViableEpoch {
	fn from(epoch: Epoch) -> ViableEpoch {
		ViableEpoch::Regular(epoch)
	}
}

impl AsRef<Epoch> for ViableEpoch {
	fn as_ref(&self) -> &Epoch {
		match *self {
			ViableEpoch::Genesis(UnimportedGenesis(ref e)) => e,
			ViableEpoch::Regular(ref e) => e,
		}
	}
}

impl ViableEpoch {
	/// Extract the underlying epoch, disregarding the fact that a genesis
	/// epoch may be unimported.
	pub fn into_inner(self) -> Epoch {
		match self {
			ViableEpoch::Genesis(UnimportedGenesis(e)) => e,
			ViableEpoch::Regular(e) => e,
		}
	}

	/// Increment the epoch, yielding an `IncrementedEpoch` to be imported
	/// into the fork-tree.
	pub fn increment(&self, next_descriptor: NextEpochDescriptor) -> IncrementedEpoch {
		let next = self.as_ref().increment(next_descriptor);
		let to_persist = match *self {
			ViableEpoch::Genesis(UnimportedGenesis(ref epoch_0)) =>
				PersistedEpoch::Genesis(epoch_0.clone(), next),
			ViableEpoch::Regular(_) => PersistedEpoch::Regular(next),
		};

		IncrementedEpoch(to_persist)
	}
}

/// The datatype encoded on disk.
// This really shouldn't be public, but the encode/decode derives force it to be.
#[derive(Clone, Encode, Decode)]
pub enum PersistedEpoch {
	// epoch_0, epoch_1,
	Genesis(Epoch, Epoch),
	// epoch_n
	Regular(Epoch),
}

/// A fresh, incremented epoch to import into the underlying fork-tree.
///
/// Create this with `ViableEpoch::increment`.
#[must_use = "Freshly-incremented epoch must be imported with `EpochChanges::import`"]
pub struct IncrementedEpoch(PersistedEpoch);

impl AsRef<Epoch> for IncrementedEpoch {
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
/// BABE special-cases the first epoch, epoch_0, by saying that it starts at
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
pub struct EpochChanges<Hash, Number> {
	inner: ForkTree<Hash, Number, PersistedEpoch>,
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

	/// Prune out finalized epochs, except for the ancestor of the finalized
	/// block. The given slot should be the slot number at which the finalized
	/// block was authored.
	pub fn prune_finalized<D: IsDescendentOfBuilder<Hash>>(
		&mut self,
		descendent_of_builder: D,
		hash: &Hash,
		number: Number,
		slot: SlotNumber,
	) -> Result<(), fork_tree::Error<D::Error>> {
		let is_descendent_of = descendent_of_builder
			.build_is_descendent_of(None);

		let predicate = |epoch: &PersistedEpoch| match *epoch {
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
		slot_number: SlotNumber,
		make_genesis: G,
	) -> Result<Option<ViableEpoch>, fork_tree::Error<D::Error>>
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
			return Ok(Some(ViableEpoch::Genesis(UnimportedGenesis(genesis_epoch))));
		}

		// We want to find the deepest node in the tree which is an ancestor
		// of our block and where the start slot of the epoch was before the
		// slot of our block. The genesis special-case doesn't need to look
		// at epoch_1 -- all we're doing here is figuring out which node
		// we need.
		let predicate = |epoch: &PersistedEpoch| match *epoch {
			PersistedEpoch::Genesis(ref epoch_0, _) =>
				epoch_0.start_slot <= slot_number,
			PersistedEpoch::Regular(ref epoch_n) =>
				epoch_n.start_slot <= slot_number,
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
					if epoch_1.start_slot <= slot_number {
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
		epoch: IncrementedEpoch,
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

	/// Return the inner fork tree, useful for testing purposes.
	#[cfg(test)]
	pub fn tree(&self) -> &ForkTree<Hash, Number, PersistedEpoch> {
		&self.inner
	}
}

/// Type alias to produce the epoch-changes tree from a block type.
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
			epoch_index: 0,
			start_slot: slot,
			duration: 100,
			authorities: Vec::new(),
			randomness: [0; 32],
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
			100,
			&make_genesis,
		).unwrap().unwrap();

		assert_eq!(genesis_epoch.as_ref(), &make_genesis(100));

		let import_epoch_1 = genesis_epoch.increment(NextEpochDescriptor {
			authorities: Vec::new(),
			randomness: [1; 32],
		});
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
			epoch_index: 0,
			start_slot: slot,
			duration,
			authorities: Vec::new(),
			randomness: [0; 32],
		};

		let mut epoch_changes = EpochChanges::new();
		let next_descriptor = NextEpochDescriptor {
			authorities: Vec::new(),
			randomness: [0; 32],
		};

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
