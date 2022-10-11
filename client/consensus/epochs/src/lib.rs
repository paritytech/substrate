// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Generic utilities for epoch-based consensus engines.

pub mod migration;

use codec::{Decode, Encode};
use fork_tree::{FilterAction, ForkTree};
use sc_client_api::utils::is_descendent_of;
use sp_blockchain::{Error as ClientError, HeaderBackend, HeaderMetadata};
use sp_runtime::traits::{Block as BlockT, NumberFor, One, Zero};
use std::{
	borrow::{Borrow, BorrowMut},
	collections::BTreeMap,
	ops::{Add, Sub},
};

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
	fn build_is_descendent_of(&self, current: Option<(Hash, Hash)>) -> Self::IsDescendentOf;
}

/// Produce a descendent query object given the client.
pub fn descendent_query<H, Block>(client: &H) -> HeaderBackendDescendentBuilder<&H, Block> {
	HeaderBackendDescendentBuilder(client, std::marker::PhantomData)
}

/// Wrapper to get around unconstrained type errors when implementing
/// `IsDescendentOfBuilder` for header backends.
pub struct HeaderBackendDescendentBuilder<H, Block>(H, std::marker::PhantomData<Block>);

impl<'a, H, Block> IsDescendentOfBuilder<Block::Hash>
	for HeaderBackendDescendentBuilder<&'a H, Block>
where
	H: HeaderBackend<Block> + HeaderMetadata<Block, Error = ClientError>,
	Block: BlockT,
{
	type Error = ClientError;
	type IsDescendentOf = Box<dyn Fn(&Block::Hash, &Block::Hash) -> Result<bool, ClientError> + 'a>;

	fn build_is_descendent_of(
		&self,
		current: Option<(Block::Hash, Block::Hash)>,
	) -> Self::IsDescendentOf {
		Box::new(is_descendent_of(self.0, current))
	}
}

/// Epoch data, distinguish whether it is genesis or not.
///
/// Once an epoch is created, it must have a known `start_slot` and `end_slot`, which cannot be
/// changed. Consensus engine may modify any other data in the epoch, if needed.
pub trait Epoch: std::fmt::Debug {
	/// Descriptor for the next epoch.
	type NextEpochDescriptor;
	/// Type of the slot number.
	type Slot: Ord + Copy + std::fmt::Debug;

	/// The starting slot of the epoch.
	fn start_slot(&self) -> Self::Slot;
	/// Produce the "end slot" of the epoch. This is NOT inclusive to the epoch,
	/// i.e. the slots covered by the epoch are `self.start_slot() .. self.end_slot()`.
	fn end_slot(&self) -> Self::Slot;
	/// Increment the epoch data, using the next epoch descriptor.
	fn increment(&self, descriptor: Self::NextEpochDescriptor) -> Self;
}

impl<'a, E: Epoch> From<&'a E> for EpochHeader<E> {
	fn from(epoch: &'a E) -> EpochHeader<E> {
		Self { start_slot: epoch.start_slot(), end_slot: epoch.end_slot() }
	}
}

/// Header of epoch data, consisting of start and end slot.
#[derive(Eq, PartialEq, Encode, Decode, Debug)]
pub struct EpochHeader<E: Epoch> {
	/// The starting slot of the epoch.
	pub start_slot: E::Slot,
	/// The end slot of the epoch. This is NOT inclusive to the epoch,
	/// i.e. the slots covered by the epoch are `self.start_slot() .. self.end_slot()`.
	pub end_slot: E::Slot,
}

impl<E: Epoch> Clone for EpochHeader<E> {
	fn clone(&self) -> Self {
		Self { start_slot: self.start_slot, end_slot: self.end_slot }
	}
}

/// Position of the epoch identifier.
#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug)]
pub enum EpochIdentifierPosition {
	/// The identifier points to a genesis epoch `epoch_0`.
	Genesis0,
	/// The identifier points to a genesis epoch `epoch_1`.
	Genesis1,
	/// The identifier points to a regular epoch.
	Regular,
}

/// Epoch identifier.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct EpochIdentifier<Hash, Number> {
	/// Location of the epoch.
	pub position: EpochIdentifierPosition,
	/// Hash of the block when the epoch is signaled.
	pub hash: Hash,
	/// Number of the block when the epoch is signaled.
	pub number: Number,
}

/// The viable epoch under which a block can be verified.
///
/// If this is the first non-genesis block in the chain, then it will
/// hold an `UnimportedGenesis` epoch.
pub enum ViableEpoch<E, ERef = E> {
	/// Unimported genesis viable epoch data.
	UnimportedGenesis(E),
	/// Regular viable epoch data.
	Signaled(ERef),
}

impl<E, ERef> AsRef<E> for ViableEpoch<E, ERef>
where
	ERef: Borrow<E>,
{
	fn as_ref(&self) -> &E {
		match *self {
			ViableEpoch::UnimportedGenesis(ref e) => e,
			ViableEpoch::Signaled(ref e) => e.borrow(),
		}
	}
}

impl<E, ERef> AsMut<E> for ViableEpoch<E, ERef>
where
	ERef: BorrowMut<E>,
{
	fn as_mut(&mut self) -> &mut E {
		match *self {
			ViableEpoch::UnimportedGenesis(ref mut e) => e,
			ViableEpoch::Signaled(ref mut e) => e.borrow_mut(),
		}
	}
}

impl<E, ERef> ViableEpoch<E, ERef>
where
	E: Epoch + Clone,
	ERef: Borrow<E>,
{
	/// Extract the underlying epoch, disregarding the fact that a genesis
	/// epoch may be unimported.
	pub fn into_cloned_inner(self) -> E {
		match self {
			ViableEpoch::UnimportedGenesis(e) => e,
			ViableEpoch::Signaled(e) => e.borrow().clone(),
		}
	}

	/// Get cloned value for the viable epoch.
	pub fn into_cloned(self) -> ViableEpoch<E, E> {
		match self {
			ViableEpoch::UnimportedGenesis(e) => ViableEpoch::UnimportedGenesis(e),
			ViableEpoch::Signaled(e) => ViableEpoch::Signaled(e.borrow().clone()),
		}
	}

	/// Increment the epoch, yielding an `IncrementedEpoch` to be imported
	/// into the fork-tree.
	pub fn increment(&self, next_descriptor: E::NextEpochDescriptor) -> IncrementedEpoch<E> {
		let next = self.as_ref().increment(next_descriptor);
		let to_persist = match *self {
			ViableEpoch::UnimportedGenesis(ref epoch_0) =>
				PersistedEpoch::Genesis(epoch_0.clone(), next),
			ViableEpoch::Signaled(_) => PersistedEpoch::Regular(next),
		};

		IncrementedEpoch(to_persist)
	}
}

/// Descriptor for a viable epoch.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum ViableEpochDescriptor<Hash, Number, E: Epoch> {
	/// The epoch is an unimported genesis, with given start slot number.
	UnimportedGenesis(E::Slot),
	/// The epoch is signaled and has been imported, with given identifier and header.
	Signaled(EpochIdentifier<Hash, Number>, EpochHeader<E>),
}

impl<Hash, Number, E: Epoch> ViableEpochDescriptor<Hash, Number, E> {
	/// Start slot of the descriptor.
	pub fn start_slot(&self) -> E::Slot {
		match self {
			Self::UnimportedGenesis(start_slot) => *start_slot,
			Self::Signaled(_, header) => header.start_slot,
		}
	}
}

/// Persisted epoch stored in EpochChanges.
#[derive(Clone, Encode, Decode, Debug)]
pub enum PersistedEpoch<E> {
	/// Genesis persisted epoch data. epoch_0, epoch_1.
	Genesis(E, E),
	/// Regular persisted epoch data. epoch_n.
	Regular(E),
}

impl<E> PersistedEpoch<E> {
	/// Returns if this is a genesis epoch.
	pub fn is_genesis(&self) -> bool {
		matches!(self, Self::Genesis(_, _))
	}
}

impl<'a, E: Epoch> From<&'a PersistedEpoch<E>> for PersistedEpochHeader<E> {
	fn from(epoch: &'a PersistedEpoch<E>) -> Self {
		match epoch {
			PersistedEpoch::Genesis(ref epoch_0, ref epoch_1) =>
				PersistedEpochHeader::Genesis(epoch_0.into(), epoch_1.into()),
			PersistedEpoch::Regular(ref epoch_n) => PersistedEpochHeader::Regular(epoch_n.into()),
		}
	}
}

impl<E: Epoch> PersistedEpoch<E> {
	/// Map the epoch to a different type using a conversion function.
	pub fn map<B, F, Hash, Number>(self, h: &Hash, n: &Number, f: &mut F) -> PersistedEpoch<B>
	where
		B: Epoch<Slot = E::Slot>,
		F: FnMut(&Hash, &Number, E) -> B,
	{
		match self {
			PersistedEpoch::Genesis(epoch_0, epoch_1) =>
				PersistedEpoch::Genesis(f(h, n, epoch_0), f(h, n, epoch_1)),
			PersistedEpoch::Regular(epoch_n) => PersistedEpoch::Regular(f(h, n, epoch_n)),
		}
	}
}

/// Persisted epoch header stored in ForkTree.
#[derive(Encode, Decode, PartialEq, Eq, Debug)]
pub enum PersistedEpochHeader<E: Epoch> {
	/// Genesis persisted epoch header. epoch_0, epoch_1.
	Genesis(EpochHeader<E>, EpochHeader<E>),
	/// Regular persisted epoch header. epoch_n.
	Regular(EpochHeader<E>),
}

impl<E: Epoch> Clone for PersistedEpochHeader<E> {
	fn clone(&self) -> Self {
		match self {
			Self::Genesis(epoch_0, epoch_1) => Self::Genesis(epoch_0.clone(), epoch_1.clone()),
			Self::Regular(epoch_n) => Self::Regular(epoch_n.clone()),
		}
	}
}

impl<E: Epoch> PersistedEpochHeader<E> {
	/// Map the epoch header to a different type.
	pub fn map<B>(self) -> PersistedEpochHeader<B>
	where
		B: Epoch<Slot = E::Slot>,
	{
		match self {
			PersistedEpochHeader::Genesis(epoch_0, epoch_1) => PersistedEpochHeader::Genesis(
				EpochHeader { start_slot: epoch_0.start_slot, end_slot: epoch_0.end_slot },
				EpochHeader { start_slot: epoch_1.start_slot, end_slot: epoch_1.end_slot },
			),
			PersistedEpochHeader::Regular(epoch_n) => PersistedEpochHeader::Regular(EpochHeader {
				start_slot: epoch_n.start_slot,
				end_slot: epoch_n.end_slot,
			}),
		}
	}
}

/// A fresh, incremented epoch to import into the underlying fork-tree.
///
/// Create this with `ViableEpoch::increment`.
#[must_use = "Freshly-incremented epoch must be imported with `EpochChanges::import`"]
pub struct IncrementedEpoch<E: Epoch>(PersistedEpoch<E>);

impl<E: Epoch> AsRef<E> for IncrementedEpoch<E> {
	fn as_ref(&self) -> &E {
		match self.0 {
			PersistedEpoch::Genesis(_, ref epoch_1) => epoch_1,
			PersistedEpoch::Regular(ref epoch_n) => epoch_n,
		}
	}
}

/// A pair of epochs for the gap block download validation.
/// Block gap is created after the warp sync is complete. Blocks
/// are imported both at the tip of the chain and at the start of the gap.
/// This holds a pair of epochs that are required to validate headers
/// at the start of the gap. Since gap download does not allow forks we don't
/// need to keep a tree of epochs.
#[derive(Clone, Encode, Decode, Debug)]
pub struct GapEpochs<Hash, Number, E: Epoch> {
	current: (Hash, Number, PersistedEpoch<E>),
	next: Option<(Hash, Number, E)>,
}

impl<Hash, Number, E> GapEpochs<Hash, Number, E>
where
	Hash: Copy + PartialEq + std::fmt::Debug,
	Number: Copy + PartialEq + std::fmt::Debug,
	E: Epoch,
{
	/// Check if given slot matches one of the gap epochs.
	/// Returns epoch identifier if it does.
	fn matches(
		&self,
		slot: E::Slot,
	) -> Option<(Hash, Number, EpochHeader<E>, EpochIdentifierPosition)> {
		match &self.current {
			(_, _, PersistedEpoch::Genesis(epoch_0, _))
				if slot >= epoch_0.start_slot() && slot < epoch_0.end_slot() =>
				return Some((
					self.current.0,
					self.current.1,
					epoch_0.into(),
					EpochIdentifierPosition::Genesis0,
				)),
			(_, _, PersistedEpoch::Genesis(_, epoch_1))
				if slot >= epoch_1.start_slot() && slot < epoch_1.end_slot() =>
				return Some((
					self.current.0,
					self.current.1,
					epoch_1.into(),
					EpochIdentifierPosition::Genesis1,
				)),
			(_, _, PersistedEpoch::Regular(epoch_n))
				if slot >= epoch_n.start_slot() && slot < epoch_n.end_slot() =>
				return Some((
					self.current.0,
					self.current.1,
					epoch_n.into(),
					EpochIdentifierPosition::Regular,
				)),
			_ => {},
		};
		match &self.next {
			Some((h, n, epoch_n)) if slot >= epoch_n.start_slot() && slot < epoch_n.end_slot() =>
				Some((*h, *n, epoch_n.into(), EpochIdentifierPosition::Regular)),
			_ => None,
		}
	}

	/// Returns epoch data if it matches given identifier.
	pub fn epoch(&self, id: &EpochIdentifier<Hash, Number>) -> Option<&E> {
		match (&self.current, &self.next) {
			((h, n, e), _) if h == &id.hash && n == &id.number => match e {
				PersistedEpoch::Genesis(ref epoch_0, _)
					if id.position == EpochIdentifierPosition::Genesis0 =>
					Some(epoch_0),
				PersistedEpoch::Genesis(_, ref epoch_1)
					if id.position == EpochIdentifierPosition::Genesis1 =>
					Some(epoch_1),
				PersistedEpoch::Regular(ref epoch_n)
					if id.position == EpochIdentifierPosition::Regular =>
					Some(epoch_n),
				_ => None,
			},
			(_, Some((h, n, e)))
				if h == &id.hash &&
					n == &id.number && id.position == EpochIdentifierPosition::Regular =>
				Some(e),
			_ => None,
		}
	}

	/// Import a new gap epoch, potentially replacing an old epoch.
	fn import(&mut self, slot: E::Slot, hash: Hash, number: Number, epoch: E) -> Result<(), E> {
		match (&mut self.current, &mut self.next) {
			((_, _, PersistedEpoch::Genesis(_, epoch_1)), _) if slot == epoch_1.end_slot() => {
				self.next = Some((hash, number, epoch));
				Ok(())
			},
			(_, Some((_, _, epoch_n))) if slot == epoch_n.end_slot() => {
				let (cur_h, cur_n, cur_epoch) =
					self.next.take().expect("Already matched as `Some`");
				self.current = (cur_h, cur_n, PersistedEpoch::Regular(cur_epoch));
				self.next = Some((hash, number, epoch));
				Ok(())
			},
			_ => Err(epoch),
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
///
/// Also maintains a pair of epochs for the start of the gap,
/// as long as there's an active gap download after a warp sync.
#[derive(Clone, Encode, Decode, Debug)]
pub struct EpochChanges<Hash, Number, E: Epoch> {
	inner: ForkTree<Hash, Number, PersistedEpochHeader<E>>,
	epochs: BTreeMap<(Hash, Number), PersistedEpoch<E>>,
	gap: Option<GapEpochs<Hash, Number, E>>,
}

// create a fake header hash which hasn't been included in the chain.
fn fake_head_hash<H: AsRef<[u8]> + AsMut<[u8]> + Clone>(parent_hash: &H) -> H {
	let mut h = parent_hash.clone();
	// dirty trick: flip the first bit of the parent hash to create a hash
	// which has not been in the chain before (assuming a strong hash function).
	h.as_mut()[0] ^= 0b10000000;
	h
}

impl<Hash, Number, E: Epoch> Default for EpochChanges<Hash, Number, E>
where
	Hash: PartialEq + Ord,
	Number: Ord,
{
	fn default() -> Self {
		EpochChanges { inner: ForkTree::new(), epochs: BTreeMap::new(), gap: None }
	}
}

impl<Hash, Number, E: Epoch> EpochChanges<Hash, Number, E>
where
	Hash: PartialEq + Ord + AsRef<[u8]> + AsMut<[u8]> + Copy + std::fmt::Debug,
	Number: Ord + One + Zero + Add<Output = Number> + Sub<Output = Number> + Copy + std::fmt::Debug,
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

	/// Clear gap epochs if any.
	pub fn clear_gap(&mut self) {
		self.gap = None;
	}

	/// Map the epoch changes from one storing data to a different one.
	pub fn map<B, F>(self, mut f: F) -> EpochChanges<Hash, Number, B>
	where
		B: Epoch<Slot = E::Slot>,
		F: FnMut(&Hash, &Number, E) -> B,
	{
		EpochChanges {
			inner: self.inner.map(&mut |_, _, header: PersistedEpochHeader<E>| header.map()),
			gap: self.gap.map(|GapEpochs { current: (h, n, header), next }| GapEpochs {
				current: (h, n, header.map(&h, &n, &mut f)),
				next: next.map(|(h, n, e)| (h, n, f(&h, &n, e))),
			}),
			epochs: self
				.epochs
				.into_iter()
				.map(|((hash, number), epoch)| ((hash, number), epoch.map(&hash, &number, &mut f)))
				.collect(),
		}
	}

	/// Prune out finalized epochs, except for the ancestor of the finalized
	/// block. The given slot should be the slot number at which the finalized
	/// block was authored.
	pub fn prune_finalized<D: IsDescendentOfBuilder<Hash>>(
		&mut self,
		descendent_of_builder: D,
		hash: &Hash,
		number: Number,
		slot: E::Slot,
	) -> Result<(), fork_tree::Error<D::Error>> {
		let is_descendent_of = descendent_of_builder.build_is_descendent_of(None);

		let predicate = |epoch: &PersistedEpochHeader<E>| match *epoch {
			PersistedEpochHeader::Genesis(_, ref epoch_1) => slot >= epoch_1.end_slot,
			PersistedEpochHeader::Regular(ref epoch_n) => slot >= epoch_n.end_slot,
		};

		// prune any epochs which could not be _live_ as of the children of the
		// finalized block, i.e. re-root the fork tree to the oldest ancestor of
		// (hash, number) where epoch.end_slot() >= finalized_slot
		let removed = self.inner.prune(hash, &number, &is_descendent_of, &predicate)?;

		for (hash, number, _) in removed {
			self.epochs.remove(&(hash, number));
		}

		Ok(())
	}

	/// Get a reference to an epoch with given identifier.
	pub fn epoch(&self, id: &EpochIdentifier<Hash, Number>) -> Option<&E> {
		if let Some(e) = &self.gap.as_ref().and_then(|gap| gap.epoch(id)) {
			return Some(e)
		}
		self.epochs.get(&(id.hash, id.number)).and_then(|v| match v {
			PersistedEpoch::Genesis(ref epoch_0, _)
				if id.position == EpochIdentifierPosition::Genesis0 =>
				Some(epoch_0),
			PersistedEpoch::Genesis(_, ref epoch_1)
				if id.position == EpochIdentifierPosition::Genesis1 =>
				Some(epoch_1),
			PersistedEpoch::Regular(ref epoch_n)
				if id.position == EpochIdentifierPosition::Regular =>
				Some(epoch_n),
			_ => None,
		})
	}

	/// Get a reference to a viable epoch with given descriptor.
	pub fn viable_epoch<G>(
		&self,
		descriptor: &ViableEpochDescriptor<Hash, Number, E>,
		make_genesis: G,
	) -> Option<ViableEpoch<E, &E>>
	where
		G: FnOnce(E::Slot) -> E,
	{
		match descriptor {
			ViableEpochDescriptor::UnimportedGenesis(slot) =>
				Some(ViableEpoch::UnimportedGenesis(make_genesis(*slot))),
			ViableEpochDescriptor::Signaled(identifier, _) =>
				self.epoch(identifier).map(ViableEpoch::Signaled),
		}
	}

	/// Get a mutable reference to an epoch with given identifier.
	pub fn epoch_mut(&mut self, id: &EpochIdentifier<Hash, Number>) -> Option<&mut E> {
		self.epochs.get_mut(&(id.hash, id.number)).and_then(|v| match v {
			PersistedEpoch::Genesis(ref mut epoch_0, _)
				if id.position == EpochIdentifierPosition::Genesis0 =>
				Some(epoch_0),
			PersistedEpoch::Genesis(_, ref mut epoch_1)
				if id.position == EpochIdentifierPosition::Genesis1 =>
				Some(epoch_1),
			PersistedEpoch::Regular(ref mut epoch_n)
				if id.position == EpochIdentifierPosition::Regular =>
				Some(epoch_n),
			_ => None,
		})
	}

	/// Get a mutable reference to a viable epoch with given descriptor.
	pub fn viable_epoch_mut<G>(
		&mut self,
		descriptor: &ViableEpochDescriptor<Hash, Number, E>,
		make_genesis: G,
	) -> Option<ViableEpoch<E, &mut E>>
	where
		G: FnOnce(E::Slot) -> E,
	{
		match descriptor {
			ViableEpochDescriptor::UnimportedGenesis(slot) =>
				Some(ViableEpoch::UnimportedGenesis(make_genesis(*slot))),
			ViableEpochDescriptor::Signaled(identifier, _) =>
				self.epoch_mut(identifier).map(ViableEpoch::Signaled),
		}
	}

	/// Get the epoch data from an epoch descriptor.
	///
	/// Note that this function ignores the fact that an genesis epoch might need to be imported.
	/// Mostly useful for testing.
	pub fn epoch_data<G>(
		&self,
		descriptor: &ViableEpochDescriptor<Hash, Number, E>,
		make_genesis: G,
	) -> Option<E>
	where
		G: FnOnce(E::Slot) -> E,
		E: Clone,
	{
		match descriptor {
			ViableEpochDescriptor::UnimportedGenesis(slot) => Some(make_genesis(*slot)),
			ViableEpochDescriptor::Signaled(identifier, _) => self.epoch(identifier).cloned(),
		}
	}

	/// Finds the epoch data for a child of the given block. Similar to
	/// `epoch_descriptor_for_child_of` but returns the full data.
	///
	/// Note that this function ignores the fact that an genesis epoch might need to be imported.
	/// Mostly useful for testing.
	pub fn epoch_data_for_child_of<D: IsDescendentOfBuilder<Hash>, G>(
		&self,
		descendent_of_builder: D,
		parent_hash: &Hash,
		parent_number: Number,
		slot: E::Slot,
		make_genesis: G,
	) -> Result<Option<E>, fork_tree::Error<D::Error>>
	where
		G: FnOnce(E::Slot) -> E,
		E: Clone,
	{
		let descriptor = self.epoch_descriptor_for_child_of(
			descendent_of_builder,
			parent_hash,
			parent_number,
			slot,
		)?;

		Ok(descriptor.and_then(|des| self.epoch_data(&des, make_genesis)))
	}

	/// Finds the epoch for a child of the given block, assuming the given slot number.
	///
	/// If the returned epoch is an `UnimportedGenesis` epoch, it should be imported into the
	/// tree.
	pub fn epoch_descriptor_for_child_of<D: IsDescendentOfBuilder<Hash>>(
		&self,
		descendent_of_builder: D,
		parent_hash: &Hash,
		parent_number: Number,
		slot: E::Slot,
	) -> Result<Option<ViableEpochDescriptor<Hash, Number, E>>, fork_tree::Error<D::Error>> {
		if parent_number == Zero::zero() {
			// need to insert the genesis epoch.
			return Ok(Some(ViableEpochDescriptor::UnimportedGenesis(slot)))
		}

		if let Some(gap) = &self.gap {
			if let Some((hash, number, hdr, position)) = gap.matches(slot) {
				return Ok(Some(ViableEpochDescriptor::Signaled(
					EpochIdentifier { position, hash, number },
					hdr,
				)))
			}
		}

		// find_node_where will give you the node in the fork-tree which is an ancestor
		// of the `parent_hash` by default. if the last epoch was signalled at the parent_hash,
		// then it won't be returned. we need to create a new fake chain head hash which
		// "descends" from our parent-hash.
		let fake_head_hash = fake_head_hash(parent_hash);

		let is_descendent_of =
			descendent_of_builder.build_is_descendent_of(Some((fake_head_hash, *parent_hash)));

		// We want to find the deepest node in the tree which is an ancestor
		// of our block and where the start slot of the epoch was before the
		// slot of our block. The genesis special-case doesn't need to look
		// at epoch_1 -- all we're doing here is figuring out which node
		// we need.
		let predicate = |epoch: &PersistedEpochHeader<E>| match *epoch {
			PersistedEpochHeader::Genesis(ref epoch_0, _) => epoch_0.start_slot <= slot,
			PersistedEpochHeader::Regular(ref epoch_n) => epoch_n.start_slot <= slot,
		};

		self.inner
			.find_node_where(
				&fake_head_hash,
				&(parent_number + One::one()),
				&is_descendent_of,
				&predicate,
			)
			.map(|n| {
				n.map(|node| {
					(
						match node.data {
							// Ok, we found our node.
							// and here we figure out which of the internal epochs
							// of a genesis node to use based on their start slot.
							PersistedEpochHeader::Genesis(ref epoch_0, ref epoch_1) => {
								if epoch_1.start_slot <= slot {
									(EpochIdentifierPosition::Genesis1, epoch_1.clone())
								} else {
									(EpochIdentifierPosition::Genesis0, epoch_0.clone())
								}
							},
							PersistedEpochHeader::Regular(ref epoch_n) =>
								(EpochIdentifierPosition::Regular, epoch_n.clone()),
						},
						node,
					)
				})
				.map(|((position, header), node)| {
					ViableEpochDescriptor::Signaled(
						EpochIdentifier { position, hash: node.hash, number: node.number },
						header,
					)
				})
			})
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
		epoch: IncrementedEpoch<E>,
	) -> Result<(), fork_tree::Error<D::Error>> {
		let is_descendent_of =
			descendent_of_builder.build_is_descendent_of(Some((hash, parent_hash)));
		let slot = epoch.as_ref().start_slot();
		let IncrementedEpoch(mut epoch) = epoch;
		let header = PersistedEpochHeader::<E>::from(&epoch);

		if let Some(gap) = &mut self.gap {
			if let PersistedEpoch::Regular(e) = epoch {
				epoch = match gap.import(slot, hash, number, e) {
					Ok(()) => return Ok(()),
					Err(e) => PersistedEpoch::Regular(e),
				}
			}
		} else if epoch.is_genesis() &&
			!self.epochs.is_empty() &&
			!self.epochs.values().any(|e| e.is_genesis())
		{
			// There's a genesis epoch imported when we already have an active epoch.
			// This happens after the warp sync as the ancient blocks download start.
			// We need to start tracking gap epochs here.
			self.gap = Some(GapEpochs { current: (hash, number, epoch), next: None });
			return Ok(())
		}

		let res = self.inner.import(hash, number, header, &is_descendent_of);

		match res {
			Ok(_) | Err(fork_tree::Error::Duplicate) => {
				self.epochs.insert((hash, number), epoch);
				Ok(())
			},
			Err(e) => Err(e),
		}
	}

	/// Reset to a specified pair of epochs, as if they were announced at blocks `parent_hash` and
	/// `hash`.
	pub fn reset(&mut self, parent_hash: Hash, hash: Hash, number: Number, current: E, next: E) {
		self.inner = ForkTree::new();
		self.epochs.clear();
		let persisted = PersistedEpoch::Regular(current);
		let header = PersistedEpochHeader::from(&persisted);
		let _res = self.inner.import(parent_hash, number - One::one(), header, &|_, _| {
			Ok(false) as Result<bool, fork_tree::Error<ClientError>>
		});
		self.epochs.insert((parent_hash, number - One::one()), persisted);

		let persisted = PersistedEpoch::Regular(next);
		let header = PersistedEpochHeader::from(&persisted);
		let _res = self.inner.import(hash, number, header, &|_, _| {
			Ok(true) as Result<bool, fork_tree::Error<ClientError>>
		});
		self.epochs.insert((hash, number), persisted);
	}

	/// Revert to a specified block given its `hash` and `number`.
	/// This removes all the epoch changes information that were announced by
	/// all the given block descendents.
	pub fn revert<D: IsDescendentOfBuilder<Hash>>(
		&mut self,
		descendent_of_builder: D,
		hash: Hash,
		number: Number,
	) {
		let is_descendent_of = descendent_of_builder.build_is_descendent_of(None);

		let filter = |node_hash: &Hash, node_num: &Number, _: &PersistedEpochHeader<E>| {
			if number >= *node_num &&
				(is_descendent_of(node_hash, &hash).unwrap_or_default() || *node_hash == hash)
			{
				// Continue the search in this subtree.
				FilterAction::KeepNode
			} else if number < *node_num && is_descendent_of(&hash, node_hash).unwrap_or_default() {
				// Found a node to be removed.
				FilterAction::Remove
			} else {
				// Not a parent or child of the one we're looking for, stop processing this branch.
				FilterAction::KeepTree
			}
		};

		self.inner.drain_filter(filter).for_each(|(h, n, _)| {
			self.epochs.remove(&(h, n));
		});
	}

	/// Return the inner fork tree (mostly useful for testing)
	pub fn tree(&self) -> &ForkTree<Hash, Number, PersistedEpochHeader<E>> {
		&self.inner
	}
}

/// Type alias to produce the epoch-changes tree from a block type.
pub type EpochChangesFor<Block, Epoch> =
	EpochChanges<<Block as BlockT>::Hash, NumberFor<Block>, Epoch>;

/// A shared epoch changes tree.
pub type SharedEpochChanges<Block, Epoch> =
	sc_consensus::shared_data::SharedData<EpochChangesFor<Block, Epoch>>;

#[cfg(test)]
mod tests {
	use super::{Epoch as EpochT, *};

	#[derive(Debug, PartialEq)]
	pub struct TestError;

	impl std::fmt::Display for TestError {
		fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
			write!(f, "TestError")
		}
	}

	impl std::error::Error for TestError {}

	impl<'a, F: 'a, H: 'a + PartialEq + std::fmt::Debug> IsDescendentOfBuilder<H> for &'a F
	where
		F: Fn(&H, &H) -> Result<bool, TestError>,
	{
		type Error = TestError;
		type IsDescendentOf = Box<dyn Fn(&H, &H) -> Result<bool, TestError> + 'a>;

		fn build_is_descendent_of(&self, current: Option<(H, H)>) -> Self::IsDescendentOf {
			let f = *self;
			Box::new(move |base, head| {
				let mut head = head;

				if let Some((ref c_head, ref c_parent)) = current {
					if head == c_head {
						if base == c_parent {
							return Ok(true)
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
	type Slot = u64;

	#[derive(Debug, Clone, Eq, PartialEq)]
	struct Epoch {
		start_slot: Slot,
		duration: Slot,
	}

	impl EpochT for Epoch {
		type NextEpochDescriptor = ();
		type Slot = Slot;

		fn increment(&self, _: ()) -> Self {
			Epoch { start_slot: self.start_slot + self.duration, duration: self.duration }
		}

		fn end_slot(&self) -> Slot {
			self.start_slot + self.duration
		}

		fn start_slot(&self) -> Slot {
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

		let epoch_changes = EpochChanges::<_, _, Epoch>::new();
		let genesis_epoch = epoch_changes
			.epoch_descriptor_for_child_of(&is_descendent_of, b"0", 0, 10101)
			.unwrap()
			.unwrap();

		match genesis_epoch {
			ViableEpochDescriptor::UnimportedGenesis(slot) => {
				assert_eq!(slot, 10101u64);
			},
			_ => panic!("should be unimported genesis"),
		};

		let genesis_epoch_2 = epoch_changes
			.epoch_descriptor_for_child_of(&is_descendent_of, b"0", 0, 10102)
			.unwrap()
			.unwrap();

		match genesis_epoch_2 {
			ViableEpochDescriptor::UnimportedGenesis(slot) => {
				assert_eq!(slot, 10102u64);
			},
			_ => panic!("should be unimported genesis"),
		};
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

		let make_genesis = |slot| Epoch { start_slot: slot, duration: 100 };

		let mut epoch_changes = EpochChanges::<_, _, Epoch>::new();
		let genesis_epoch = epoch_changes
			.epoch_descriptor_for_child_of(&is_descendent_of, b"0", 0, 100)
			.unwrap()
			.unwrap();

		assert_eq!(genesis_epoch, ViableEpochDescriptor::UnimportedGenesis(100));

		let import_epoch_1 =
			epoch_changes.viable_epoch(&genesis_epoch, &make_genesis).unwrap().increment(());
		let epoch_1 = import_epoch_1.as_ref().clone();

		epoch_changes
			.import(&is_descendent_of, *b"A", 1, *b"0", import_epoch_1)
			.unwrap();
		let genesis_epoch = epoch_changes.epoch_data(&genesis_epoch, &make_genesis).unwrap();

		assert!(is_descendent_of(b"0", b"A").unwrap());

		let end_slot = genesis_epoch.end_slot();
		assert_eq!(end_slot, epoch_1.start_slot);

		{
			// x is still within the genesis epoch.
			let x = epoch_changes
				.epoch_data_for_child_of(&is_descendent_of, b"A", 1, end_slot - 1, &make_genesis)
				.unwrap()
				.unwrap();

			assert_eq!(x, genesis_epoch);
		}

		{
			// x is now at the next epoch, because the block is now at the
			// start slot of epoch 1.
			let x = epoch_changes
				.epoch_data_for_child_of(&is_descendent_of, b"A", 1, end_slot, &make_genesis)
				.unwrap()
				.unwrap();

			assert_eq!(x, epoch_1);
		}

		{
			// x is now at the next epoch, because the block is now after
			// start slot of epoch 1.
			let x = epoch_changes
				.epoch_data_for_child_of(
					&is_descendent_of,
					b"A",
					1,
					epoch_1.end_slot() - 1,
					&make_genesis,
				)
				.unwrap()
				.unwrap();

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

		let make_genesis = |slot| Epoch { start_slot: slot, duration };

		let mut epoch_changes = EpochChanges::new();
		let next_descriptor = ();

		// insert genesis epoch for A
		{
			let genesis_epoch_a_descriptor = epoch_changes
				.epoch_descriptor_for_child_of(&is_descendent_of, b"0", 0, 100)
				.unwrap()
				.unwrap();

			let incremented_epoch = epoch_changes
				.viable_epoch(&genesis_epoch_a_descriptor, &make_genesis)
				.unwrap()
				.increment(next_descriptor);

			epoch_changes
				.import(&is_descendent_of, *b"A", 1, *b"0", incremented_epoch)
				.unwrap();
		}

		// insert genesis epoch for X
		{
			let genesis_epoch_x_descriptor = epoch_changes
				.epoch_descriptor_for_child_of(&is_descendent_of, b"0", 0, 1000)
				.unwrap()
				.unwrap();

			let incremented_epoch = epoch_changes
				.viable_epoch(&genesis_epoch_x_descriptor, &make_genesis)
				.unwrap()
				.increment(next_descriptor);

			epoch_changes
				.import(&is_descendent_of, *b"X", 1, *b"0", incremented_epoch)
				.unwrap();
		}

		// now check that the genesis epochs for our respective block 1s
		// respect the chain structure.
		{
			let epoch_for_a_child = epoch_changes
				.epoch_data_for_child_of(&is_descendent_of, b"A", 1, 101, &make_genesis)
				.unwrap()
				.unwrap();

			assert_eq!(epoch_for_a_child, make_genesis(100));

			let epoch_for_x_child = epoch_changes
				.epoch_data_for_child_of(&is_descendent_of, b"X", 1, 1001, &make_genesis)
				.unwrap()
				.unwrap();

			assert_eq!(epoch_for_x_child, make_genesis(1000));

			let epoch_for_x_child_before_genesis = epoch_changes
				.epoch_data_for_child_of(&is_descendent_of, b"X", 1, 101, &make_genesis)
				.unwrap();

			// even though there is a genesis epoch at that slot, it's not in
			// this chain.
			assert!(epoch_for_x_child_before_genesis.is_none());
		}
	}

	/// Test that ensures that the gap is not enabled when we import multiple genesis blocks.
	#[test]
	fn gap_is_not_enabled_when_multiple_genesis_epochs_are_imported() {
		//     X
		//   /
		// 0 - A
		//
		let is_descendent_of = |base: &Hash, block: &Hash| -> Result<bool, TestError> {
			match (base, *block) {
				(b"0", _) => Ok(true),
				_ => Ok(false),
			}
		};

		let duration = 100;

		let make_genesis = |slot| Epoch { start_slot: slot, duration };

		let mut epoch_changes = EpochChanges::new();
		let next_descriptor = ();

		// insert genesis epoch for A
		{
			let genesis_epoch_a_descriptor = epoch_changes
				.epoch_descriptor_for_child_of(&is_descendent_of, b"0", 0, 100)
				.unwrap()
				.unwrap();

			let incremented_epoch = epoch_changes
				.viable_epoch(&genesis_epoch_a_descriptor, &make_genesis)
				.unwrap()
				.increment(next_descriptor);

			epoch_changes
				.import(&is_descendent_of, *b"A", 1, *b"0", incremented_epoch)
				.unwrap();
		}

		// insert genesis epoch for X
		{
			let genesis_epoch_x_descriptor = epoch_changes
				.epoch_descriptor_for_child_of(&is_descendent_of, b"0", 0, 1000)
				.unwrap()
				.unwrap();

			let incremented_epoch = epoch_changes
				.viable_epoch(&genesis_epoch_x_descriptor, &make_genesis)
				.unwrap()
				.increment(next_descriptor);

			epoch_changes
				.import(&is_descendent_of, *b"X", 1, *b"0", incremented_epoch)
				.unwrap();
		}

		// Clearing the gap should be a no-op.
		epoch_changes.clear_gap();

		// Check that both epochs are available.
		let epoch_a = epoch_changes
			.epoch_data_for_child_of(&is_descendent_of, b"A", 1, 101, &make_genesis)
			.unwrap()
			.unwrap();

		let epoch_x = epoch_changes
			.epoch_data_for_child_of(&is_descendent_of, b"X", 1, 1001, &make_genesis)
			.unwrap()
			.unwrap();

		assert!(epoch_a != epoch_x)
	}

	#[test]
	fn gap_epochs_advance() {
		// 0 - 1 - 2 - 3 - .... 42 - 43
		let is_descendent_of = |base: &Hash, block: &Hash| -> Result<bool, TestError> {
			match (base, *block) {
				(b"0", _) => Ok(true),
				(b"1", b) => Ok(b == *b"0"),
				(b"2", b) => Ok(b == *b"1"),
				(b"3", b) => Ok(b == *b"2"),
				_ => Ok(false),
			}
		};

		let duration = 100;

		let make_genesis = |slot| Epoch { start_slot: slot, duration };

		let mut epoch_changes = EpochChanges::new();
		let next_descriptor = ();

		let epoch42 = Epoch { start_slot: 42, duration: 100 };
		let epoch43 = Epoch { start_slot: 43, duration: 100 };
		epoch_changes.reset(*b"0", *b"1", 4200, epoch42, epoch43);
		assert!(epoch_changes.gap.is_none());

		// Import a new genesis epoch, this should crate the gap.
		let genesis_epoch_a_descriptor = epoch_changes
			.epoch_descriptor_for_child_of(&is_descendent_of, b"0", 0, 100)
			.unwrap()
			.unwrap();

		let incremented_epoch = epoch_changes
			.viable_epoch(&genesis_epoch_a_descriptor, &make_genesis)
			.unwrap()
			.increment(next_descriptor);

		epoch_changes
			.import(&is_descendent_of, *b"1", 1, *b"0", incremented_epoch)
			.unwrap();
		assert!(epoch_changes.gap.is_some());

		let genesis_epoch = epoch_changes
			.epoch_descriptor_for_child_of(&is_descendent_of, b"0", 0, 100)
			.unwrap()
			.unwrap();

		assert_eq!(genesis_epoch, ViableEpochDescriptor::UnimportedGenesis(100));

		// Import more epochs and check that gap advances.
		let import_epoch_1 =
			epoch_changes.viable_epoch(&genesis_epoch, &make_genesis).unwrap().increment(());

		let epoch_1 = import_epoch_1.as_ref().clone();
		epoch_changes
			.import(&is_descendent_of, *b"1", 1, *b"0", import_epoch_1)
			.unwrap();
		let genesis_epoch_data = epoch_changes.epoch_data(&genesis_epoch, &make_genesis).unwrap();
		let end_slot = genesis_epoch_data.end_slot();
		let x = epoch_changes
			.epoch_data_for_child_of(&is_descendent_of, b"1", 1, end_slot, &make_genesis)
			.unwrap()
			.unwrap();

		assert_eq!(x, epoch_1);
		assert_eq!(epoch_changes.gap.as_ref().unwrap().current.0, *b"1");
		assert!(epoch_changes.gap.as_ref().unwrap().next.is_none());

		let epoch_1_desriptor = epoch_changes
			.epoch_descriptor_for_child_of(&is_descendent_of, b"1", 1, end_slot)
			.unwrap()
			.unwrap();
		let epoch_1 = epoch_changes.epoch_data(&epoch_1_desriptor, &make_genesis).unwrap();
		let import_epoch_2 = epoch_changes
			.viable_epoch(&epoch_1_desriptor, &make_genesis)
			.unwrap()
			.increment(());
		let epoch_2 = import_epoch_2.as_ref().clone();
		epoch_changes
			.import(&is_descendent_of, *b"2", 2, *b"1", import_epoch_2)
			.unwrap();

		let end_slot = epoch_1.end_slot();
		let x = epoch_changes
			.epoch_data_for_child_of(&is_descendent_of, b"2", 2, end_slot, &make_genesis)
			.unwrap()
			.unwrap();
		assert_eq!(epoch_changes.gap.as_ref().unwrap().current.0, *b"1");
		assert_eq!(epoch_changes.gap.as_ref().unwrap().next.as_ref().unwrap().0, *b"2");
		assert_eq!(x, epoch_2);

		let epoch_2_desriptor = epoch_changes
			.epoch_descriptor_for_child_of(&is_descendent_of, b"2", 2, end_slot)
			.unwrap()
			.unwrap();
		let import_epoch_3 = epoch_changes
			.viable_epoch(&epoch_2_desriptor, &make_genesis)
			.unwrap()
			.increment(());
		epoch_changes
			.import(&is_descendent_of, *b"3", 3, *b"2", import_epoch_3)
			.unwrap();

		assert_eq!(epoch_changes.gap.as_ref().unwrap().current.0, *b"2");

		epoch_changes.clear_gap();
		assert!(epoch_changes.gap.is_none());
	}

	/// Test that ensures that the gap is not enabled when there's still genesis
	/// epochs imported, regardless of whether there are already other further
	/// epochs imported descending from such genesis epochs.
	#[test]
	fn gap_is_not_enabled_when_at_least_one_genesis_epoch_is_still_imported() {
		//     A (#1) - B (#201)
		//   /
		// 0 - C (#1)
		//
		// The epoch duration is 100 slots, each of these blocks represents
		// an epoch change block. block B starts a new epoch at #201 since the
		// genesis epoch spans two epochs.

		let is_descendent_of = |base: &Hash, block: &Hash| -> Result<bool, TestError> {
			match (base, block) {
				(b"0", _) => Ok(true),
				(b"A", b"B") => Ok(true),
				_ => Ok(false),
			}
		};

		let duration = 100;
		let make_genesis = |slot| Epoch { start_slot: slot, duration };
		let mut epoch_changes = EpochChanges::new();
		let next_descriptor = ();

		// insert genesis epoch for A at slot 1
		{
			let genesis_epoch_a_descriptor = epoch_changes
				.epoch_descriptor_for_child_of(&is_descendent_of, b"0", 0, 1)
				.unwrap()
				.unwrap();

			let incremented_epoch = epoch_changes
				.viable_epoch(&genesis_epoch_a_descriptor, &make_genesis)
				.unwrap()
				.increment(next_descriptor);

			epoch_changes
				.import(&is_descendent_of, *b"A", 1, *b"0", incremented_epoch)
				.unwrap();
		}

		// insert regular epoch for B at slot 201, descending from A
		{
			let epoch_b_descriptor = epoch_changes
				.epoch_descriptor_for_child_of(&is_descendent_of, b"A", 1, 201)
				.unwrap()
				.unwrap();

			let incremented_epoch = epoch_changes
				.viable_epoch(&epoch_b_descriptor, &make_genesis)
				.unwrap()
				.increment(next_descriptor);

			epoch_changes
				.import(&is_descendent_of, *b"B", 201, *b"A", incremented_epoch)
				.unwrap();
		}

		// insert genesis epoch for C at slot 1000
		{
			let genesis_epoch_x_descriptor = epoch_changes
				.epoch_descriptor_for_child_of(&is_descendent_of, b"0", 0, 1000)
				.unwrap()
				.unwrap();

			let incremented_epoch = epoch_changes
				.viable_epoch(&genesis_epoch_x_descriptor, &make_genesis)
				.unwrap()
				.increment(next_descriptor);

			epoch_changes
				.import(&is_descendent_of, *b"C", 1, *b"0", incremented_epoch)
				.unwrap();
		}

		// Clearing the gap should be a no-op.
		epoch_changes.clear_gap();

		// Check that all three epochs are available.
		let epoch_a = epoch_changes
			.epoch_data_for_child_of(&is_descendent_of, b"A", 1, 10, &make_genesis)
			.unwrap()
			.unwrap();

		let epoch_b = epoch_changes
			.epoch_data_for_child_of(&is_descendent_of, b"B", 201, 201, &make_genesis)
			.unwrap()
			.unwrap();

		assert!(epoch_a != epoch_b);

		// the genesis epoch A will span slots [1, 200] with epoch B starting at slot 201
		assert_eq!(epoch_b.start_slot(), 201);

		let epoch_c = epoch_changes
			.epoch_data_for_child_of(&is_descendent_of, b"C", 1, 1001, &make_genesis)
			.unwrap()
			.unwrap();

		assert!(epoch_a != epoch_c);
	}
}
