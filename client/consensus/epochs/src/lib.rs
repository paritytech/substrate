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

//! Generic utilities for session-based consensus engines.

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

/// Session data, distinguish whether it is genesis or not.
///
/// Once an session is created, it must have a known `start_slot` and `end_slot`, which cannot be
/// changed. Consensus engine may modify any other data in the session, if needed.
pub trait Session: std::fmt::Debug {
	/// Descriptor for the next session.
	type NextSessionDescriptor;
	/// Type of the slot number.
	type Slot: Ord + Copy + std::fmt::Debug;

	/// The starting slot of the session.
	fn start_slot(&self) -> Self::Slot;
	/// Produce the "end slot" of the session. This is NOT inclusive to the session,
	/// i.e. the slots covered by the session are `self.start_slot() .. self.end_slot()`.
	fn end_slot(&self) -> Self::Slot;
	/// Increment the session data, using the next session descriptor.
	fn increment(&self, descriptor: Self::NextSessionDescriptor) -> Self;
}

impl<'a, E: Session> From<&'a E> for SessionHeader<E> {
	fn from(session: &'a E) -> SessionHeader<E> {
		Self { start_slot: session.start_slot(), end_slot: session.end_slot() }
	}
}

/// Header of session data, consisting of start and end slot.
#[derive(Eq, PartialEq, Encode, Decode, Debug)]
pub struct SessionHeader<E: Session> {
	/// The starting slot of the session.
	pub start_slot: E::Slot,
	/// The end slot of the session. This is NOT inclusive to the session,
	/// i.e. the slots covered by the session are `self.start_slot() .. self.end_slot()`.
	pub end_slot: E::Slot,
}

impl<E: Session> Clone for SessionHeader<E> {
	fn clone(&self) -> Self {
		Self { start_slot: self.start_slot, end_slot: self.end_slot }
	}
}

/// Position of the session identifier.
#[derive(PartialEq, Eq, PartialOrd, Ord, Copy, Clone, Debug)]
pub enum SessionIdentifierPosition {
	/// The identifier points to a genesis session `session_0`.
	Genesis0,
	/// The identifier points to a genesis session `session_1`.
	Genesis1,
	/// The identifier points to a regular session.
	Regular,
}

/// Session identifier.
#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub struct SessionIdentifier<Hash, Number> {
	/// Location of the session.
	pub position: SessionIdentifierPosition,
	/// Hash of the block when the session is signaled.
	pub hash: Hash,
	/// Number of the block when the session is signaled.
	pub number: Number,
}

/// The viable session under which a block can be verified.
///
/// If this is the first non-genesis block in the chain, then it will
/// hold an `UnimportedGenesis` session.
pub enum ViableSession<E, ERef = E> {
	/// Unimported genesis viable session data.
	UnimportedGenesis(E),
	/// Regular viable session data.
	Signaled(ERef),
}

impl<E, ERef> AsRef<E> for ViableSession<E, ERef>
where
	ERef: Borrow<E>,
{
	fn as_ref(&self) -> &E {
		match *self {
			ViableSession::UnimportedGenesis(ref e) => e,
			ViableSession::Signaled(ref e) => e.borrow(),
		}
	}
}

impl<E, ERef> AsMut<E> for ViableSession<E, ERef>
where
	ERef: BorrowMut<E>,
{
	fn as_mut(&mut self) -> &mut E {
		match *self {
			ViableSession::UnimportedGenesis(ref mut e) => e,
			ViableSession::Signaled(ref mut e) => e.borrow_mut(),
		}
	}
}

impl<E, ERef> ViableSession<E, ERef>
where
	E: Session + Clone,
	ERef: Borrow<E>,
{
	/// Extract the underlying session, disregarding the fact that a genesis
	/// session may be unimported.
	pub fn into_cloned_inner(self) -> E {
		match self {
			ViableSession::UnimportedGenesis(e) => e,
			ViableSession::Signaled(e) => e.borrow().clone(),
		}
	}

	/// Get cloned value for the viable session.
	pub fn into_cloned(self) -> ViableSession<E, E> {
		match self {
			ViableSession::UnimportedGenesis(e) => ViableSession::UnimportedGenesis(e),
			ViableSession::Signaled(e) => ViableSession::Signaled(e.borrow().clone()),
		}
	}

	/// Increment the session, yielding an `IncrementedSession` to be imported
	/// into the fork-tree.
	pub fn increment(&self, next_descriptor: E::NextSessionDescriptor) -> IncrementedSession<E> {
		let next = self.as_ref().increment(next_descriptor);
		let to_persist = match *self {
			ViableSession::UnimportedGenesis(ref session_0) =>
				PersistedSession::Genesis(session_0.clone(), next),
			ViableSession::Signaled(_) => PersistedSession::Regular(next),
		};

		IncrementedSession(to_persist)
	}
}

/// Descriptor for a viable session.
#[derive(PartialEq, Eq, Clone, Debug)]
pub enum ViableSessionDescriptor<Hash, Number, E: Session> {
	/// The session is an unimported genesis, with given start slot number.
	UnimportedGenesis(E::Slot),
	/// The session is signaled and has been imported, with given identifier and header.
	Signaled(SessionIdentifier<Hash, Number>, SessionHeader<E>),
}

impl<Hash, Number, E: Session> ViableSessionDescriptor<Hash, Number, E> {
	/// Start slot of the descriptor.
	pub fn start_slot(&self) -> E::Slot {
		match self {
			Self::UnimportedGenesis(start_slot) => *start_slot,
			Self::Signaled(_, header) => header.start_slot,
		}
	}
}

/// Persisted session stored in SessionChanges.
#[derive(Clone, Encode, Decode, Debug)]
pub enum PersistedSession<E> {
	/// Genesis persisted session data. session_0, session_1.
	Genesis(E, E),
	/// Regular persisted session data. session_n.
	Regular(E),
}

impl<E> PersistedSession<E> {
	/// Returns if this is a genesis session.
	pub fn is_genesis(&self) -> bool {
		matches!(self, Self::Genesis(_, _))
	}
}

impl<'a, E: Session> From<&'a PersistedSession<E>> for PersistedSessionHeader<E> {
	fn from(session: &'a PersistedSession<E>) -> Self {
		match session {
			PersistedSession::Genesis(ref session_0, ref session_1) =>
				PersistedSessionHeader::Genesis(session_0.into(), session_1.into()),
			PersistedSession::Regular(ref session_n) => PersistedSessionHeader::Regular(session_n.into()),
		}
	}
}

impl<E: Session> PersistedSession<E> {
	/// Map the session to a different type using a conversion function.
	pub fn map<B, F, Hash, Number>(self, h: &Hash, n: &Number, f: &mut F) -> PersistedSession<B>
	where
		B: Session<Slot = E::Slot>,
		F: FnMut(&Hash, &Number, E) -> B,
	{
		match self {
			PersistedSession::Genesis(session_0, session_1) =>
				PersistedSession::Genesis(f(h, n, session_0), f(h, n, session_1)),
			PersistedSession::Regular(session_n) => PersistedSession::Regular(f(h, n, session_n)),
		}
	}
}

/// Persisted session header stored in ForkTree.
#[derive(Encode, Decode, PartialEq, Eq, Debug)]
pub enum PersistedSessionHeader<E: Session> {
	/// Genesis persisted session header. session_0, session_1.
	Genesis(SessionHeader<E>, SessionHeader<E>),
	/// Regular persisted session header. session_n.
	Regular(SessionHeader<E>),
}

impl<E: Session> Clone for PersistedSessionHeader<E> {
	fn clone(&self) -> Self {
		match self {
			Self::Genesis(session_0, session_1) => Self::Genesis(session_0.clone(), session_1.clone()),
			Self::Regular(session_n) => Self::Regular(session_n.clone()),
		}
	}
}

impl<E: Session> PersistedSessionHeader<E> {
	/// Map the session header to a different type.
	pub fn map<B>(self) -> PersistedSessionHeader<B>
	where
		B: Session<Slot = E::Slot>,
	{
		match self {
			PersistedSessionHeader::Genesis(session_0, session_1) => PersistedSessionHeader::Genesis(
				SessionHeader { start_slot: session_0.start_slot, end_slot: session_0.end_slot },
				SessionHeader { start_slot: session_1.start_slot, end_slot: session_1.end_slot },
			),
			PersistedSessionHeader::Regular(session_n) => PersistedSessionHeader::Regular(SessionHeader {
				start_slot: session_n.start_slot,
				end_slot: session_n.end_slot,
			}),
		}
	}
}

/// A fresh, incremented session to import into the underlying fork-tree.
///
/// Create this with `ViableSession::increment`.
#[must_use = "Freshly-incremented session must be imported with `SessionChanges::import`"]
pub struct IncrementedSession<E: Session>(PersistedSession<E>);

impl<E: Session> AsRef<E> for IncrementedSession<E> {
	fn as_ref(&self) -> &E {
		match self.0 {
			PersistedSession::Genesis(_, ref session_1) => session_1,
			PersistedSession::Regular(ref session_n) => session_n,
		}
	}
}

/// A pair of sessions for the gap block download validation.
/// Block gap is created after the warp sync is complete. Blocks
/// are imported both at the tip of the chain and at the start of the gap.
/// This holds a pair of sessions that are required to validate headers
/// at the start of the gap. Since gap download does not allow forks we don't
/// need to keep a tree of sessions.
#[derive(Clone, Encode, Decode, Debug)]
pub struct GapSessions<Hash, Number, E: Session> {
	current: (Hash, Number, PersistedSession<E>),
	next: Option<(Hash, Number, E)>,
}

impl<Hash, Number, E> GapSessions<Hash, Number, E>
where
	Hash: Copy + PartialEq + std::fmt::Debug,
	Number: Copy + PartialEq + std::fmt::Debug,
	E: Session,
{
	/// Check if given slot matches one of the gap sessions.
	/// Returns session identifier if it does.
	fn matches(
		&self,
		slot: E::Slot,
	) -> Option<(Hash, Number, SessionHeader<E>, SessionIdentifierPosition)> {
		match &self.current {
			(_, _, PersistedSession::Genesis(session_0, _))
				if slot >= session_0.start_slot() && slot < session_0.end_slot() =>
				return Some((
					self.current.0,
					self.current.1,
					session_0.into(),
					SessionIdentifierPosition::Genesis0,
				)),
			(_, _, PersistedSession::Genesis(_, session_1))
				if slot >= session_1.start_slot() && slot < session_1.end_slot() =>
				return Some((
					self.current.0,
					self.current.1,
					session_1.into(),
					SessionIdentifierPosition::Genesis1,
				)),
			(_, _, PersistedSession::Regular(session_n))
				if slot >= session_n.start_slot() && slot < session_n.end_slot() =>
				return Some((
					self.current.0,
					self.current.1,
					session_n.into(),
					SessionIdentifierPosition::Regular,
				)),
			_ => {},
		};
		match &self.next {
			Some((h, n, session_n)) if slot >= session_n.start_slot() && slot < session_n.end_slot() =>
				Some((*h, *n, session_n.into(), SessionIdentifierPosition::Regular)),
			_ => None,
		}
	}

	/// Returns session data if it matches given identifier.
	pub fn session(&self, id: &SessionIdentifier<Hash, Number>) -> Option<&E> {
		match (&self.current, &self.next) {
			((h, n, e), _) if h == &id.hash && n == &id.number => match e {
				PersistedSession::Genesis(ref session_0, _)
					if id.position == SessionIdentifierPosition::Genesis0 =>
					Some(session_0),
				PersistedSession::Genesis(_, ref session_1)
					if id.position == SessionIdentifierPosition::Genesis1 =>
					Some(session_1),
				PersistedSession::Regular(ref session_n)
					if id.position == SessionIdentifierPosition::Regular =>
					Some(session_n),
				_ => None,
			},
			(_, Some((h, n, e)))
				if h == &id.hash &&
					n == &id.number && id.position == SessionIdentifierPosition::Regular =>
				Some(e),
			_ => None,
		}
	}

	/// Import a new gap session, potentially replacing an old session.
	fn import(&mut self, slot: E::Slot, hash: Hash, number: Number, session: E) -> Result<(), E> {
		match (&mut self.current, &mut self.next) {
			((_, _, PersistedSession::Genesis(_, session_1)), _) if slot == session_1.end_slot() => {
				self.next = Some((hash, number, session));
				Ok(())
			},
			(_, Some((_, _, session_n))) if slot == session_n.end_slot() => {
				let (cur_h, cur_n, cur_session) =
					self.next.take().expect("Already matched as `Some`");
				self.current = (cur_h, cur_n, PersistedSession::Regular(cur_session));
				self.next = Some((hash, number, session));
				Ok(())
			},
			_ => Err(session),
		}
	}
}

/// Tree of all session changes across all *seen* forks. Data stored in tree is
/// the hash and block number of the block signaling the session change, and the
/// session that was signalled at that block.
///
/// The first session, session_0, is special cased by saying that it starts at
/// slot number of the first block in the chain. When bootstrapping a chain,
/// there can be multiple competing block #1s, so we have to ensure that the overlayed
/// DAG doesn't get confused.
///
/// The first block of every session should be producing a descriptor for the next
/// session - this is checked in higher-level code. So the first block of session_0 contains
/// a descriptor for session_1. We special-case these and bundle them together in the
/// same DAG entry, pinned to a specific block #1.
///
/// Further sessions (session_2, ..., session_n) each get their own entry.
///
/// Also maintains a pair of sessions for the start of the gap,
/// as long as there's an active gap download after a warp sync.
#[derive(Clone, Encode, Decode, Debug)]
pub struct SessionChanges<Hash, Number, E: Session> {
	inner: ForkTree<Hash, Number, PersistedSessionHeader<E>>,
	sessions: BTreeMap<(Hash, Number), PersistedSession<E>>,
	gap: Option<GapSessions<Hash, Number, E>>,
}

// create a fake header hash which hasn't been included in the chain.
fn fake_head_hash<H: AsRef<[u8]> + AsMut<[u8]> + Clone>(parent_hash: &H) -> H {
	let mut h = parent_hash.clone();
	// dirty trick: flip the first bit of the parent hash to create a hash
	// which has not been in the chain before (assuming a strong hash function).
	h.as_mut()[0] ^= 0b10000000;
	h
}

impl<Hash, Number, E: Session> Default for SessionChanges<Hash, Number, E>
where
	Hash: PartialEq + Ord,
	Number: Ord,
{
	fn default() -> Self {
		SessionChanges { inner: ForkTree::new(), sessions: BTreeMap::new(), gap: None }
	}
}

impl<Hash, Number, E: Session> SessionChanges<Hash, Number, E>
where
	Hash: PartialEq + Ord + AsRef<[u8]> + AsMut<[u8]> + Copy + std::fmt::Debug,
	Number: Ord + One + Zero + Add<Output = Number> + Sub<Output = Number> + Copy + std::fmt::Debug,
{
	/// Create a new session change.
	pub fn new() -> Self {
		Self::default()
	}

	/// Rebalances the tree of session changes so that it is sorted by length of
	/// fork (longest fork first).
	pub fn rebalance(&mut self) {
		self.inner.rebalance()
	}

	/// Clear gap sessions if any.
	pub fn clear_gap(&mut self) {
		self.gap = None;
	}

	/// Map the session changes from one storing data to a different one.
	pub fn map<B, F>(self, mut f: F) -> SessionChanges<Hash, Number, B>
	where
		B: Session<Slot = E::Slot>,
		F: FnMut(&Hash, &Number, E) -> B,
	{
		SessionChanges {
			inner: self.inner.map(&mut |_, _, header: PersistedSessionHeader<E>| header.map()),
			gap: self.gap.map(|GapSessions { current: (h, n, header), next }| GapSessions {
				current: (h, n, header.map(&h, &n, &mut f)),
				next: next.map(|(h, n, e)| (h, n, f(&h, &n, e))),
			}),
			sessions: self
				.sessions
				.into_iter()
				.map(|((hash, number), session)| ((hash, number), session.map(&hash, &number, &mut f)))
				.collect(),
		}
	}

	/// Prune out finalized sessions, except for the ancestor of the finalized
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

		let predicate = |session: &PersistedSessionHeader<E>| match *session {
			PersistedSessionHeader::Genesis(_, ref session_1) => slot >= session_1.end_slot,
			PersistedSessionHeader::Regular(ref session_n) => slot >= session_n.end_slot,
		};

		// prune any sessions which could not be _live_ as of the children of the
		// finalized block, i.e. re-root the fork tree to the oldest ancestor of
		// (hash, number) where session.end_slot() >= finalized_slot
		let removed = self.inner.prune(hash, &number, &is_descendent_of, &predicate)?;

		for (hash, number, _) in removed {
			self.sessions.remove(&(hash, number));
		}

		Ok(())
	}

	/// Get a reference to an session with given identifier.
	pub fn session(&self, id: &SessionIdentifier<Hash, Number>) -> Option<&E> {
		if let Some(e) = &self.gap.as_ref().and_then(|gap| gap.session(id)) {
			return Some(e)
		}
		self.sessions.get(&(id.hash, id.number)).and_then(|v| match v {
			PersistedSession::Genesis(ref session_0, _)
				if id.position == SessionIdentifierPosition::Genesis0 =>
				Some(session_0),
			PersistedSession::Genesis(_, ref session_1)
				if id.position == SessionIdentifierPosition::Genesis1 =>
				Some(session_1),
			PersistedSession::Regular(ref session_n)
				if id.position == SessionIdentifierPosition::Regular =>
				Some(session_n),
			_ => None,
		})
	}

	/// Get a reference to a viable session with given descriptor.
	pub fn viable_session<G>(
		&self,
		descriptor: &ViableSessionDescriptor<Hash, Number, E>,
		make_genesis: G,
	) -> Option<ViableSession<E, &E>>
	where
		G: FnOnce(E::Slot) -> E,
	{
		match descriptor {
			ViableSessionDescriptor::UnimportedGenesis(slot) =>
				Some(ViableSession::UnimportedGenesis(make_genesis(*slot))),
			ViableSessionDescriptor::Signaled(identifier, _) =>
				self.session(&identifier).map(ViableSession::Signaled),
		}
	}

	/// Get a mutable reference to an session with given identifier.
	pub fn session_mut(&mut self, id: &SessionIdentifier<Hash, Number>) -> Option<&mut E> {
		self.sessions.get_mut(&(id.hash, id.number)).and_then(|v| match v {
			PersistedSession::Genesis(ref mut session_0, _)
				if id.position == SessionIdentifierPosition::Genesis0 =>
				Some(session_0),
			PersistedSession::Genesis(_, ref mut session_1)
				if id.position == SessionIdentifierPosition::Genesis1 =>
				Some(session_1),
			PersistedSession::Regular(ref mut session_n)
				if id.position == SessionIdentifierPosition::Regular =>
				Some(session_n),
			_ => None,
		})
	}

	/// Get a mutable reference to a viable session with given descriptor.
	pub fn viable_session_mut<G>(
		&mut self,
		descriptor: &ViableSessionDescriptor<Hash, Number, E>,
		make_genesis: G,
	) -> Option<ViableSession<E, &mut E>>
	where
		G: FnOnce(E::Slot) -> E,
	{
		match descriptor {
			ViableSessionDescriptor::UnimportedGenesis(slot) =>
				Some(ViableSession::UnimportedGenesis(make_genesis(*slot))),
			ViableSessionDescriptor::Signaled(identifier, _) =>
				self.session_mut(&identifier).map(ViableSession::Signaled),
		}
	}

	/// Get the session data from an session descriptor.
	///
	/// Note that this function ignores the fact that an genesis session might need to be imported.
	/// Mostly useful for testing.
	pub fn session_data<G>(
		&self,
		descriptor: &ViableSessionDescriptor<Hash, Number, E>,
		make_genesis: G,
	) -> Option<E>
	where
		G: FnOnce(E::Slot) -> E,
		E: Clone,
	{
		match descriptor {
			ViableSessionDescriptor::UnimportedGenesis(slot) => Some(make_genesis(*slot)),
			ViableSessionDescriptor::Signaled(identifier, _) => self.session(&identifier).cloned(),
		}
	}

	/// Finds the session data for a child of the given block. Similar to
	/// `session_descriptor_for_child_of` but returns the full data.
	///
	/// Note that this function ignores the fact that an genesis session might need to be imported.
	/// Mostly useful for testing.
	pub fn session_data_for_child_of<D: IsDescendentOfBuilder<Hash>, G>(
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
		let descriptor = self.session_descriptor_for_child_of(
			descendent_of_builder,
			parent_hash,
			parent_number,
			slot,
		)?;

		Ok(descriptor.and_then(|des| self.session_data(&des, make_genesis)))
	}

	/// Finds the session for a child of the given block, assuming the given slot number.
	///
	/// If the returned session is an `UnimportedGenesis` session, it should be imported into the
	/// tree.
	pub fn session_descriptor_for_child_of<D: IsDescendentOfBuilder<Hash>>(
		&self,
		descendent_of_builder: D,
		parent_hash: &Hash,
		parent_number: Number,
		slot: E::Slot,
	) -> Result<Option<ViableSessionDescriptor<Hash, Number, E>>, fork_tree::Error<D::Error>> {
		if parent_number == Zero::zero() {
			// need to insert the genesis session.
			return Ok(Some(ViableSessionDescriptor::UnimportedGenesis(slot)))
		}

		if let Some(gap) = &self.gap {
			if let Some((hash, number, hdr, position)) = gap.matches(slot) {
				return Ok(Some(ViableSessionDescriptor::Signaled(
					SessionIdentifier { position, hash, number },
					hdr,
				)))
			}
		}

		// find_node_where will give you the node in the fork-tree which is an ancestor
		// of the `parent_hash` by default. if the last session was signalled at the parent_hash,
		// then it won't be returned. we need to create a new fake chain head hash which
		// "descends" from our parent-hash.
		let fake_head_hash = fake_head_hash(parent_hash);

		let is_descendent_of =
			descendent_of_builder.build_is_descendent_of(Some((fake_head_hash, *parent_hash)));

		// We want to find the deepest node in the tree which is an ancestor
		// of our block and where the start slot of the session was before the
		// slot of our block. The genesis special-case doesn't need to look
		// at session_1 -- all we're doing here is figuring out which node
		// we need.
		let predicate = |session: &PersistedSessionHeader<E>| match *session {
			PersistedSessionHeader::Genesis(ref session_0, _) => session_0.start_slot <= slot,
			PersistedSessionHeader::Regular(ref session_n) => session_n.start_slot <= slot,
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
							// and here we figure out which of the internal sessions
							// of a genesis node to use based on their start slot.
							PersistedSessionHeader::Genesis(ref session_0, ref session_1) => {
								if session_1.start_slot <= slot {
									(SessionIdentifierPosition::Genesis1, session_1.clone())
								} else {
									(SessionIdentifierPosition::Genesis0, session_0.clone())
								}
							},
							PersistedSessionHeader::Regular(ref session_n) =>
								(SessionIdentifierPosition::Regular, session_n.clone()),
						},
						node,
					)
				})
				.map(|((position, header), node)| {
					ViableSessionDescriptor::Signaled(
						SessionIdentifier { position, hash: node.hash, number: node.number },
						header,
					)
				})
			})
	}

	/// Import a new session-change, signalled at the given block.
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
		session: IncrementedSession<E>,
	) -> Result<(), fork_tree::Error<D::Error>> {
		let is_descendent_of =
			descendent_of_builder.build_is_descendent_of(Some((hash, parent_hash)));
		let slot = session.as_ref().start_slot();
		let IncrementedSession(mut session) = session;
		let header = PersistedSessionHeader::<E>::from(&session);

		if let Some(gap) = &mut self.gap {
			if let PersistedSession::Regular(e) = session {
				session = match gap.import(slot, hash.clone(), number.clone(), e) {
					Ok(()) => return Ok(()),
					Err(e) => PersistedSession::Regular(e),
				}
			}
		} else if session.is_genesis() && !self.sessions.values().all(|e| e.is_genesis()) {
			// There's a genesis session imported when we already have an active session.
			// This happens after the warp sync as the ancient blocks download start.
			// We need to start tracking gap sessions here.
			self.gap = Some(GapSessions { current: (hash, number, session), next: None });
			return Ok(())
		}

		let res = self.inner.import(hash, number, header, &is_descendent_of);

		match res {
			Ok(_) | Err(fork_tree::Error::Duplicate) => {
				self.sessions.insert((hash, number), session);
				Ok(())
			},
			Err(e) => Err(e),
		}
	}

	/// Return the inner fork tree.
	pub fn tree(&self) -> &ForkTree<Hash, Number, PersistedSessionHeader<E>> {
		&self.inner
	}

	/// Reset to a specified pair of sessions, as if they were announced at blocks `parent_hash` and
	/// `hash`.
	pub fn reset(&mut self, parent_hash: Hash, hash: Hash, number: Number, current: E, next: E) {
		self.inner = ForkTree::new();
		self.sessions.clear();
		let persisted = PersistedSession::Regular(current);
		let header = PersistedSessionHeader::from(&persisted);
		let _res = self.inner.import(parent_hash, number - One::one(), header, &|_, _| {
			Ok(false) as Result<bool, fork_tree::Error<ClientError>>
		});
		self.sessions.insert((parent_hash, number - One::one()), persisted);

		let persisted = PersistedSession::Regular(next);
		let header = PersistedSessionHeader::from(&persisted);
		let _res = self.inner.import(hash, number, header, &|_, _| {
			Ok(true) as Result<bool, fork_tree::Error<ClientError>>
		});
		self.sessions.insert((hash, number), persisted);
	}

	/// Revert to a specified block given its `hash` and `number`.
	/// This removes all the session changes information that were announced by
	/// all the given block descendents.
	pub fn revert<D: IsDescendentOfBuilder<Hash>>(
		&mut self,
		descendent_of_builder: D,
		hash: Hash,
		number: Number,
	) {
		let is_descendent_of = descendent_of_builder.build_is_descendent_of(None);

		let filter = |node_hash: &Hash, node_num: &Number, _: &PersistedSessionHeader<E>| {
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
			self.sessions.remove(&(h, n));
		});
	}
}

/// Type alias to produce the session-changes tree from a block type.
pub type SessionChangesFor<Block, Session> =
	SessionChanges<<Block as BlockT>::Hash, NumberFor<Block>, Session>;

/// A shared session changes tree.
pub type SharedSessionChanges<Block, Session> =
	sc_consensus::shared_data::SharedData<SessionChangesFor<Block, Session>>;

#[cfg(test)]
mod tests {
	use super::{Session as SessionT, *};

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
	struct Session {
		start_slot: Slot,
		duration: Slot,
	}

	impl SessionT for Session {
		type NextSessionDescriptor = ();
		type Slot = Slot;

		fn increment(&self, _: ()) -> Self {
			Session { start_slot: self.start_slot + self.duration, duration: self.duration }
		}

		fn end_slot(&self) -> Slot {
			self.start_slot + self.duration
		}

		fn start_slot(&self) -> Slot {
			self.start_slot
		}
	}

	#[test]
	fn genesis_session_is_created_but_not_imported() {
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

		let session_changes = SessionChanges::<_, _, Session>::new();
		let genesis_session = session_changes
			.session_descriptor_for_child_of(&is_descendent_of, b"0", 0, 10101)
			.unwrap()
			.unwrap();

		match genesis_session {
			ViableSessionDescriptor::UnimportedGenesis(slot) => {
				assert_eq!(slot, 10101u64);
			},
			_ => panic!("should be unimported genesis"),
		};

		let genesis_session_2 = session_changes
			.session_descriptor_for_child_of(&is_descendent_of, b"0", 0, 10102)
			.unwrap()
			.unwrap();

		match genesis_session_2 {
			ViableSessionDescriptor::UnimportedGenesis(slot) => {
				assert_eq!(slot, 10102u64);
			},
			_ => panic!("should be unimported genesis"),
		};
	}

	#[test]
	fn session_changes_between_blocks() {
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

		let make_genesis = |slot| Session { start_slot: slot, duration: 100 };

		let mut session_changes = SessionChanges::<_, _, Session>::new();
		let genesis_session = session_changes
			.session_descriptor_for_child_of(&is_descendent_of, b"0", 0, 100)
			.unwrap()
			.unwrap();

		assert_eq!(genesis_session, ViableSessionDescriptor::UnimportedGenesis(100));

		let import_session_1 =
			session_changes.viable_session(&genesis_session, &make_genesis).unwrap().increment(());
		let session_1 = import_session_1.as_ref().clone();

		session_changes
			.import(&is_descendent_of, *b"A", 1, *b"0", import_session_1)
			.unwrap();
		let genesis_session = session_changes.session_data(&genesis_session, &make_genesis).unwrap();

		assert!(is_descendent_of(b"0", b"A").unwrap());

		let end_slot = genesis_session.end_slot();
		assert_eq!(end_slot, session_1.start_slot);

		{
			// x is still within the genesis session.
			let x = session_changes
				.session_data_for_child_of(&is_descendent_of, b"A", 1, end_slot - 1, &make_genesis)
				.unwrap()
				.unwrap();

			assert_eq!(x, genesis_session);
		}

		{
			// x is now at the next session, because the block is now at the
			// start slot of session 1.
			let x = session_changes
				.session_data_for_child_of(&is_descendent_of, b"A", 1, end_slot, &make_genesis)
				.unwrap()
				.unwrap();

			assert_eq!(x, session_1);
		}

		{
			// x is now at the next session, because the block is now after
			// start slot of session 1.
			let x = session_changes
				.session_data_for_child_of(
					&is_descendent_of,
					b"A",
					1,
					session_1.end_slot() - 1,
					&make_genesis,
				)
				.unwrap()
				.unwrap();

			assert_eq!(x, session_1);
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

		let make_genesis = |slot| Session { start_slot: slot, duration };

		let mut session_changes = SessionChanges::new();
		let next_descriptor = ();

		// insert genesis session for A
		{
			let genesis_session_a_descriptor = session_changes
				.session_descriptor_for_child_of(&is_descendent_of, b"0", 0, 100)
				.unwrap()
				.unwrap();

			let incremented_session = session_changes
				.viable_session(&genesis_session_a_descriptor, &make_genesis)
				.unwrap()
				.increment(next_descriptor.clone());

			session_changes
				.import(&is_descendent_of, *b"A", 1, *b"0", incremented_session)
				.unwrap();
		}

		// insert genesis session for X
		{
			let genesis_session_x_descriptor = session_changes
				.session_descriptor_for_child_of(&is_descendent_of, b"0", 0, 1000)
				.unwrap()
				.unwrap();

			let incremented_session = session_changes
				.viable_session(&genesis_session_x_descriptor, &make_genesis)
				.unwrap()
				.increment(next_descriptor.clone());

			session_changes
				.import(&is_descendent_of, *b"X", 1, *b"0", incremented_session)
				.unwrap();
		}

		// now check that the genesis sessions for our respective block 1s
		// respect the chain structure.
		{
			let session_for_a_child = session_changes
				.session_data_for_child_of(&is_descendent_of, b"A", 1, 101, &make_genesis)
				.unwrap()
				.unwrap();

			assert_eq!(session_for_a_child, make_genesis(100));

			let session_for_x_child = session_changes
				.session_data_for_child_of(&is_descendent_of, b"X", 1, 1001, &make_genesis)
				.unwrap()
				.unwrap();

			assert_eq!(session_for_x_child, make_genesis(1000));

			let session_for_x_child_before_genesis = session_changes
				.session_data_for_child_of(&is_descendent_of, b"X", 1, 101, &make_genesis)
				.unwrap();

			// even though there is a genesis session at that slot, it's not in
			// this chain.
			assert!(session_for_x_child_before_genesis.is_none());
		}
	}

	/// Test that ensures that the gap is not enabled when we import multiple genesis blocks.
	#[test]
	fn gap_is_not_enabled_when_multiple_genesis_sessions_are_imported() {
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

		let make_genesis = |slot| Session { start_slot: slot, duration };

		let mut session_changes = SessionChanges::new();
		let next_descriptor = ();

		// insert genesis session for A
		{
			let genesis_session_a_descriptor = session_changes
				.session_descriptor_for_child_of(&is_descendent_of, b"0", 0, 100)
				.unwrap()
				.unwrap();

			let incremented_session = session_changes
				.viable_session(&genesis_session_a_descriptor, &make_genesis)
				.unwrap()
				.increment(next_descriptor.clone());

			session_changes
				.import(&is_descendent_of, *b"A", 1, *b"0", incremented_session)
				.unwrap();
		}

		// insert genesis session for X
		{
			let genesis_session_x_descriptor = session_changes
				.session_descriptor_for_child_of(&is_descendent_of, b"0", 0, 1000)
				.unwrap()
				.unwrap();

			let incremented_session = session_changes
				.viable_session(&genesis_session_x_descriptor, &make_genesis)
				.unwrap()
				.increment(next_descriptor.clone());

			session_changes
				.import(&is_descendent_of, *b"X", 1, *b"0", incremented_session)
				.unwrap();
		}

		// Clearing the gap should be a no-op.
		session_changes.clear_gap();

		// Check that both sessions are available.
		session_changes
			.session_data_for_child_of(&is_descendent_of, b"A", 1, 101, &make_genesis)
			.unwrap()
			.unwrap();

		session_changes
			.session_data_for_child_of(&is_descendent_of, b"X", 1, 1001, &make_genesis)
			.unwrap()
			.unwrap();
	}

	#[test]
	fn gap_sessions_advance() {
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

		let make_genesis = |slot| Session { start_slot: slot, duration };

		let mut session_changes = SessionChanges::new();
		let next_descriptor = ();

		let session42 = Session { start_slot: 42, duration: 100 };
		let session43 = Session { start_slot: 43, duration: 100 };
		session_changes.reset(*b"0", *b"1", 4200, session42, session43);
		assert!(session_changes.gap.is_none());

		// Import a new genesis session, this should crate the gap.
		let genesis_session_a_descriptor = session_changes
			.session_descriptor_for_child_of(&is_descendent_of, b"0", 0, 100)
			.unwrap()
			.unwrap();

		let incremented_session = session_changes
			.viable_session(&genesis_session_a_descriptor, &make_genesis)
			.unwrap()
			.increment(next_descriptor.clone());

		session_changes
			.import(&is_descendent_of, *b"1", 1, *b"0", incremented_session)
			.unwrap();
		assert!(session_changes.gap.is_some());

		let genesis_session = session_changes
			.session_descriptor_for_child_of(&is_descendent_of, b"0", 0, 100)
			.unwrap()
			.unwrap();

		assert_eq!(genesis_session, ViableSessionDescriptor::UnimportedGenesis(100));

		// Import more sessions and check that gap advances.
		let import_session_1 =
			session_changes.viable_session(&genesis_session, &make_genesis).unwrap().increment(());

		let session_1 = import_session_1.as_ref().clone();
		session_changes
			.import(&is_descendent_of, *b"1", 1, *b"0", import_session_1)
			.unwrap();
		let genesis_session_data = session_changes.session_data(&genesis_session, &make_genesis).unwrap();
		let end_slot = genesis_session_data.end_slot();
		let x = session_changes
			.session_data_for_child_of(&is_descendent_of, b"1", 1, end_slot, &make_genesis)
			.unwrap()
			.unwrap();

		assert_eq!(x, session_1);
		assert_eq!(session_changes.gap.as_ref().unwrap().current.0, *b"1");
		assert!(session_changes.gap.as_ref().unwrap().next.is_none());

		let session_1_desriptor = session_changes
			.session_descriptor_for_child_of(&is_descendent_of, b"1", 1, end_slot)
			.unwrap()
			.unwrap();
		let session_1 = session_changes.session_data(&session_1_desriptor, &make_genesis).unwrap();
		let import_session_2 = session_changes
			.viable_session(&session_1_desriptor, &make_genesis)
			.unwrap()
			.increment(());
		let session_2 = import_session_2.as_ref().clone();
		session_changes
			.import(&is_descendent_of, *b"2", 2, *b"1", import_session_2)
			.unwrap();

		let end_slot = session_1.end_slot();
		let x = session_changes
			.session_data_for_child_of(&is_descendent_of, b"2", 2, end_slot, &make_genesis)
			.unwrap()
			.unwrap();
		assert_eq!(session_changes.gap.as_ref().unwrap().current.0, *b"1");
		assert_eq!(session_changes.gap.as_ref().unwrap().next.as_ref().unwrap().0, *b"2");
		assert_eq!(x, session_2);

		let session_2_desriptor = session_changes
			.session_descriptor_for_child_of(&is_descendent_of, b"2", 2, end_slot)
			.unwrap()
			.unwrap();
		let import_session_3 = session_changes
			.viable_session(&session_2_desriptor, &make_genesis)
			.unwrap()
			.increment(());
		session_changes
			.import(&is_descendent_of, *b"3", 3, *b"2", import_session_3)
			.unwrap();

		assert_eq!(session_changes.gap.as_ref().unwrap().current.0, *b"2");

		session_changes.clear_gap();
		assert!(session_changes.gap.is_none());
	}
}
