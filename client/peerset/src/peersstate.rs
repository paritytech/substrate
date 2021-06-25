// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Reputation and slots allocation system behind the peerset.
//!
//! The [`PeersState`] state machine is responsible for managing the reputation and allocating
//! slots. It holds a list of nodes, each associated with a reputation value, a list of sets the
//! node belongs to, and for each set whether we are connected or not to this node. Thanks to this
//! list, it knows how many slots are occupied. It also holds a list of nodes which don't occupy
//! slots.
//!
//! > Note: This module is purely dedicated to managing slots and reputations. Features such as
//! >       for example connecting to some nodes in priority should be added outside of this
//! >       module, rather than inside.

use libp2p::PeerId;
use log::error;
use std::{
	borrow::Cow,
	collections::{HashMap, HashSet, hash_map::{Entry, OccupiedEntry}},
};
use wasm_timer::Instant;

/// State storage behind the peerset.
///
/// # Usage
///
/// This struct is nothing more but a data structure containing a list of nodes, where each node
/// has a reputation and is either connected to us or not.
///
#[derive(Debug, Clone)]
pub struct PeersState {
	/// List of nodes that we know about.
	///
	/// > **Note**: This list should really be ordered by decreasing reputation, so that we can
	///           easily select the best node to connect to. As a first draft, however, we don't
	///           sort, to make the logic easier.
	nodes: HashMap<PeerId, Node>,

	/// Configuration of each set. The size of this `Vec` is never modified.
	sets: Vec<SetInfo>,
}

/// Configuration of a single set.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct SetConfig {
	/// Maximum allowed number of slot-occupying nodes for ingoing connections.
	pub in_peers: u32,

	/// Maximum allowed number of slot-occupying nodes for outgoing connections.
	pub out_peers: u32,
}

/// State of a single set.
#[derive(Debug, Clone, PartialEq, Eq)]
struct SetInfo {
	/// Number of slot-occupying nodes for which the `MembershipState` is `In`.
	num_in: u32,

	/// Number of slot-occupying nodes for which the `MembershipState` is `In`.
	num_out: u32,

	/// Maximum allowed number of slot-occupying nodes for which the `MembershipState` is `In`.
	max_in: u32,

	/// Maximum allowed number of slot-occupying nodes for which the `MembershipState` is `Out`.
	max_out: u32,

	/// List of node identities (discovered or not) that don't occupy slots.
	///
	/// Note for future readers: this module is purely dedicated to managing slots. If you are
	/// considering adding more features, please consider doing so outside of this module rather
	/// than inside.
	no_slot_nodes: HashSet<PeerId>,
}

/// State of a single node that we know about.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Node {
	/// List of sets the node belongs to.
	/// Always has a fixed size equal to the one of [`PeersState::set`]. The various possible sets
	/// are indices into this `Vec`.
	sets: Vec<MembershipState>,

	/// Reputation value of the node, between `i32::MIN` (we hate that node) and
	/// `i32::MAX` (we love that node).
	reputation: i32,
}

impl Node {
	fn new(num_sets: usize) -> Node {
		Node {
			sets: (0..num_sets).map(|_| MembershipState::NotMember).collect(),
			reputation: 0,
		}
	}
}

/// Whether we are connected to a node in the context of a specific set.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum MembershipState {
	/// Node isn't part of that set.
	NotMember,
	/// We are connected through an ingoing connection.
	In,
	/// We are connected through an outgoing connection.
	Out,
	/// Node is part of that set, but we are not connected to it.
	NotConnected {
		/// When we were last connected to the node, or if we were never connected when we
		/// discovered it.
		last_connected: Instant,
	},
}

impl MembershipState {
	/// Returns `true` for `In` and `Out`.
	fn is_connected(self) -> bool {
		match self {
			MembershipState::NotMember => false,
			MembershipState::In => true,
			MembershipState::Out => true,
			MembershipState::NotConnected { .. } => false,
		}
	}
}

impl PeersState {
	/// Builds a new empty `PeersState`.
	pub fn new(sets: impl IntoIterator<Item = SetConfig>) -> Self {
		PeersState {
			nodes: HashMap::new(),
			sets: sets
				.into_iter()
				.map(|config| SetInfo {
					num_in: 0,
					num_out: 0,
					max_in: config.in_peers,
					max_out: config.out_peers,
					no_slot_nodes: HashSet::new(),
				})
				.collect(),
		}
	}

	/// Returns the number of sets.
	///
	/// Corresponds to the number of elements passed to [`PeersState::new`].
	pub fn num_sets(&self) -> usize {
		self.sets.len()
	}

	/// Returns an object that grants access to the reputation value of a peer.
	pub fn peer_reputation(&mut self, peer_id: PeerId) -> Reputation {
		if !self.nodes.contains_key(&peer_id) {
			self.nodes.insert(peer_id.clone(), Node::new(self.sets.len()));
		}

		let entry = match self.nodes.entry(peer_id) {
			Entry::Vacant(_) => unreachable!("guaranteed to be inserted above; qed"),
			Entry::Occupied(e) => e,
		};

		Reputation { node: Some(entry) }
	}

	/// Returns an object that grants access to the state of a peer in the context of a specific
	/// set.
	///
	/// # Panic
	///
	/// `set` must be within range of the sets passed to [`PeersState::new`].
	///
	pub fn peer<'a>(&'a mut self, set: usize, peer_id: &'a PeerId) -> Peer<'a> {
		// The code below will panic anyway if this happens to be false, but this earlier assert
		// makes it explicit what is wrong.
		assert!(set < self.sets.len());

		match self.nodes.get_mut(peer_id).map(|p| &p.sets[set]) {
			None | Some(MembershipState::NotMember) => Peer::Unknown(UnknownPeer {
				parent: self,
				set,
				peer_id: Cow::Borrowed(peer_id),
			}),
			Some(MembershipState::In) | Some(MembershipState::Out) => {
				Peer::Connected(ConnectedPeer {
					state: self,
					set,
					peer_id: Cow::Borrowed(peer_id),
				})
			}
			Some(MembershipState::NotConnected { .. }) => Peer::NotConnected(NotConnectedPeer {
				state: self,
				set,
				peer_id: Cow::Borrowed(peer_id),
			}),
		}
	}

	/// Returns the list of all the peers we know of.
	// Note: this method could theoretically return a `Peer`, but implementing that
	// isn't simple.
	pub fn peers(&self) -> impl ExactSizeIterator<Item = &PeerId> {
		self.nodes.keys()
	}

	/// Returns the list of peers we are connected to in the context of a specific set.
	///
	/// # Panic
	///
	/// `set` must be within range of the sets passed to [`PeersState::new`].
	///
	// Note: this method could theoretically return a `ConnectedPeer`, but implementing that
	// isn't simple.
	pub fn connected_peers(&self, set: usize) -> impl Iterator<Item = &PeerId> {
		// The code below will panic anyway if this happens to be false, but this earlier assert
		// makes it explicit what is wrong.
		assert!(set < self.sets.len());

		self.nodes
			.iter()
			.filter(move |(_, p)| p.sets[set].is_connected())
			.map(|(p, _)| p)
	}

	/// Returns the peer with the highest reputation and that we are not connected to.
	///
	/// If multiple nodes have the same reputation, which one is returned is unspecified.
	///
	/// # Panic
	///
	/// `set` must be within range of the sets passed to [`PeersState::new`].
	///
	pub fn highest_not_connected_peer(&mut self, set: usize) -> Option<NotConnectedPeer> {
		// The code below will panic anyway if this happens to be false, but this earlier assert
		// makes it explicit what is wrong.
		assert!(set < self.sets.len());

		let outcome = self
			.nodes
			.iter_mut()
			.filter(|(_, Node { sets, .. })| {
				match sets[set] {
					MembershipState::NotMember => false,
					MembershipState::In => false,
					MembershipState::Out => false,
					MembershipState::NotConnected { .. } => true,
				}
			})
			.fold(None::<(&PeerId, &mut Node)>, |mut cur_node, to_try| {
				if let Some(cur_node) = cur_node.take() {
					if cur_node.1.reputation >= to_try.1.reputation {
						return Some(cur_node);
					}
				}
				Some(to_try)
			})
			.map(|(peer_id, _)| peer_id.clone());

		outcome.map(move |peer_id| NotConnectedPeer {
				state: self,
				set,
				peer_id: Cow::Owned(peer_id),
			})
	}

	/// Returns `true` if there is a free outgoing slot available related to this set.
	pub fn has_free_outgoing_slot(&self, set: usize) -> bool {
		self.sets[set].num_out < self.sets[set].max_out
	}

	/// Add a node to the list of nodes that don't occupy slots.
	///
	/// Has no effect if the node was already in the group.
	pub fn add_no_slot_node(&mut self, set: usize, peer_id: PeerId) {
		// Reminder: `HashSet::insert` returns false if the node was already in the set
		if !self.sets[set].no_slot_nodes.insert(peer_id.clone()) {
			return;
		}

		if let Some(peer) = self.nodes.get_mut(&peer_id) {
			match peer.sets[set] {
				MembershipState::In => self.sets[set].num_in -= 1,
				MembershipState::Out => self.sets[set].num_out -= 1,
				MembershipState::NotConnected { .. } | MembershipState::NotMember => {}
			}
		}
	}

	/// Removes a node from the list of nodes that don't occupy slots.
	///
	/// Has no effect if the node was not in the group.
	pub fn remove_no_slot_node(&mut self, set: usize, peer_id: &PeerId) {
		// Reminder: `HashSet::remove` returns false if the node was already not in the set
		if !self.sets[set].no_slot_nodes.remove(peer_id) {
			return;
		}

		if let Some(peer) = self.nodes.get_mut(peer_id) {
			match peer.sets[set] {
				MembershipState::In => self.sets[set].num_in += 1,
				MembershipState::Out => self.sets[set].num_out += 1,
				MembershipState::NotConnected { .. } | MembershipState::NotMember => {}
			}
		}
	}
}

/// Grants access to the state of a peer in the [`PeersState`] in the context of a specific set.
pub enum Peer<'a> {
	/// We are connected to this node.
	Connected(ConnectedPeer<'a>),
	/// We are not connected to this node.
	NotConnected(NotConnectedPeer<'a>),
	/// We have never heard of this node, or it is not part of the set.
	Unknown(UnknownPeer<'a>),
}

impl<'a> Peer<'a> {
	/// If we are the `Connected` variant, returns the inner `ConnectedPeer`. Returns `None`
	/// otherwise.
	pub fn into_connected(self) -> Option<ConnectedPeer<'a>> {
		match self {
			Peer::Connected(peer) => Some(peer),
			Peer::NotConnected(_) => None,
			Peer::Unknown(_) => None,
		}
	}

	/// If we are the `Unknown` variant, returns the inner `ConnectedPeer`. Returns `None`
	/// otherwise.
	#[cfg(test)] // Feel free to remove this if this function is needed outside of tests
	pub fn into_not_connected(self) -> Option<NotConnectedPeer<'a>> {
		match self {
			Peer::Connected(_) => None,
			Peer::NotConnected(peer) => Some(peer),
			Peer::Unknown(_) => None,
		}
	}

	/// If we are the `Unknown` variant, returns the inner `ConnectedPeer`. Returns `None`
	/// otherwise.
	#[cfg(test)] // Feel free to remove this if this function is needed outside of tests
	pub fn into_unknown(self) -> Option<UnknownPeer<'a>> {
		match self {
			Peer::Connected(_) => None,
			Peer::NotConnected(_) => None,
			Peer::Unknown(peer) => Some(peer),
		}
	}
}

/// A peer that is connected to us.
pub struct ConnectedPeer<'a> {
	state: &'a mut PeersState,
	set: usize,
	peer_id: Cow<'a, PeerId>,
}

impl<'a> ConnectedPeer<'a> {
	/// Get the `PeerId` associated to this `ConnectedPeer`.
	pub fn peer_id(&self) -> &PeerId {
		&self.peer_id
	}

	/// Destroys this `ConnectedPeer` and returns the `PeerId` inside of it.
	pub fn into_peer_id(self) -> PeerId {
		self.peer_id.into_owned()
	}

	/// Switches the peer to "not connected".
	pub fn disconnect(self) -> NotConnectedPeer<'a> {
		let is_no_slot_occupy = self.state.sets[self.set].no_slot_nodes.contains(&*self.peer_id);
		if let Some(node) = self.state.nodes.get_mut(&*self.peer_id) {
			if !is_no_slot_occupy {
				match node.sets[self.set] {
					MembershipState::In => self.state.sets[self.set].num_in -= 1,
					MembershipState::Out => self.state.sets[self.set].num_out -= 1,
					MembershipState::NotMember | MembershipState::NotConnected { .. } => {
						debug_assert!(
							false,
							"State inconsistency: disconnecting a disconnected node"
						)
					}
				}
			}
			node.sets[self.set] = MembershipState::NotConnected {
				last_connected: Instant::now(),
			};
		} else {
			debug_assert!(
				false,
				"State inconsistency: disconnecting a disconnected node"
			);
		}

		NotConnectedPeer {
			state: self.state,
			set: self.set,
			peer_id: self.peer_id,
		}
	}

	/// Performs an arithmetic addition on the reputation score of that peer.
	///
	/// In case of overflow, the value will be capped.
	///
	/// > **Note**: Reputation values aren't specific to a set but are global per peer.
	pub fn add_reputation(&mut self, modifier: i32) {
		if let Some(node) = self.state.nodes.get_mut(&*self.peer_id) {
			node.reputation = node.reputation.saturating_add(modifier);
		} else {
			debug_assert!(
				false,
				"State inconsistency: add_reputation on an unknown node"
			);
		}
	}

	/// Returns the reputation value of the node.
	///
	/// > **Note**: Reputation values aren't specific to a set but are global per peer.
	pub fn reputation(&self) -> i32 {
		self.state
			.nodes
			.get(&*self.peer_id)
			.map_or(0, |p| p.reputation)
	}
}

/// A peer that is not connected to us.
#[derive(Debug)]
pub struct NotConnectedPeer<'a> {
	state: &'a mut PeersState,
	set: usize,
	peer_id: Cow<'a, PeerId>,
}

impl<'a> NotConnectedPeer<'a> {
	/// Destroys this `NotConnectedPeer` and returns the `PeerId` inside of it.
	pub fn into_peer_id(self) -> PeerId {
		self.peer_id.into_owned()
	}

	/// Bumps the value that `last_connected_or_discovered` would return to now, even if we
	/// didn't connect or disconnect.
	pub fn bump_last_connected_or_discovered(&mut self) {
		let state = match self.state.nodes.get_mut(&*self.peer_id) {
			Some(s) => s,
			None => return,
		};

		if let MembershipState::NotConnected { last_connected } = &mut state.sets[self.set] {
			*last_connected = Instant::now();
		}
	}

	/// Returns when we were last connected to this peer, or when we discovered it if we were
	/// never connected.
	///
	/// Guaranteed to be earlier than calling `Instant::now()` after the function returns.
	pub fn last_connected_or_discovered(&self) -> Instant {
		let state = match self.state.nodes.get(&*self.peer_id) {
			Some(s) => s,
			None => {
				error!(
					target: "peerset",
					"State inconsistency with {}; not connected after borrow",
					self.peer_id
				);
				return Instant::now();
			}
		};

		match state.sets[self.set] {
			MembershipState::NotConnected { last_connected } => last_connected,
			_ => {
				error!(target: "peerset", "State inconsistency with {}", self.peer_id);
				Instant::now()
			}
		}
	}

	/// Tries to set the peer as connected as an outgoing connection.
	///
	/// If there are enough slots available, switches the node to "connected" and returns `Ok`. If
	/// the slots are full, the node stays "not connected" and we return `Err`.
	///
	/// Non-slot-occupying nodes don't count towards the number of slots.
	pub fn try_outgoing(self) -> Result<ConnectedPeer<'a>, NotConnectedPeer<'a>> {
		let is_no_slot_occupy = self.state.sets[self.set].no_slot_nodes.contains(&*self.peer_id);

		// Note that it is possible for num_out to be strictly superior to the max, in case we were
		// connected to reserved node then marked them as not reserved.
		if !self.state.has_free_outgoing_slot(self.set) && !is_no_slot_occupy {
			return Err(self);
		}

		if let Some(peer) = self.state.nodes.get_mut(&*self.peer_id) {
			peer.sets[self.set] = MembershipState::Out;
			if !is_no_slot_occupy {
				self.state.sets[self.set].num_out += 1;
			}
		} else {
			debug_assert!(
				false,
				"State inconsistency: try_outgoing on an unknown node"
			);
		}

		Ok(ConnectedPeer {
			state: self.state,
			set: self.set,
			peer_id: self.peer_id,
		})
	}

	/// Tries to accept the peer as an incoming connection.
	///
	/// If there are enough slots available, switches the node to "connected" and returns `Ok`. If
	/// the slots are full, the node stays "not connected" and we return `Err`.
	///
	/// Non-slot-occupying nodes don't count towards the number of slots.
	pub fn try_accept_incoming(self) -> Result<ConnectedPeer<'a>, NotConnectedPeer<'a>> {
		let is_no_slot_occupy = self.state.sets[self.set].no_slot_nodes.contains(&*self.peer_id);

		// Note that it is possible for num_in to be strictly superior to the max, in case we were
		// connected to reserved node then marked them as not reserved.
		if self.state.sets[self.set].num_in >= self.state.sets[self.set].max_in
			&& !is_no_slot_occupy
		{
			return Err(self);
		}

		if let Some(peer) = self.state.nodes.get_mut(&*self.peer_id) {
			peer.sets[self.set] = MembershipState::In;
			if !is_no_slot_occupy {
				self.state.sets[self.set].num_in += 1;
			}
		} else {
			debug_assert!(
				false,
				"State inconsistency: try_accept_incoming on an unknown node"
			);
		}

		Ok(ConnectedPeer {
			state: self.state,
			set: self.set,
			peer_id: self.peer_id,
		})
	}

	/// Returns the reputation value of the node.
	///
	/// > **Note**: Reputation values aren't specific to a set but are global per peer.
	pub fn reputation(&self) -> i32 {
		self.state
			.nodes
			.get(&*self.peer_id)
			.map_or(0, |p| p.reputation)
	}

	/// Sets the reputation of the peer.
	///
	/// > **Note**: Reputation values aren't specific to a set but are global per peer.
	#[cfg(test)] // Feel free to remove this if this function is needed outside of tests
	pub fn set_reputation(&mut self, value: i32) {
		if let Some(node) = self.state.nodes.get_mut(&*self.peer_id) {
			node.reputation = value;
		} else {
			debug_assert!(
				false,
				"State inconsistency: set_reputation on an unknown node"
			);
		}
	}

	/// Removes the peer from the list of members of the set.
	pub fn forget_peer(self) -> UnknownPeer<'a> {
		if let Some(peer) = self.state.nodes.get_mut(&*self.peer_id) {
			debug_assert!(!matches!(peer.sets[self.set], MembershipState::NotMember));
			peer.sets[self.set] = MembershipState::NotMember;

			// Remove the peer from `self.state.nodes` entirely if it isn't a member of any set.
			if peer.reputation == 0 && peer
				.sets
				.iter()
				.all(|set| matches!(set, MembershipState::NotMember))
			{
				self.state.nodes.remove(&*self.peer_id);
			}
		} else {
			debug_assert!(false, "State inconsistency: forget_peer on an unknown node");
			error!(
				target: "peerset",
				"State inconsistency with {} when forgetting peer",
				self.peer_id
			);
		};

		UnknownPeer {
			parent: self.state,
			set: self.set,
			peer_id: self.peer_id,
		}
	}
}

/// A peer that we have never heard of or that isn't part of the set.
pub struct UnknownPeer<'a> {
	parent: &'a mut PeersState,
	set: usize,
	peer_id: Cow<'a, PeerId>,
}

impl<'a> UnknownPeer<'a> {
	/// Inserts the peer identity in our list.
	///
	/// The node starts with a reputation of 0. You can adjust these default
	/// values using the `NotConnectedPeer` that this method returns.
	pub fn discover(self) -> NotConnectedPeer<'a> {
		let num_sets = self.parent.sets.len();

		self.parent
			.nodes
			.entry(self.peer_id.clone().into_owned())
			.or_insert_with(|| Node::new(num_sets))
			.sets[self.set] = MembershipState::NotConnected {
			last_connected: Instant::now(),
		};

		NotConnectedPeer {
			state: self.parent,
			set: self.set,
			peer_id: self.peer_id,
		}
	}
}

/// Access to the reputation of a peer.
pub struct Reputation<'a> {
	/// Node entry in [`PeersState::nodes`]. Always `Some` except right before dropping.
	node: Option<OccupiedEntry<'a, PeerId, Node>>,
}

impl<'a> Reputation<'a> {
	/// Returns the reputation value of the node.
	pub fn reputation(&self) -> i32 {
		self.node.as_ref().unwrap().get().reputation
	}

	/// Sets the reputation of the peer.
	pub fn set_reputation(&mut self, value: i32) {
		self.node.as_mut().unwrap().get_mut().reputation = value;
	}

	/// Performs an arithmetic addition on the reputation score of that peer.
	///
	/// In case of overflow, the value will be capped.
	pub fn add_reputation(&mut self, modifier: i32) {
		let reputation = &mut self.node.as_mut().unwrap().get_mut().reputation;
		*reputation = reputation.saturating_add(modifier);
	}
}

impl<'a> Drop for Reputation<'a> {
	fn drop(&mut self) {
		if let Some(node) = self.node.take() {
			if node.get().reputation == 0 &&
				node.get().sets.iter().all(|set| matches!(set, MembershipState::NotMember))
			{
				node.remove();
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::{Peer, PeersState, SetConfig};
	use libp2p::PeerId;
	use std::iter;

	#[test]
	fn full_slots_in() {
		let mut peers_state = PeersState::new(iter::once(SetConfig {
			in_peers: 1,
			out_peers: 1,
		}));
		let id1 = PeerId::random();
		let id2 = PeerId::random();

		if let Peer::Unknown(e) = peers_state.peer(0, &id1) {
			assert!(e.discover().try_accept_incoming().is_ok());
		}

		if let Peer::Unknown(e) = peers_state.peer(0, &id2) {
			assert!(e.discover().try_accept_incoming().is_err());
		}
	}

	#[test]
	fn no_slot_node_doesnt_use_slot() {
		let mut peers_state = PeersState::new(iter::once(SetConfig {
			in_peers: 1,
			out_peers: 1,
		}));
		let id1 = PeerId::random();
		let id2 = PeerId::random();

		peers_state.add_no_slot_node(0, id1.clone());
		if let Peer::Unknown(p) = peers_state.peer(0, &id1) {
			assert!(p.discover().try_accept_incoming().is_ok());
		} else {
			panic!()
		}

		if let Peer::Unknown(e) = peers_state.peer(0, &id2) {
			assert!(e.discover().try_accept_incoming().is_ok());
		} else {
			panic!()
		}
	}

	#[test]
	fn disconnecting_frees_slot() {
		let mut peers_state = PeersState::new(iter::once(SetConfig {
			in_peers: 1,
			out_peers: 1,
		}));
		let id1 = PeerId::random();
		let id2 = PeerId::random();

		assert!(peers_state
			.peer(0, &id1)
			.into_unknown()
			.unwrap()
			.discover()
			.try_accept_incoming()
			.is_ok());
		assert!(peers_state
			.peer(0, &id2)
			.into_unknown()
			.unwrap()
			.discover()
			.try_accept_incoming()
			.is_err());
		peers_state
			.peer(0, &id1)
			.into_connected()
			.unwrap()
			.disconnect();
		assert!(peers_state
			.peer(0, &id2)
			.into_not_connected()
			.unwrap()
			.try_accept_incoming()
			.is_ok());
	}

	#[test]
	fn highest_not_connected_peer() {
		let mut peers_state = PeersState::new(iter::once(SetConfig {
			in_peers: 25,
			out_peers: 25,
		}));
		let id1 = PeerId::random();
		let id2 = PeerId::random();

		assert!(peers_state.highest_not_connected_peer(0).is_none());
		peers_state
			.peer(0, &id1)
			.into_unknown()
			.unwrap()
			.discover()
			.set_reputation(50);
		peers_state
			.peer(0, &id2)
			.into_unknown()
			.unwrap()
			.discover()
			.set_reputation(25);
		assert_eq!(
			peers_state
				.highest_not_connected_peer(0)
				.map(|p| p.into_peer_id()),
			Some(id1.clone())
		);
		peers_state
			.peer(0, &id2)
			.into_not_connected()
			.unwrap()
			.set_reputation(75);
		assert_eq!(
			peers_state
				.highest_not_connected_peer(0)
				.map(|p| p.into_peer_id()),
			Some(id2.clone())
		);
		peers_state
			.peer(0, &id2)
			.into_not_connected()
			.unwrap()
			.try_accept_incoming()
			.unwrap();
		assert_eq!(
			peers_state
				.highest_not_connected_peer(0)
				.map(|p| p.into_peer_id()),
			Some(id1.clone())
		);
		peers_state
			.peer(0, &id1)
			.into_not_connected()
			.unwrap()
			.set_reputation(100);
		peers_state
			.peer(0, &id2)
			.into_connected()
			.unwrap()
			.disconnect();
		assert_eq!(
			peers_state
				.highest_not_connected_peer(0)
				.map(|p| p.into_peer_id()),
			Some(id1.clone())
		);
		peers_state
			.peer(0, &id1)
			.into_not_connected()
			.unwrap()
			.set_reputation(-100);
		assert_eq!(
			peers_state
				.highest_not_connected_peer(0)
				.map(|p| p.into_peer_id()),
			Some(id2.clone())
		);
	}

	#[test]
	fn disconnect_no_slot_doesnt_panic() {
		let mut peers_state = PeersState::new(iter::once(SetConfig {
			in_peers: 1,
			out_peers: 1,
		}));
		let id = PeerId::random();
		peers_state.add_no_slot_node(0, id.clone());
		let peer = peers_state
			.peer(0, &id)
			.into_unknown()
			.unwrap()
			.discover()
			.try_outgoing()
			.unwrap();
		peer.disconnect();
	}
}
