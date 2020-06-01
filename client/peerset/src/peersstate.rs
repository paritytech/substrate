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

//! Reputation and slots allocation system behind the peerset.
//!
//! The [`PeersState`] state machine is responsible for managing the reputation and allocating
//! slots. It holds a list of nodes, each associated with a reputation value and whether we are
//! connected or not to this node. Thanks to this list, it knows how many slots are occupied. It
//! also holds a list of nodes which don't occupy slots.
//!
//! > Note: This module is purely dedicated to managing slots and reputations. Features such as
//! >       for example connecting to some nodes in priority should be added outside of this
//! >       module, rather than inside.

use libp2p::PeerId;
use log::error;
use std::{borrow::Cow, collections::{HashSet, HashMap}};
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
	/// 			easily select the best node to connect to. As a first draft, however, we don't
	/// 			sort, to make the logic easier.
	nodes: HashMap<PeerId, Node>,

	/// Number of slot-occupying nodes for which the `ConnectionState` is `In`.
	num_in: u32,

	/// Number of slot-occupying nodes for which the `ConnectionState` is `In`.
	num_out: u32,

	/// Maximum allowed number of slot-occupying nodes for which the `ConnectionState` is `In`.
	max_in: u32,

	/// Maximum allowed number of slot-occupying nodes for which the `ConnectionState` is `Out`.
	max_out: u32,

	/// List of node identities (discovered or not) that don't occupy slots.
	///
	/// Note for future readers: this module is purely dedicated to managing slots. If you are
	/// considering adding more features, please consider doing so outside of this module rather
	/// than inside.
	no_slot_nodes: HashSet<PeerId>,
}

/// State of a single node that we know about.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Node {
	/// Whether we are connected to this node.
	connection_state: ConnectionState,

	/// Reputation value of the node, between `i32::min_value` (we hate that node) and
	/// `i32::max_value` (we love that node).
	reputation: i32,
}

impl Default for Node {
	fn default() -> Node {
		Node {
			connection_state: ConnectionState::NotConnected {
				last_connected: Instant::now(),
			},
			reputation: 0,
		}
	}
}

/// Whether we are connected to a node.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum ConnectionState {
	/// We are connected through an ingoing connection.
	In,
	/// We are connected through an outgoing connection.
	Out,
	/// We are not connected to this node.
	NotConnected {
		/// When we were last connected to the node, or if we were never connected when we
		/// discovered it.
		last_connected: Instant,
	},
}

impl ConnectionState {
	/// Returns `true` for `In` and `Out`.
	fn is_connected(self) -> bool {
		match self {
			ConnectionState::In => true,
			ConnectionState::Out => true,
			ConnectionState::NotConnected { .. } => false,
		}
	}
}

impl PeersState {
	/// Builds a new empty `PeersState`.
	pub fn new(in_peers: u32, out_peers: u32) -> Self {
		PeersState {
			nodes: HashMap::new(),
			num_in: 0,
			num_out: 0,
			max_in: in_peers,
			max_out: out_peers,
			no_slot_nodes: HashSet::new(),
		}
	}

	/// Returns an object that grants access to the state of a peer.
	pub fn peer<'a>(&'a mut self, peer_id: &'a PeerId) -> Peer<'a> {
		match self.nodes.get_mut(peer_id) {
			None => return Peer::Unknown(UnknownPeer {
				parent: self,
				peer_id: Cow::Borrowed(peer_id),
			}),
			Some(peer) => {
				if peer.connection_state.is_connected() {
					Peer::Connected(ConnectedPeer {
						state: self,
						peer_id: Cow::Borrowed(peer_id),
					})
				} else {
					Peer::NotConnected(NotConnectedPeer {
						state: self,
						peer_id: Cow::Borrowed(peer_id),
					})
				}
			}
		}
	}

	/// Returns the list of all the peers we know of.
	// Note: this method could theoretically return a `Peer`, but implementing that
	// isn't simple.
	pub fn peers(&self) -> impl ExactSizeIterator<Item = &PeerId> {
		self.nodes.keys()
	}

	/// Returns the list of peers we are connected to.
	// Note: this method could theoretically return a `ConnectedPeer`, but implementing that
	// isn't simple.
	pub fn connected_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.nodes.iter()
			.filter(|(_, p)| p.connection_state.is_connected())
			.map(|(p, _)| p)
	}

	/// Returns the peer with the highest reputation and that we are not connected to.
	///
	/// If multiple nodes have the same reputation, which one is returned is unspecified.
	pub fn highest_not_connected_peer(&mut self) -> Option<NotConnectedPeer> {
		let outcome = self.nodes
			.iter_mut()
			.filter(|(_, Node { connection_state, .. })| !connection_state.is_connected())
			.fold(None::<(&PeerId, &mut Node)>, |mut cur_node, to_try| {
				if let Some(cur_node) = cur_node.take() {
					if cur_node.1.reputation >= to_try.1.reputation {
						return Some(cur_node);
					}
				}
				Some(to_try)
			})
			.map(|(peer_id, _)| peer_id.clone());

		if let Some(peer_id) = outcome {
			Some(NotConnectedPeer {
				state: self,
				peer_id: Cow::Owned(peer_id),
			})
		} else {
			None
		}
	}

	/// Add a node to the list of nodes that don't occupy slots.
	///
	/// Has no effect if the peer was already in the group.
	pub fn add_no_slot_node(&mut self, peer_id: PeerId) {
		// Reminder: `HashSet::insert` returns false if the node was already in the set
		if !self.no_slot_nodes.insert(peer_id.clone()) {
			return;
		}

		if let Some(peer) = self.nodes.get_mut(&peer_id) {
			match peer.connection_state {
				ConnectionState::In => self.num_in -= 1,
				ConnectionState::Out => self.num_out -= 1,
				ConnectionState::NotConnected { .. } => {},
			}
		}
	}

	/// Removes a node from the list of nodes that don't occupy slots.
	///
	/// Has no effect if the peer was not in the group.
	pub fn remove_no_slot_node(&mut self, peer_id: &PeerId) {
		// Reminder: `HashSet::remove` returns false if the node was already not in the set
		if !self.no_slot_nodes.remove(peer_id) {
			return;
		}

		if let Some(peer) = self.nodes.get_mut(peer_id) {
			match peer.connection_state {
				ConnectionState::In => self.num_in += 1,
				ConnectionState::Out => self.num_out += 1,
				ConnectionState::NotConnected { .. } => {},
			}
		}
	}
}

/// Grants access to the state of a peer in the `PeersState`.
pub enum Peer<'a> {
	/// We are connected to this node.
	Connected(ConnectedPeer<'a>),
	/// We are not connected to this node.
	NotConnected(NotConnectedPeer<'a>),
	/// We have never heard of this node.
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
	#[cfg(test)]	// Feel free to remove this if this function is needed outside of tests
	pub fn into_not_connected(self) -> Option<NotConnectedPeer<'a>> {
		match self {
			Peer::Connected(_) => None,
			Peer::NotConnected(peer) => Some(peer),
			Peer::Unknown(_) => None,
		}
	}

	/// If we are the `Unknown` variant, returns the inner `ConnectedPeer`. Returns `None`
	/// otherwise.
	#[cfg(test)]	// Feel free to remove this if this function is needed outside of tests
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
	peer_id: Cow<'a, PeerId>,
}

impl<'a> ConnectedPeer<'a> {
	/// Destroys this `ConnectedPeer` and returns the `PeerId` inside of it.
	pub fn into_peer_id(self) -> PeerId {
		self.peer_id.into_owned()
	}

	/// Switches the peer to "not connected".
	pub fn disconnect(self) -> NotConnectedPeer<'a> {
		let is_no_slot_occupy = self.state.no_slot_nodes.contains(&*self.peer_id);
		if let Some(mut node) = self.state.nodes.get_mut(&*self.peer_id) {
			if !is_no_slot_occupy {
				match node.connection_state {
					ConnectionState::In => self.state.num_in -= 1,
					ConnectionState::Out => self.state.num_out -= 1,
					ConnectionState::NotConnected { .. } =>
						debug_assert!(false, "State inconsistency: disconnecting a disconnected node")
				}
			}
			node.connection_state = ConnectionState::NotConnected {
				last_connected: Instant::now(),
			};
		} else {
			debug_assert!(false, "State inconsistency: disconnecting a disconnected node");
		}

		NotConnectedPeer {
			state: self.state,
			peer_id: self.peer_id,
		}
	}

	/// Returns the reputation value of the node.
	pub fn reputation(&self) -> i32 {
		self.state.nodes.get(&*self.peer_id).map_or(0, |p| p.reputation)
	}

	/// Sets the reputation of the peer.
	pub fn set_reputation(&mut self, value: i32) {
		if let Some(node) = self.state.nodes.get_mut(&*self.peer_id) {
			node.reputation = value;
		} else {
			debug_assert!(false, "State inconsistency: set_reputation on an unknown node");
		}
	}

	/// Performs an arithmetic addition on the reputation score of that peer.
	///
	/// In case of overflow, the value will be capped.
	pub fn add_reputation(&mut self, modifier: i32) {
		if let Some(node) = self.state.nodes.get_mut(&*self.peer_id) {
			node.reputation = node.reputation.saturating_add(modifier);
		} else {
			debug_assert!(false, "State inconsistency: add_reputation on an unknown node");
		}
	}
}

/// A peer that is not connected to us.
#[derive(Debug)]
pub struct NotConnectedPeer<'a> {
	state: &'a mut PeersState,
	peer_id: Cow<'a, PeerId>,
}

impl<'a> NotConnectedPeer<'a> {
	/// Destroys this `NotConnectedPeer` and returns the `PeerId` inside of it.
	#[cfg(test)]	// Feel free to remove this if this function is needed outside of tests
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

		if let ConnectionState::NotConnected { last_connected } = &mut state.connection_state {
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

		match state.connection_state {
			ConnectionState::NotConnected { last_connected } => last_connected,
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
		let is_no_slot_occupy = self.state.no_slot_nodes.contains(&*self.peer_id);

		// Note that it is possible for num_out to be strictly superior to the max, in case we were
		// connected to reserved node then marked them as not reserved.
		if self.state.num_out >= self.state.max_out && !is_no_slot_occupy {
			return Err(self);
		}

		if let Some(mut peer) = self.state.nodes.get_mut(&*self.peer_id) {
			peer.connection_state = ConnectionState::Out;
			if !is_no_slot_occupy {
				self.state.num_out += 1;
			}
		} else {
			debug_assert!(false, "State inconsistency: try_outgoing on an unknown node");
		}

		Ok(ConnectedPeer {
			state: self.state,
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
		let is_no_slot_occupy = self.state.no_slot_nodes.contains(&*self.peer_id);

		// Note that it is possible for num_in to be strictly superior to the max, in case we were
		// connected to reserved node then marked them as not reserved.
		if self.state.num_in >= self.state.max_in && !is_no_slot_occupy {
			return Err(self);
		}

		if let Some(mut peer) = self.state.nodes.get_mut(&*self.peer_id) {
			peer.connection_state = ConnectionState::In;
			if !is_no_slot_occupy {
				self.state.num_in += 1;
			}
		} else {
			debug_assert!(false, "State inconsistency: try_accept_incoming on an unknown node");
		}

		Ok(ConnectedPeer {
			state: self.state,
			peer_id: self.peer_id,
		})
	}

	/// Returns the reputation value of the node.
	pub fn reputation(&self) -> i32 {
		self.state.nodes.get(&*self.peer_id).map_or(0, |p| p.reputation)
	}

	/// Sets the reputation of the peer.
	pub fn set_reputation(&mut self, value: i32) {
		if let Some(node) = self.state.nodes.get_mut(&*self.peer_id) {
			node.reputation = value;
		} else {
			debug_assert!(false, "State inconsistency: set_reputation on an unknown node");
		}
	}

	/// Performs an arithmetic addition on the reputation score of that peer.
	///
	/// In case of overflow, the value will be capped.
	pub fn add_reputation(&mut self, modifier: i32) {
		if let Some(node) = self.state.nodes.get_mut(&*self.peer_id) {
			node.reputation = node.reputation.saturating_add(modifier);
		} else {
			debug_assert!(false, "State inconsistency: add_reputation on an unknown node");
		}
	}

	/// Un-discovers the peer. Removes it from the list.
	pub fn forget_peer(self) -> UnknownPeer<'a> {
		if self.state.nodes.remove(&*self.peer_id).is_none() {
			error!(
				target: "peerset",
				"State inconsistency with {} when forgetting peer",
				self.peer_id
			);
		}

		UnknownPeer {
			parent: self.state,
			peer_id: self.peer_id,
		}
	}
}

/// A peer that we have never heard of.
pub struct UnknownPeer<'a> {
	parent: &'a mut PeersState,
	peer_id: Cow<'a, PeerId>,
}

impl<'a> UnknownPeer<'a> {
	/// Inserts the peer identity in our list.
	///
	/// The node starts with a reputation of 0. You can adjust these default
	/// values using the `NotConnectedPeer` that this method returns.
	pub fn discover(self) -> NotConnectedPeer<'a> {
		self.parent.nodes.insert(self.peer_id.clone().into_owned(), Node {
			connection_state: ConnectionState::NotConnected {
				last_connected: Instant::now(),
			},
			reputation: 0,
		});

		let state = self.parent;
		NotConnectedPeer {
			state,
			peer_id: self.peer_id,
		}
	}
}

#[cfg(test)]
mod tests {
	use super::{PeersState, Peer};
	use libp2p::PeerId;

	#[test]
	fn full_slots_in() {
		let mut peers_state = PeersState::new(1, 1);
		let id1 = PeerId::random();
		let id2 = PeerId::random();

		if let Peer::Unknown(e) = peers_state.peer(&id1) {
			assert!(e.discover().try_accept_incoming().is_ok());
		}

		if let Peer::Unknown(e) = peers_state.peer(&id2) {
			assert!(e.discover().try_accept_incoming().is_err());
		}
	}

	#[test]
	fn no_slot_node_doesnt_use_slot() {
		let mut peers_state = PeersState::new(1, 1);
		let id1 = PeerId::random();
		let id2 = PeerId::random();

		peers_state.add_no_slot_node(id1.clone());
		if let Peer::Unknown(p) = peers_state.peer(&id1) {
			assert!(p.discover().try_accept_incoming().is_ok());
		} else { panic!() }

		if let Peer::Unknown(e) = peers_state.peer(&id2) {
			assert!(e.discover().try_accept_incoming().is_ok());
		} else { panic!() }
	}

	#[test]
	fn disconnecting_frees_slot() {
		let mut peers_state = PeersState::new(1, 1);
		let id1 = PeerId::random();
		let id2 = PeerId::random();

		assert!(peers_state.peer(&id1).into_unknown().unwrap().discover().try_accept_incoming().is_ok());
		assert!(peers_state.peer(&id2).into_unknown().unwrap().discover().try_accept_incoming().is_err());
		peers_state.peer(&id1).into_connected().unwrap().disconnect();
		assert!(peers_state.peer(&id2).into_not_connected().unwrap().try_accept_incoming().is_ok());
	}

	#[test]
	fn highest_not_connected_peer() {
		let mut peers_state = PeersState::new(25, 25);
		let id1 = PeerId::random();
		let id2 = PeerId::random();

		assert!(peers_state.highest_not_connected_peer().is_none());
		peers_state.peer(&id1).into_unknown().unwrap().discover().set_reputation(50);
		peers_state.peer(&id2).into_unknown().unwrap().discover().set_reputation(25);
		assert_eq!(peers_state.highest_not_connected_peer().map(|p| p.into_peer_id()), Some(id1.clone()));
		peers_state.peer(&id2).into_not_connected().unwrap().set_reputation(75);
		assert_eq!(peers_state.highest_not_connected_peer().map(|p| p.into_peer_id()), Some(id2.clone()));
		peers_state.peer(&id2).into_not_connected().unwrap().try_accept_incoming().unwrap();
		assert_eq!(peers_state.highest_not_connected_peer().map(|p| p.into_peer_id()), Some(id1.clone()));
		peers_state.peer(&id1).into_not_connected().unwrap().set_reputation(100);
		peers_state.peer(&id2).into_connected().unwrap().disconnect();
		assert_eq!(peers_state.highest_not_connected_peer().map(|p| p.into_peer_id()), Some(id1.clone()));
		peers_state.peer(&id1).into_not_connected().unwrap().set_reputation(-100);
		assert_eq!(peers_state.highest_not_connected_peer().map(|p| p.into_peer_id()), Some(id2.clone()));
	}

	#[test]
	fn disconnect_no_slot_doesnt_panic() {
		let mut peers_state = PeersState::new(1, 1);
		let id = PeerId::random();
		peers_state.add_no_slot_node(id.clone());
		let peer = peers_state.peer(&id).into_unknown().unwrap().discover().try_outgoing().unwrap();
		peer.disconnect();
	}
}
