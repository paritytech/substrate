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

//! Contains the state storage behind the peerset.

use libp2p::PeerId;
use log::{error, warn};
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

	/// Number of non-priority nodes for which the `ConnectionState` is `In`.
	num_in: u32,

	/// Number of non-priority nodes for which the `ConnectionState` is `In`.
	num_out: u32,

	/// Maximum allowed number of non-priority nodes for which the `ConnectionState` is `In`.
	max_in: u32,

	/// Maximum allowed number of non-priority nodes for which the `ConnectionState` is `Out`.
	max_out: u32,

	/// Priority groups. Each group is identified by a string ID and contains a set of peer IDs.
	priority_nodes: HashMap<String, HashSet<PeerId>>,

	/// Only allow connections to/from peers in a priority group.
	priority_only: bool,
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
	pub fn new(in_peers: u32, out_peers: u32, priority_only: bool) -> Self {
		PeersState {
			nodes: HashMap::new(),
			num_in: 0,
			num_out: 0,
			max_in: in_peers,
			max_out: out_peers,
			priority_nodes: HashMap::new(),
			priority_only,
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

	/// Returns the first priority peer that we are not connected to.
	///
	/// If multiple nodes are prioritized, which one is returned is unspecified.
	pub fn priority_not_connected_peer(&mut self) -> Option<NotConnectedPeer> {
		let id = self.priority_nodes.values()
			.flatten()
			.find(|&id| self.nodes.get(id).map_or(false, |node| !node.connection_state.is_connected()))
			.cloned();
		id.map(move |id| NotConnectedPeer {
			state: self,
			peer_id: Cow::Owned(id),
		})
	}

	/// Returns the first priority peer that we are not connected to.
	///
	/// If multiple nodes are prioritized, which one is returned is unspecified.
	pub fn priority_not_connected_peer_from_group(&mut self, group_id: &str) -> Option<NotConnectedPeer> {
		let id = self.priority_nodes.get(group_id)
			.and_then(|group| group.iter()
				.find(|&id| self.nodes.get(id).map_or(false, |node| !node.connection_state.is_connected()))
				.cloned());
		id.map(move |id| NotConnectedPeer {
			state: self,
			peer_id: Cow::Owned(id),
		})
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

	fn disconnect(&mut self, peer_id: &PeerId) {
		let is_priority = self.is_priority(peer_id);
		if let Some(mut node) = self.nodes.get_mut(peer_id) {
			if !is_priority {
				match node.connection_state {
					ConnectionState::In => self.num_in -= 1,
					ConnectionState::Out => self.num_out -= 1,
					ConnectionState::NotConnected { .. } =>
						debug_assert!(false, "State inconsistency: disconnecting a disconnected node")
				}
			}
			node.connection_state = ConnectionState::NotConnected {
				last_connected: Instant::now(),
			};
		} else {
			warn!(target: "peerset", "Attempting to disconnect unknown peer {}", peer_id);
		}
	}

	/// Sets the peer as connected with an outgoing connection.
	fn try_outgoing(&mut self, peer_id: &PeerId) -> bool {
		let is_priority = self.is_priority(peer_id);

		// We are only accepting connections from priority nodes.
		if !is_priority && self.priority_only {
			return false;
		}

		// Note that it is possible for num_out to be strictly superior to the max, in case we were
		// connected to reserved node then marked them as not reserved.
		if self.num_out >= self.max_out && !is_priority {
			return false;
		}

		if let Some(mut peer) = self.nodes.get_mut(peer_id) {
			peer.connection_state = ConnectionState::Out;
			if !is_priority {
				self.num_out += 1;
			}
			return true;
		}
		false
	}

	/// Tries to accept the peer as an incoming connection.
	///
	/// If there are enough slots available, switches the node to "connected" and returns `true`. If
	/// the slots are full, the node stays "not connected" and we return `false`.
	///
	/// Note that reserved nodes don't count towards the number of slots.
	fn try_accept_incoming(&mut self, peer_id: &PeerId) -> bool {
		let is_priority = self.is_priority(peer_id);

		// We are only accepting connections from priority nodes.
		if !is_priority && self.priority_only {
			return false;
		}

		// Note that it is possible for num_in to be strictly superior to the max, in case we were
		// connected to reserved node then marked them as not reserved.
		if self.num_in >= self.max_in && !is_priority {
			return false;
		}
		if let Some(mut peer) = self.nodes.get_mut(peer_id) {
			peer.connection_state = ConnectionState::In;
			if !is_priority {
				self.num_in += 1;
			}
			return true;
		}
		false
	}

	/// Sets priority group
	pub fn set_priority_group(&mut self, group_id: &str, peers: HashSet<PeerId>) {
		// update slot counters
		let all_other_groups: HashSet<_> = self.priority_nodes
			.iter()
			.filter(|(g, _)| *g != group_id)
			.flat_map(|(_, id)| id.clone())
			.collect();
		let existing_group = self.priority_nodes.remove(group_id).unwrap_or_default();
		for id in existing_group {
			// update slots for nodes that are no longer priority
			if !all_other_groups.contains(&id) {
				if let Some(peer) = self.nodes.get_mut(&id) {
					match peer.connection_state {
						ConnectionState::In => self.num_in += 1,
						ConnectionState::Out => self.num_out += 1,
						ConnectionState::NotConnected { .. } => {},
					}
				}
			}
		}

		for id in &peers {
			// update slots for nodes that become priority
			if !all_other_groups.contains(id) {
				let peer = self.nodes.entry(id.clone()).or_default();
				match peer.connection_state {
					ConnectionState::In => self.num_in -= 1,
					ConnectionState::Out => self.num_out -= 1,
					ConnectionState::NotConnected { .. } => {},
				}
			}
		}
		self.priority_nodes.insert(group_id.into(), peers);
	}

	/// Add a peer to a priority group.
	pub fn add_to_priority_group(&mut self, group_id: &str, peer_id: PeerId) {
		let mut peers = self.priority_nodes.get(group_id).cloned().unwrap_or_default();
		peers.insert(peer_id);
		self.set_priority_group(group_id, peers);
	}

	/// Remove a peer from a priority group.
	pub fn remove_from_priority_group(&mut self, group_id: &str, peer_id: &PeerId) {
		let mut peers = self.priority_nodes.get(group_id).cloned().unwrap_or_default();
		peers.remove(peer_id);
		self.set_priority_group(group_id, peers);
	}

	/// Get priority group content.
	pub fn get_priority_group(&self, group_id: &str) -> Option<HashSet<PeerId>> {
		self.priority_nodes.get(group_id).cloned()
	}

	/// Set whether to only allow connections to/from peers in a priority group.
	/// Calling this method does not affect any existing connection, e.g.
	/// enabling priority only will not disconnect from any non-priority peers
	/// we are already connected to, only future incoming/outgoing connection
	/// attempts will be affected.
	pub fn set_priority_only(&mut self, priority: bool) {
		self.priority_only = priority;
	}

	/// Check that node is any priority group.
	fn is_priority(&self, peer_id: &PeerId) -> bool {
		self.priority_nodes.iter().any(|(_, group)| group.contains(peer_id))
	}

	/// Returns the reputation value of the node.
	fn reputation(&self, peer_id: &PeerId) -> i32 {
		self.nodes.get(peer_id).map_or(0, |p| p.reputation)
	}

	/// Sets the reputation of the peer.
	fn set_reputation(&mut self, peer_id: &PeerId, value: i32) {
		let node = self.nodes
			.entry(peer_id.clone())
			.or_default();
		node.reputation = value;
	}

	/// Performs an arithmetic addition on the reputation score of that peer.
	///
	/// In case of overflow, the value will be capped.
	/// If the peer is unknown to us, we insert it and consider that it has a reputation of 0.
	fn add_reputation(&mut self, peer_id: &PeerId, modifier: i32) {
		let node = self.nodes
			.entry(peer_id.clone())
			.or_default();
		node.reputation = node.reputation.saturating_add(modifier);
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
		self.state.disconnect(&self.peer_id);
		NotConnectedPeer {
			state: self.state,
			peer_id: self.peer_id,
		}
	}

	/// Returns the reputation value of the node.
	pub fn reputation(&self) -> i32 {
		self.state.reputation(&self.peer_id)
	}

	/// Sets the reputation of the peer.
	pub fn set_reputation(&mut self, value: i32) {
		self.state.set_reputation(&self.peer_id, value)
	}

	/// Performs an arithmetic addition on the reputation score of that peer.
	///
	/// In case of overflow, the value will be capped.
	pub fn add_reputation(&mut self, modifier: i32) {
		self.state.add_reputation(&self.peer_id, modifier)
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
	/// Note that priority nodes don't count towards the number of slots.
	pub fn try_outgoing(self) -> Result<ConnectedPeer<'a>, NotConnectedPeer<'a>> {
		if self.state.try_outgoing(&self.peer_id) {
			Ok(ConnectedPeer {
				state: self.state,
				peer_id: self.peer_id,
			})
		} else {
			Err(self)
		}
	}

	/// Tries to accept the peer as an incoming connection.
	///
	/// If there are enough slots available, switches the node to "connected" and returns `Ok`. If
	/// the slots are full, the node stays "not connected" and we return `Err`.
	///
	/// Note that priority nodes don't count towards the number of slots.
	pub fn try_accept_incoming(self) -> Result<ConnectedPeer<'a>, NotConnectedPeer<'a>> {
		if self.state.try_accept_incoming(&self.peer_id) {
			Ok(ConnectedPeer {
				state: self.state,
				peer_id: self.peer_id,
			})
		} else {
			Err(self)
		}
	}

	/// Returns the reputation value of the node.
	pub fn reputation(&self) -> i32 {
		self.state.reputation(&self.peer_id)
	}

	/// Sets the reputation of the peer.
	pub fn set_reputation(&mut self, value: i32) {
		self.state.set_reputation(&self.peer_id, value)
	}

	/// Performs an arithmetic addition on the reputation score of that peer.
	///
	/// In case of overflow, the value will be capped.
	/// If the peer is unknown to us, we insert it and consider that it has a reputation of 0.
	pub fn add_reputation(&mut self, modifier: i32) {
		self.state.add_reputation(&self.peer_id, modifier)
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
		let mut peers_state = PeersState::new(1, 1, false);
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
	fn priority_node_doesnt_use_slot() {
		let mut peers_state = PeersState::new(1, 1, false);
		let id1 = PeerId::random();
		let id2 = PeerId::random();

		peers_state.set_priority_group("test", vec![id1.clone()].into_iter().collect());
		if let Peer::NotConnected(p) = peers_state.peer(&id1) {
			assert!(p.try_accept_incoming().is_ok());
		} else { panic!() }

		if let Peer::Unknown(e) = peers_state.peer(&id2) {
			assert!(e.discover().try_accept_incoming().is_ok());
		} else { panic!() }
	}

	#[test]
	fn disconnecting_frees_slot() {
		let mut peers_state = PeersState::new(1, 1, false);
		let id1 = PeerId::random();
		let id2 = PeerId::random();

		assert!(peers_state.peer(&id1).into_unknown().unwrap().discover().try_accept_incoming().is_ok());
		assert!(peers_state.peer(&id2).into_unknown().unwrap().discover().try_accept_incoming().is_err());
		peers_state.peer(&id1).into_connected().unwrap().disconnect();
		assert!(peers_state.peer(&id2).into_not_connected().unwrap().try_accept_incoming().is_ok());
	}

	#[test]
	fn priority_not_connected_peer() {
		let mut peers_state = PeersState::new(25, 25, false);
		let id1 = PeerId::random();
		let id2 = PeerId::random();

		assert!(peers_state.priority_not_connected_peer().is_none());
		peers_state.peer(&id1).into_unknown().unwrap().discover();
		peers_state.peer(&id2).into_unknown().unwrap().discover();

		assert!(peers_state.priority_not_connected_peer().is_none());
		peers_state.set_priority_group("test", vec![id1.clone()].into_iter().collect());
		assert!(peers_state.priority_not_connected_peer().is_some());
		peers_state.set_priority_group("test", vec![id2.clone(), id2.clone()].into_iter().collect());
		assert!(peers_state.priority_not_connected_peer().is_some());
		peers_state.set_priority_group("test", vec![].into_iter().collect());
		assert!(peers_state.priority_not_connected_peer().is_none());
	}

	#[test]
	fn highest_not_connected_peer() {
		let mut peers_state = PeersState::new(25, 25, false);
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
	fn disconnect_priority_doesnt_panic() {
		let mut peers_state = PeersState::new(1, 1, false);
		let id = PeerId::random();
		peers_state.set_priority_group("test", vec![id.clone()].into_iter().collect());
		let peer = peers_state.peer(&id).into_not_connected().unwrap().try_outgoing().unwrap();
		peer.disconnect();
	}

	#[test]
	fn multiple_priority_groups_slot_count() {
		let mut peers_state = PeersState::new(1, 1, false);
		let id = PeerId::random();

		if let Peer::Unknown(p) = peers_state.peer(&id) {
			assert!(p.discover().try_accept_incoming().is_ok());
		} else { panic!() }

		assert_eq!(peers_state.num_in, 1);
		peers_state.set_priority_group("test1", vec![id.clone()].into_iter().collect());
		assert_eq!(peers_state.num_in, 0);
		peers_state.set_priority_group("test2", vec![id.clone()].into_iter().collect());
		assert_eq!(peers_state.num_in, 0);
		peers_state.set_priority_group("test1", vec![].into_iter().collect());
		assert_eq!(peers_state.num_in, 0);
		peers_state.set_priority_group("test2", vec![].into_iter().collect());
		assert_eq!(peers_state.num_in, 1);
	}

	#[test]
	fn priority_only_mode_ignores_drops_unknown_nodes() {
		// test whether connection to/from given peer is allowed
		let test_connection = |peers_state: &mut PeersState, id| {
			if let Peer::Unknown(p) = peers_state.peer(id) {
				p.discover();
			}

			let incoming = if let Peer::NotConnected(p) = peers_state.peer(id) {
				p.try_accept_incoming().is_ok()
			} else {
				panic!()
			};

			if incoming {
				peers_state.peer(id).into_connected().map(|p| p.disconnect());
			}

			let outgoing = if let Peer::NotConnected(p) = peers_state.peer(id) {
				p.try_outgoing().is_ok()
			} else {
				panic!()
			};

			if outgoing {
				peers_state.peer(id).into_connected().map(|p| p.disconnect());
			}

			incoming || outgoing
		};

		let mut peers_state = PeersState::new(1, 1, true);
		let id = PeerId::random();

		// this is an unknown peer and our peer state is set to only allow
		// priority peers so any connection attempt should be denied.
		assert!(!test_connection(&mut peers_state, &id));

		// disabling priority only mode should allow the connection to go
		// through.
		peers_state.set_priority_only(false);
		assert!(test_connection(&mut peers_state, &id));

		// re-enabling it we should again deny connections from the peer.
		peers_state.set_priority_only(true);
		assert!(!test_connection(&mut peers_state, &id));

		// but if we add the peer to a priority group it should be accepted.
		peers_state.set_priority_group("TEST_GROUP", vec![id.clone()].into_iter().collect());
		assert!(test_connection(&mut peers_state, &id));

		// and removing it will cause the connection to once again be denied.
		peers_state.remove_from_priority_group("TEST_GROUP", &id);
		assert!(!test_connection(&mut peers_state, &id));
	}
}
