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

//! Contains the state storage behind the peerset.

use libp2p::PeerId;
use std::{borrow::Cow, collections::HashMap, convert::TryFrom};

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

	/// Maximum allowed number of non-reserved nodes for which the `ConnectionState` is `In`.
	max_in: u32,

	/// Maximum allowed number of non-reserved nodes for which the `ConnectionState` is `Out`.
	max_out: u32,
}

/// State of a single node that we know about.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
struct Node {
	/// Whether we are connected to this node.
	connection_state: ConnectionState,

	/// If true, this node is reserved and should always be connected to.
	reserved: bool,

	/// Reputation value of the node, between `i32::min_value` (we hate that node) and
	/// `i32::max_value` (we love that node).
	reputation: i32,
}

/// Whether we are connected to a node.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum ConnectionState {
	/// We are connected through an ingoing connection.
	In,
	/// We are connected through an outgoing connection.
	Out,
	/// We are not connected to this node.
	NotConnected,
}

impl ConnectionState {
	/// Returns `true` for `In` and `Out`.
	fn is_connected(self) -> bool {
		match self {
			ConnectionState::In => true,
			ConnectionState::Out => true,
			ConnectionState::NotConnected => false,
		}
	}
}

impl PeersState {
	/// Builds a new empty `PeersState`.
	pub fn new(in_peers: u32, out_peers: u32) -> Self {
		PeersState {
			nodes: HashMap::new(),
			max_in: in_peers,
			max_out: out_peers,
		}
	}

	/// Adds `value` to the reputation of all the nodes we are connected to.
	///
	/// In case of overflow, the value of capped.
	pub fn connected_reputation_increase(&mut self, value: i32) {
		for (_, peer_state) in self.nodes.iter_mut() {
			if peer_state.connection_state.is_connected() {
				peer_state.reputation = peer_state.reputation.saturating_add(value);
			}
		}
	}

	/// Returns an object that grants access to the state of a peer.
	pub fn peer<'a>(&'a mut self, peer_id: &'a PeerId) -> Peer<'a> {
		if let Some(node) = self.nodes.get(peer_id) {
			if node.connection_state.is_connected() {
				Peer::Connected(ConnectedPeer {
					parent: self,
					peer_id: Cow::Borrowed(peer_id),
				})
			} else {
				Peer::NotConnected(NotConnectedPeer {
					parent: self,
					peer_id: Cow::Borrowed(peer_id),
				})
			}
		} else {
			Peer::Unknown(UnknownPeer {
				parent: self,
				peer_id: Cow::Borrowed(peer_id),
			})
		}
	}

	/// Returns the list of all the peers we know of.
	// Note: this method could theoretically return a `Peer`, but implementing that
	// isn't simple.
	pub fn peers(&self) -> impl Iterator<Item = &PeerId> {
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

	/// Returns the first reserved peer that we are not connected to.
	///
	/// If multiple nodes are reserved, which one is returned is unspecified.
	pub fn reserved_not_connected_peer(&mut self) -> Option<NotConnectedPeer> {
		let peer_id = self.nodes.iter_mut()
			.find(|(_, &mut Node { connection_state, reserved, .. })| {
				reserved && !connection_state.is_connected()
			})
			.map(|(peer_id, _)| peer_id.clone());

		if let Some(peer_id) = peer_id {
			Some(NotConnectedPeer {
				parent: self,
				peer_id: Cow::Owned(peer_id),
			})
		} else {
			None
		}
	}

	/// Returns the peer with the highest reputation and that we are not connected to.
	///
	/// If multiple nodes have the same reputation, which one is returned is unspecified.
	pub fn highest_not_connected_peer(&mut self) -> Option<NotConnectedPeer> {
		let peer_id = self.nodes
			.iter()
			.filter(|(_, Node { connection_state, .. })| !connection_state.is_connected())
			.fold(None::<(&PeerId, &Node)>, |mut cur_node, to_try| {
				if let Some(cur_node) = cur_node.take() {
					if cur_node.1.reputation >= to_try.1.reputation {
						return Some(cur_node);
					}
				}
				Some(to_try)
			})
			.map(|(peer_id, _)| peer_id.clone());

		if let Some(peer_id) = peer_id {
			Some(NotConnectedPeer {
				parent: self,
				peer_id: Cow::Owned(peer_id),
			})
		} else {
			None
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
}

/// A peer that is connected to us.
pub struct ConnectedPeer<'a> {
	parent: &'a mut PeersState,
	peer_id: Cow<'a, PeerId>,
}

impl<'a> ConnectedPeer<'a> {
	/// Destroys this `ConnectedPeer` and returns the `PeerId` inside of it.
	pub fn into_peer_id(self) -> PeerId {
		self.peer_id.into_owned()
	}

	/// Switches the peer to "not connected".
	pub fn disconnect(self) -> NotConnectedPeer<'a> {
		let connec_state = &mut self.parent.nodes.get_mut(&self.peer_id)
			.expect("We only ever build a ConnectedPeer if the node's in the list; QED")
			.connection_state;
		debug_assert!(connec_state.is_connected());
		*connec_state = ConnectionState::NotConnected;

		NotConnectedPeer {
			parent: self.parent,
			peer_id: self.peer_id,
		}
	}

	/// Sets whether or not the node is reserved.
	pub fn set_reserved(&mut self, reserved: bool) {
		self.parent.nodes.get_mut(&self.peer_id)
			.expect("We only ever build a ConnectedPeer if the node's in the list; QED")
			.reserved = reserved;
	}

	/// Returns the reputation value of the node.
	pub fn reputation(&self) -> i32 {
		self.parent.nodes.get(&self.peer_id)
			.expect("We only ever build a ConnectedPeer if the node's in the list; QED")
			.reputation
	}

	/// Sets the reputation of the peer.
	pub fn set_reputation(&mut self, value: i32) {
		self.parent.nodes.get_mut(&self.peer_id)
			.expect("We only ever build a ConnectedPeer if the node's in the list; QED")
			.reputation = value;
	}

	/// Performs an arithmetic addition on the reputation score of that peer.
	///
	/// In case of overflow, the value will be capped.
	pub fn add_reputation(&mut self, modifier: i32) {
		let reputation = &mut self.parent.nodes.get_mut(&self.peer_id)
			.expect("We only ever build a ConnectedPeer if the node's in the list; QED")
			.reputation;
		*reputation = reputation.saturating_add(modifier);
	}
}

/// A peer that is not connected to us.
pub struct NotConnectedPeer<'a> {
	parent: &'a mut PeersState,
	peer_id: Cow<'a, PeerId>,
}

impl<'a> NotConnectedPeer<'a> {
	/// Tries to set the peer as connected as an outgoing connection.
	///
	/// If there are enough slots available, switches the node to "connected" and returns `Ok`. If
	/// the slots are full, the node stays "not connected" and we return `Err`.
	/// If the node is reserved, this method always succeeds.
	///
	/// Note that reserved nodes don't count towards the number of slots.
	pub fn try_outgoing(self) -> Result<ConnectedPeer<'a>, NotConnectedPeer<'a>> {
		if self.is_reserved() {
			return Ok(self.force_outgoing())
		}

		// Count number of nodes in our "out" slots and that are not reserved.
		let num_out_peers = u32::try_from(self.parent.nodes.values()
			.filter(|p| !p.reserved && p.connection_state == ConnectionState::Out)
			.count())
			.unwrap_or(u32::max_value());

		// Note that it is possible for num_out_peers to be strictly superior to the max, in case
		// we were connected to reserved node then marked them as not reserved, or if the user
		// used `force_outgoing`.
		if num_out_peers >= self.parent.max_out {
			return Err(self);
		}

		Ok(self.force_outgoing())
	}

	/// Sets the peer as connected as an outgoing connection.
	pub fn force_outgoing(self) -> ConnectedPeer<'a> {
		let connec_state = &mut self.parent.nodes.get_mut(&self.peer_id)
			.expect("We only ever build a ConnectedPeer if the node's in the list; QED")
			.connection_state;
		debug_assert!(!connec_state.is_connected());
		*connec_state = ConnectionState::Out;

		ConnectedPeer {
			parent: self.parent,
			peer_id: self.peer_id,
		}
	}

	/// Tries to accept the peer as an incoming connection.
	///
	/// If there are enough slots available, switches the node to "connected" and returns `Ok`. If
	/// the slots are full, the node stays "not connected" and we return `Err`.
	///
	/// Note that reserved nodes don't count towards the number of slots.
	pub fn try_accept_incoming(self) -> Result<ConnectedPeer<'a>, NotConnectedPeer<'a>> {
		if self.is_reserved() {
			return Ok(self.force_ingoing())
		}

		// Count number of nodes in our "in" slots and that are not reserved.
		let num_in_peers = u32::try_from(self.parent.nodes.values()
			.filter(|p| !p.reserved && p.connection_state == ConnectionState::In)
			.count())
			.unwrap_or(u32::max_value());

		// Note that it is possible for num_in_peers to be strictly superior to the max, in case
		// we were connected to reserved node then marked them as not reserved.
		if num_in_peers >= self.parent.max_in {
			return Err(self);
		}

		Ok(self.force_ingoing())
	}

	/// Sets the peer as connected as an ingoing connection.
	pub fn force_ingoing(self) -> ConnectedPeer<'a> {
		let connec_state = &mut self.parent.nodes.get_mut(&self.peer_id)
			.expect("We only ever build a ConnectedPeer if the node's in the list; QED")
			.connection_state;
		debug_assert!(!connec_state.is_connected());
		*connec_state = ConnectionState::In;

		ConnectedPeer {
			parent: self.parent,
			peer_id: self.peer_id,
		}
	}

	/// Returns true if the the node is reserved.
	pub fn is_reserved(&self) -> bool {
		self.parent.nodes.get(&self.peer_id)
			.expect("We only ever build a ConnectedPeer if the node's in the list; QED")
			.reserved
	}

	/// Sets whether or not the node is reserved.
	pub fn set_reserved(&mut self, reserved: bool) {
		self.parent.nodes.get_mut(&self.peer_id)
			.expect("We only ever build a ConnectedPeer if the node's in the list; QED")
			.reserved = reserved;
	}

	/// Returns the reputation value of the node.
	pub fn reputation(&self) -> i32 {
		self.parent.nodes.get(&self.peer_id)
			.expect("We only ever build a ConnectedPeer if the node's in the list; QED")
			.reputation
	}

	/// Performs an arithmetic addition on the reputation score of that peer.
	///
	/// In case of overflow, the value will be capped.
	/// If the peer is unknown to us, we insert it and consider that it has a reputation of 0.
	pub fn add_reputation(&mut self, modifier: i32) {
		let reputation = &mut self.parent.nodes.get_mut(&self.peer_id)
			.expect("We only ever build a ConnectedPeer if the node's in the list; QED")
			.reputation;
		*reputation = reputation.saturating_add(modifier);
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
	/// The node is not reserved and starts with a reputation of 0. You can adjust these default
	/// values using the `NotConnectedPeer` that this method returns.
	pub fn discover(self) -> NotConnectedPeer<'a> {
		self.parent.nodes.insert(self.peer_id.clone().into_owned(), Node {
			connection_state: ConnectionState::NotConnected,
			reputation: 0,
			reserved: false,
		});

		NotConnectedPeer {
			parent: self.parent,
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
	fn reserved_node_doesnt_use_slot() {
		let mut peers_state = PeersState::new(1, 1);
		let id1 = PeerId::random();
		let id2 = PeerId::random();

		if let Peer::Unknown(e) = peers_state.peer(&id1) {
			let mut p = e.discover();
			p.set_reserved(true);
			assert!(p.try_accept_incoming().is_ok());
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

		if let Peer::Unknown(e) = peers_state.peer(&id1) {
			assert!(e.discover().try_accept_incoming().is_ok());
		} else { panic!() }

		if let Peer::Unknown(e) = peers_state.peer(&id2) {
			assert!(e.discover().try_accept_incoming().is_err());
		} else { panic!() }

		peers_state.peer(&id1).into_connected().unwrap().disconnect();

		if let Peer::NotConnected(e) = peers_state.peer(&id2) {
			assert!(e.try_accept_incoming().is_ok());
		}
	}
}
