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
use std::{borrow::Cow, collections::HashMap};

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

	/// Number of non-reserved nodes for which the `ConnectionState` is `In`.
	num_in: u32,

	/// Number of non-reserved nodes for which the `ConnectionState` is `In`.
	num_out: u32,

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
			num_in: 0,
			num_out: 0,
			max_in: in_peers,
			max_out: out_peers,
		}
	}

	/// Returns an object that grants access to the state of a peer.
	pub fn peer<'a>(&'a mut self, peer_id: &'a PeerId) -> Peer<'a> {
		// Note: the Rust borrow checker still has some issues. In particular, we can't put this
		// block as an `else` below (as the obvious solution would be here), or it will complain
		// that we borrow `self` while it is already borrowed.
		if !self.nodes.contains_key(peer_id) {
			return Peer::Unknown(UnknownPeer {
				parent: self,
				peer_id: Cow::Borrowed(peer_id),
			});
		}

		let state = self.nodes.get_mut(peer_id)
			.expect("We check that the value is present right above; QED");

		if state.connection_state.is_connected() {
			Peer::Connected(ConnectedPeer {
				state,
				peer_id: Cow::Borrowed(peer_id),
				num_in: &mut self.num_in,
				num_out: &mut self.num_out,
				max_in: self.max_in,
				max_out: self.max_out,
			})
		} else {
			Peer::NotConnected(NotConnectedPeer {
				state,
				peer_id: Cow::Borrowed(peer_id),
				num_in: &mut self.num_in,
				num_out: &mut self.num_out,
				max_in: self.max_in,
				max_out: self.max_out,
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
		let outcome = self.nodes.iter_mut()
			.find(|(_, &mut Node { connection_state, reserved, .. })| {
				reserved && !connection_state.is_connected()
			})
			.map(|(peer_id, node)| (peer_id.clone(), node));

		if let Some((peer_id, state)) = outcome {
			Some(NotConnectedPeer {
				state,
				peer_id: Cow::Owned(peer_id),
				num_in: &mut self.num_in,
				num_out: &mut self.num_out,
				max_in: self.max_in,
				max_out: self.max_out,
			})
		} else {
			None
		}
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
			.map(|(peer_id, state)| (peer_id.clone(), state));

		if let Some((peer_id, state)) = outcome {
			Some(NotConnectedPeer {
				state,
				peer_id: Cow::Owned(peer_id),
				num_in: &mut self.num_in,
				num_out: &mut self.num_out,
				max_in: self.max_in,
				max_out: self.max_out,
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
	state: &'a mut Node,
	peer_id: Cow<'a, PeerId>,
	num_in: &'a mut u32,
	num_out: &'a mut u32,
	max_in: u32,
	max_out: u32,
}

impl<'a> ConnectedPeer<'a> {
	/// Destroys this `ConnectedPeer` and returns the `PeerId` inside of it.
	pub fn into_peer_id(self) -> PeerId {
		self.peer_id.into_owned()
	}

	/// Switches the peer to "not connected".
	pub fn disconnect(self) -> NotConnectedPeer<'a> {
		let connec_state = &mut self.state.connection_state;

		match *connec_state {
			ConnectionState::In => *self.num_in -= 1,
			ConnectionState::Out => *self.num_out -= 1,
			ConnectionState::NotConnected =>
				debug_assert!(false, "State inconsistency: disconnecting a disconnected node")
		}

		*connec_state = ConnectionState::NotConnected;

		NotConnectedPeer {
			state: self.state,
			peer_id: self.peer_id,
			num_in: self.num_in,
			num_out: self.num_out,
			max_in: self.max_in,
			max_out: self.max_out,
		}
	}

	/// Sets whether or not the node is reserved.
	pub fn set_reserved(&mut self, reserved: bool) {
		if reserved {
			self.state.reserved = true;
			match self.state.connection_state {
				ConnectionState::In => *self.num_in -= 1,
				ConnectionState::Out => *self.num_out -= 1,
				ConnectionState::NotConnected => debug_assert!(false, "State inconsistency: \
					connected node is in fact not connected"),
			}

		} else {
			self.state.reserved = false;
			match self.state.connection_state {
				ConnectionState::In => *self.num_in += 1,
				ConnectionState::Out => *self.num_out += 1,
				ConnectionState::NotConnected => debug_assert!(false, "State inconsistency: \
					connected node is in fact not connected"),
			}
		}
	}

	/// Returns whether or not the node is reserved.
	pub fn is_reserved(&self) -> bool {
		self.state.reserved
	}

	/// Returns the reputation value of the node.
	pub fn reputation(&self) -> i32 {
		self.state.reputation
	}

	/// Sets the reputation of the peer.
	pub fn set_reputation(&mut self, value: i32) {
		self.state.reputation = value;
	}

	/// Performs an arithmetic addition on the reputation score of that peer.
	///
	/// In case of overflow, the value will be capped.
	pub fn add_reputation(&mut self, modifier: i32) {
		let reputation = &mut self.state.reputation;
		*reputation = reputation.saturating_add(modifier);
	}
}

/// A peer that is not connected to us.
pub struct NotConnectedPeer<'a> {
	state: &'a mut Node,
	peer_id: Cow<'a, PeerId>,
	num_in: &'a mut u32,
	num_out: &'a mut u32,
	max_in: u32,
	max_out: u32,
}

impl<'a> NotConnectedPeer<'a> {
	/// Destroys this `NotConnectedPeer` and returns the `PeerId` inside of it.
	#[cfg(test)]	// Feel free to remove this if this function is needed outside of tests
	pub fn into_peer_id(self) -> PeerId {
		self.peer_id.into_owned()
	}

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

		// Note that it is possible for num_out to be strictly superior to the max, in case we were
		// connected to reserved node then marked them as not reserved, or if the user used
		// `force_outgoing`.
		if *self.num_out >= self.max_out {
			return Err(self);
		}

		Ok(self.force_outgoing())
	}

	/// Sets the peer as connected as an outgoing connection.
	pub fn force_outgoing(self) -> ConnectedPeer<'a> {
		let connec_state = &mut self.state.connection_state;
		debug_assert!(!connec_state.is_connected());
		*connec_state = ConnectionState::Out;

		if !self.state.reserved {
			*self.num_out += 1;
		}

		ConnectedPeer {
			state: self.state,
			peer_id: self.peer_id,
			num_in: self.num_in,
			num_out: self.num_out,
			max_in: self.max_in,
			max_out: self.max_out,
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

		// Note that it is possible for num_in to be strictly superior to the max, in case we were
		// connected to reserved node then marked them as not reserved.
		if *self.num_in >= self.max_in {
			return Err(self);
		}

		Ok(self.force_ingoing())
	}

	/// Sets the peer as connected as an ingoing connection.
	pub fn force_ingoing(self) -> ConnectedPeer<'a> {
		let connec_state = &mut self.state.connection_state;
		debug_assert!(!connec_state.is_connected());
		*connec_state = ConnectionState::In;

		if !self.state.reserved {
			*self.num_in += 1;
		}

		ConnectedPeer {
			state: self.state,
			peer_id: self.peer_id,
			num_in: self.num_in,
			num_out: self.num_out,
			max_in: self.max_in,
			max_out: self.max_out,
		}
	}

	/// Sets whether or not the node is reserved.
	pub fn set_reserved(&mut self, reserved: bool) {
		self.state.reserved = reserved;
	}

	/// Returns true if the the node is reserved.
	pub fn is_reserved(&self) -> bool {
		self.state.reserved
	}

	/// Returns the reputation value of the node.
	pub fn reputation(&self) -> i32 {
		self.state.reputation
	}

	/// Sets the reputation of the peer.
	pub fn set_reputation(&mut self, value: i32) {
		self.state.reputation = value;
	}

	/// Performs an arithmetic addition on the reputation score of that peer.
	///
	/// In case of overflow, the value will be capped.
	/// If the peer is unknown to us, we insert it and consider that it has a reputation of 0.
	pub fn add_reputation(&mut self, modifier: i32) {
		let reputation = &mut self.state.reputation;
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

		let state = self.parent.nodes.get_mut(&self.peer_id)
			.expect("We insert that key into the HashMap right above; QED");

		NotConnectedPeer {
			state,
			peer_id: self.peer_id,
			num_in: &mut self.parent.num_in,
			num_out: &mut self.parent.num_out,
			max_in: self.parent.max_in,
			max_out: self.parent.max_out,
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

		assert!(peers_state.peer(&id1).into_unknown().unwrap().discover().try_accept_incoming().is_ok());
		assert!(peers_state.peer(&id2).into_unknown().unwrap().discover().try_accept_incoming().is_err());
		peers_state.peer(&id1).into_connected().unwrap().disconnect();
		assert!(peers_state.peer(&id2).into_not_connected().unwrap().try_accept_incoming().is_ok());
	}

	#[test]
	fn reserved_not_connected_peer() {
		let mut peers_state = PeersState::new(25, 25);
		let id1 = PeerId::random();
		let id2 = PeerId::random();

		assert!(peers_state.reserved_not_connected_peer().is_none());
		peers_state.peer(&id1).into_unknown().unwrap().discover();
		peers_state.peer(&id2).into_unknown().unwrap().discover();

		assert!(peers_state.reserved_not_connected_peer().is_none());
		peers_state.peer(&id1).into_not_connected().unwrap().set_reserved(true);
		assert!(peers_state.reserved_not_connected_peer().is_some());
		peers_state.peer(&id2).into_not_connected().unwrap().set_reserved(true);
		peers_state.peer(&id1).into_not_connected().unwrap().set_reserved(false);
		assert!(peers_state.reserved_not_connected_peer().is_some());
		peers_state.peer(&id2).into_not_connected().unwrap().set_reserved(false);
		assert!(peers_state.reserved_not_connected_peer().is_none());
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
		peers_state.peer(&id2).into_not_connected().unwrap().force_ingoing();
		assert_eq!(peers_state.highest_not_connected_peer().map(|p| p.into_peer_id()), Some(id1.clone()));
		peers_state.peer(&id1).into_not_connected().unwrap().set_reputation(100);
		peers_state.peer(&id2).into_connected().unwrap().disconnect();
		assert_eq!(peers_state.highest_not_connected_peer().map(|p| p.into_peer_id()), Some(id1.clone()));
		peers_state.peer(&id1).into_not_connected().unwrap().set_reputation(-100);
		assert_eq!(peers_state.highest_not_connected_peer().map(|p| p.into_peer_id()), Some(id2.clone()));
	}
}
