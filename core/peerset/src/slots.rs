// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

use std::collections::HashMap;
use std::mem;
use libp2p::PeerId;

/// Describes the nature of connection with a given peer.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum SlotType {
	/// Reserved peer is a peer we should always stay connected to.
	Reserved,
	/// Common peer is a type of peer that we stay connected to only if it's
	/// useful for us.
	Common,
}

/// Descibes why the reason of not being able to add given peer.
pub enum SlotError {
	/// Error returned when we are already connected to this peer.
	AlreadyConnected(PeerId),
	/// Error returned when max number of connections has been already established.
	MaxConnections(PeerId),
	/// Error returned when we should disconnect from a given common peer to make space
	/// for a reserved peer.
	DemandReroute {
		/// Peer we should disconnect from.
		disconnect: PeerId,
		/// Peer we should connect to.
		connect: PeerId,
	}
}

/// Contains all information about group of slots.
#[derive(Debug)]
pub struct Slots {
	max_slots: usize,
	slots: HashMap<PeerId, SlotType>,
}

impl Slots {
	/// Creates a group of slots with a limited size.
	pub fn new(max_slots: u32) -> Self {
		let max_slots = max_slots as usize;
		Slots {
			max_slots,
			slots: HashMap::with_capacity(max_slots),
		}
	}

	/// Returns true if one of the slots contains given peer.
	pub fn contains(&self, peer_id: &PeerId) -> bool {
		self.slots.contains_key(peer_id)
	}

	/// Returns Ok if we successfully connected to a given peer.
	pub fn add_peer(&mut self, peer_id: PeerId, slot_type: SlotType) -> Result<(), SlotError>  {
		if let Some(st) = self.slots.get_mut(&peer_id) {
			if let SlotType::Reserved = slot_type {
				*st = SlotType::Reserved;
			}
			return Err(SlotError::AlreadyConnected(peer_id));
		}

		if self.slots.len() == self.max_slots {
			if let SlotType::Reserved = slot_type {
				if let Some((to_disconnect, _)) = self.slots.iter().find(|(_, &slot_type)| slot_type == SlotType::Common) {
					return Err(SlotError::DemandReroute {
						disconnect: to_disconnect.clone(),
						connect: peer_id,
					});
				}
			}
			return Err(SlotError::MaxConnections(peer_id));
		}

		self.slots.insert(peer_id, slot_type);
		Ok(())
	}

	pub fn clear_common_slots(&mut self) -> Vec<PeerId> {
		let slots = mem::replace(&mut self.slots, HashMap::with_capacity(self.max_slots));
		let mut common_peers = Vec::new();
		for (peer_id, slot_type) in slots {
			match slot_type {
				SlotType::Common => {
					common_peers.push(peer_id);
				},
				SlotType::Reserved => {
					self.slots.insert(peer_id, slot_type);
				},
			}
		}
		common_peers
	}

	pub fn mark_reserved(&mut self, peer_id: &PeerId) {
		if let Some(slot_type) = self.slots.get_mut(peer_id) {
			*slot_type = SlotType::Reserved;
		}
	}

	pub fn mark_not_reserved(&mut self, peer_id: &PeerId) {
		if let Some(slot_type) = self.slots.get_mut(peer_id) {
			*slot_type = SlotType::Common;
		}
	}

	pub fn clear_slot(&mut self, peer_id: &PeerId) {
		self.slots.remove(peer_id);
	}

	pub fn is_reserved(&self, peer_id: &PeerId) -> bool {
		self.slots.get(peer_id)
			.map(|slot_type| *slot_type == SlotType::Reserved)
			.unwrap_or_else(|| false)
	}
}
