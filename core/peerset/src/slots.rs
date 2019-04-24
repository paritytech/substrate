// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
use std::mem;
use libp2p::PeerId;
use linked_hash_map::LinkedHashMap;

/// Describes the nature of connection with a given peer.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum SlotType {
	/// Reserved peer is a peer we should always stay connected to.
	Reserved,
	/// Common peer is a type of peer that we stay connected to only if it's
	/// useful for us.
	Common,
}

/// Descibes the result of `add_peer` action.
pub enum SlotState {
	/// Returned when `add_peer` successfully adds a peer to the slot.
	Added(PeerId),
	/// Returned we already have a connection to a given peer, but it is upgraded from
	/// `Common` to `Reserved`.
	Upgraded(PeerId),
	/// Returned when we should removed a common peer to make space for a reserved peer.
	Swaped {
		/// Peer we should disconnect from.
		removed: PeerId,
		/// Peer we should connect to.
		added: PeerId,
	},
	/// Error returned when we are already connected to this peer.
	AlreadyConnected(PeerId),
	/// Error returned when max number of connections has been already established.
	MaxConnections(PeerId),
}

/// Contains all information about group of slots.
#[derive(Debug)]
pub struct Slots {
	max_slots: usize,
	/// Nodes and their type. We use `LinkedHashMap` to make this data structure more predictable
	slots: LinkedHashMap<PeerId, SlotType>,
}

impl Slots {
	/// Creates a group of slots with a limited size.
	pub fn new(max_slots: u32) -> Self {
		let max_slots = max_slots as usize;
		Slots {
			max_slots,
			slots: LinkedHashMap::with_capacity(max_slots),
		}
	}

	/// Returns true if one of the slots contains given peer.
	pub fn contains(&self, peer_id: &PeerId) -> bool {
		self.slots.contains_key(peer_id)
	}

	/// Tries to find a slot for a given peer and returns `SlotState`.
	pub fn add_peer(&mut self, peer_id: PeerId, slot_type: SlotType) -> SlotState {
		if let Some(st) = self.slots.get_mut(&peer_id) {
			if *st == SlotType::Common && slot_type == SlotType::Reserved {
				*st = SlotType::Reserved;
				return SlotState::Upgraded(peer_id);
			} else {
				return SlotState::AlreadyConnected(peer_id);
			}
		}

		if self.slots.len() == self.max_slots {
			if let SlotType::Reserved = slot_type {
				// if we are trying to insert a reserved peer, but we all of our slots are full,
				// we need to remove one of the existing common connections
				let to_remove = self.slots.iter()
					.find(|(_, &slot_type)| slot_type == SlotType::Common)
					.map(|(to_remove, _)| to_remove)
					.cloned();

				if let Some(to_remove) = to_remove {
					self.slots.remove(&to_remove);
					self.slots.insert(peer_id.clone(), slot_type);

					return SlotState::Swaped {
						removed: to_remove,
						added: peer_id,
					};
				}
			}
			return SlotState::MaxConnections(peer_id);
		}

		self.slots.insert(peer_id.clone(), slot_type);
		SlotState::Added(peer_id)
	}

	pub fn clear_common_slots(&mut self) -> Vec<PeerId> {
		let slots = mem::replace(&mut self.slots, LinkedHashMap::with_capacity(self.max_slots));
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

	pub fn clear_slot(&mut self, peer_id: &PeerId) -> bool {
		self.slots.remove(peer_id).is_some()
	}

	pub fn is_connected_and_reserved(&self, peer_id: &PeerId) -> bool {
		self.slots.get(peer_id)
			.map(|slot_type| *slot_type == SlotType::Reserved)
			.unwrap_or_else(|| false)
	}
}
