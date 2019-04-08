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

use std::{fmt, mem};
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
pub struct Slots {
	/// Maximum number of slots. Total number of reserved and common slots must be always
	/// smaller or equal to `max_slots`.
	max_slots: usize,
	/// Reserved slots.
	reserved: LinkedHashMap<PeerId,()>,
	/// Common slots.
	common: LinkedHashMap<PeerId, ()>,
}

impl fmt::Debug for Slots {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		struct ListFormatter<'a>(&'a LinkedHashMap<PeerId, ()>);

		impl<'a> fmt::Debug for ListFormatter<'a> {
			fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
				f.debug_list().entries(self.0.keys()).finish()
			}
		}

		f.debug_struct("Slots")
			.field("max_slots", &self.max_slots)
			.field("reserved", &ListFormatter(&self.reserved))
			.field("common", &ListFormatter(&self.common))
			.finish()
	}
}

impl Slots {
	/// Creates a group of slots with a limited size.
	pub fn new(max_slots: u32) -> Self {
		let max_slots = max_slots as usize;
		Slots {
			max_slots,
			reserved: LinkedHashMap::new(),
			common: LinkedHashMap::new(),
		}
	}

	/// Returns true if one of the slots contains given peer.
	pub fn contains(&self, peer_id: &PeerId) -> bool {
		self.common.contains_key(peer_id) || self.reserved.contains_key(peer_id)
	}

	/// Tries to find a slot for a given peer and returns `SlotState`.
	pub fn add_peer(&mut self, peer_id: PeerId, slot_type: SlotType) -> SlotState {
		if self.reserved.contains_key(&peer_id) {
			return SlotState::AlreadyConnected(peer_id);
		}

		if self.common.contains_key(&peer_id) {
			if slot_type == SlotType::Reserved {
				self.common.remove(&peer_id);
				self.reserved.insert(peer_id.clone(), ());
				return SlotState::Upgraded(peer_id);
			} else {
				return SlotState::AlreadyConnected(peer_id);
			}
		}

		if self.max_slots == (self.common.len() + self.reserved.len()) {
			if let SlotType::Reserved = slot_type {
				if let Some((to_remove, _)) = self.common.pop_front() {
					self.reserved.insert(peer_id.clone(), ());
					return SlotState::Swaped {
						removed: to_remove,
						added: peer_id,
					};
				}
			}
			return SlotState::MaxConnections(peer_id);
		}

		match slot_type {
			SlotType::Common => self.common.insert(peer_id.clone(), ()),
			SlotType::Reserved => self.reserved.insert(peer_id.clone(), ()),
		};

		SlotState::Added(peer_id)
	}

	/// Pops the oldest peer from the list.
	pub fn pop_peer(&mut self, reserved_only: bool) -> Option<(PeerId, SlotType)> {
		if let Some((peer_id, _)) = self.reserved.pop_front() {
			return Some((peer_id, SlotType::Reserved));
		}

		if reserved_only {
			return None;
		}

		self.common.pop_front()
			.map(|(peer_id, _)| (peer_id, SlotType::Common))
	}

	pub fn clear_common_slots(&mut self) -> impl Iterator<Item = PeerId> {
		let slots = mem::replace(&mut self.common, LinkedHashMap::new());
		slots.into_iter().map(|(peer_id, _)| peer_id)
	}

	pub fn mark_reserved(&mut self, peer_id: &PeerId) {
		if let Some(_) = self.common.remove(peer_id) {
			self.reserved.insert(peer_id.clone(), ());
		}
	}

	pub fn mark_not_reserved(&mut self, peer_id: &PeerId) {
		if let Some(_) = self.reserved.remove(peer_id) {
			self.common.insert(peer_id.clone(), ());
		}
	}

	pub fn remove_peer(&mut self, peer_id: &PeerId) -> bool {
		self.common.remove(peer_id).is_some() || self.reserved.remove(peer_id).is_some()
	}

	pub fn is_reserved(&self, peer_id: &PeerId) -> bool {
		self.reserved.contains_key(peer_id)
	}
}

#[cfg(test)]
mod tests {
	use libp2p::PeerId;
	use super::{Slots, SlotType};

	#[test]
	fn test_slots_debug() {
		let reserved_peer = PeerId::random();
		let reserved_peer2 = PeerId::random();
		let common_peer = PeerId::random();
		let mut slots = Slots::new(10);

		slots.add_peer(reserved_peer.clone(), SlotType::Reserved);
		slots.add_peer(reserved_peer2.clone(), SlotType::Reserved);
		slots.add_peer(common_peer.clone(), SlotType::Common);

		let expected = format!("Slots {{
    max_slots: 10,
    reserved: [
        PeerId(
            {:?}
        ),
        PeerId(
            {:?}
        )
    ],
    common: [
        PeerId(
            {:?}
        )
    ]
}}", reserved_peer.to_base58(), reserved_peer2.to_base58(), common_peer.to_base58());

		let s = format!("{:#?}", slots);
		assert_eq!(expected, s);
	}
}
