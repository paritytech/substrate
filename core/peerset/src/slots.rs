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
	/// Returned when we already have given peer in our list, but it is upgraded from
	/// `Common` to `Reserved`.
	Upgraded(PeerId),
	/// Returned when we should removed a common peer to make space for a reserved peer.
	Swaped {
		/// Peer was removed from the list.
		removed: PeerId,
		/// Peer was added to the list.
		added: PeerId,
	},
	/// Error returned when we are already know about given peer.
	AlreadyExists(PeerId),
	/// Error returned when list is full and no more peers can be added.
	MaxCapacity(PeerId),
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
	///
	/// - If a peer is already inserted into reserved list or inserted or
	/// inserted into common list and readded with the same `SlotType`,
	/// the function returns `SlotState::AlreadyExists`
	/// - If a peer is already inserted common list returns `SlotState::Upgraded`
	/// - If there is no slot for a reserved peer, we try to drop one common peer
	/// and it a new reserved one in it's place, function returns `SlotState::Swaped`
	/// - If there is no place for a peer, function returns `SlotState::MaxCapacity`
	/// - If the peer was simply added, `SlotState::Added` is returned
	pub fn add_peer(&mut self, peer_id: PeerId, slot_type: SlotType) -> SlotState {
		if self.reserved.contains_key(&peer_id) {
			return SlotState::AlreadyExists(peer_id);
		}

		if self.common.contains_key(&peer_id) {
			if slot_type == SlotType::Reserved {
				self.common.remove(&peer_id);
				self.reserved.insert(peer_id.clone(), ());
				return SlotState::Upgraded(peer_id);
			} else {
				return SlotState::AlreadyExists(peer_id);
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
			return SlotState::MaxCapacity(peer_id);
		}

		match slot_type {
			SlotType::Common => self.common.insert(peer_id.clone(), ()),
			SlotType::Reserved => self.reserved.insert(peer_id.clone(), ()),
		};

		SlotState::Added(peer_id)
	}

	/// Pops the oldest reserved peer. If none exists and `reserved_only = false` pops a common peer.
	pub fn pop_most_important_peer(&mut self, reserved_only: bool) -> Option<(PeerId, SlotType)> {
		if let Some((peer_id, _)) = self.reserved.pop_front() {
			return Some((peer_id, SlotType::Reserved));
		}

		if reserved_only {
			return None;
		}

		self.common.pop_front()
			.map(|(peer_id, _)| (peer_id, SlotType::Common))
	}

	/// Removes all common peers from the list and returns an iterator over them.
	pub fn clear_common_slots(&mut self) -> impl Iterator<Item = PeerId> {
		let slots = mem::replace(&mut self.common, LinkedHashMap::new());
		slots.into_iter().map(|(peer_id, _)| peer_id)
	}

	/// Marks given peer as a reserved one.
	pub fn mark_reserved(&mut self, peer_id: &PeerId) {
		if self.common.remove(peer_id).is_some() {
			self.reserved.insert(peer_id.clone(), ());
		}
	}

	/// Marks given peer as not reserved one.
	pub fn mark_not_reserved(&mut self, peer_id: &PeerId) {
		if self.reserved.remove(peer_id).is_some() {
			self.common.insert(peer_id.clone(), ());
		}
	}

	/// Removes a peer from a list and returns true if it existed.
	pub fn remove_peer(&mut self, peer_id: &PeerId) -> bool {
		self.common.remove(peer_id).is_some() || self.reserved.remove(peer_id).is_some()
	}

	/// Returns true if given peer is reserved.
	pub fn is_reserved(&self, peer_id: &PeerId) -> bool {
		self.reserved.contains_key(peer_id)
	}
}
