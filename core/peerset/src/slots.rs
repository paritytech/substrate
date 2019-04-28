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

use std::{borrow::Cow, fmt, mem};
use libp2p::PeerId;
use linked_hash_map::LinkedHashMap;
use serde_json::json;

/// Describes the nature of connection with a given peer.
#[derive(Debug, PartialEq, Clone, Copy)]
pub enum SlotType {
	/// Reserved peer is a peer we should always stay connected to.
	Reserved,
	/// Common peer is a type of peer that we stay connected to only if it's
	/// useful for us.
	Common,
}

/// Descibes the result of the `insert` method.
#[must_use]
pub enum SlotState<'a> {
	/// Returned when `insert` successfully adds a peer to the slot.
	Added(OccupiedPeerMut<'a>),

	/// Returned when we should removed a common peer to make space for a reserved peer.
	Swaped {
		/// Peer was removed from the list.
		removed: PeerId,
		/// Peer was added to the list.
		added: OccupiedPeerMut<'a>,
	},

	/// Error returned when list is full and no more peers can be added.
	MaxCapacity(VacantPeerMut<'a>),
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

	/// Returns an object giving access to an entry in the `Slots`.
	///
	/// > **Note**: This API is similar to the `entry()` API of the standard `HashMap` container.
	pub fn peer_mut<'a>(&'a mut self, peer_id: &'a PeerId) -> PeerMut<'a> {
		if self.common.contains_key(peer_id) {
			PeerMut::Occupied(OccupiedPeerMut {
				container: self,
				peer_id: Cow::Borrowed(peer_id),
				reserved: false,
			})

		} else if self.reserved.contains_key(peer_id) {
			PeerMut::Occupied(OccupiedPeerMut {
				container: self,
				peer_id: Cow::Borrowed(peer_id),
				reserved: true,
			})

		} else {
			PeerMut::Vacant(VacantPeerMut {
				container: self,
				peer_id: Cow::Borrowed(peer_id),
			})
		}
	}

	/// Returns true if one of the slots contains given peer.
	pub fn contains(&self, peer_id: &PeerId) -> bool {
		self.common.contains_key(peer_id) || self.reserved.contains_key(peer_id)
	}

	/// Returns the oldest reserved peer. If none exists and `reserved_only = false` pops a common peer.
	pub fn most_important_peer(&mut self, reserved_only: bool) -> Option<OccupiedPeerMut> {
		if let Some((peer_id, _)) = self.reserved.front() {
			let peer_id = peer_id.clone();
			return Some(OccupiedPeerMut {
				container: self,
				peer_id: Cow::Owned(peer_id),
				reserved: true,
			});
		}

		if reserved_only {
			return None;
		}

		if let Some((peer_id, _)) = self.common.front() {
			let peer_id = peer_id.clone();
			return Some(OccupiedPeerMut {
				container: self,
				peer_id: Cow::Owned(peer_id),
				reserved: false,
			});
		}

		None
	}

	/// Removes all common peers from the list and returns an iterator over them.
	pub fn clear_common_slots(&mut self) -> impl Iterator<Item = PeerId> {
		let slots = mem::replace(&mut self.common, LinkedHashMap::new());
		slots.into_iter().map(|(peer_id, _)| peer_id)
	}

	/// Produces a JSON object containing the state of slots, for debugging purposes.
	pub fn debug_info(&self) -> serde_json::Value {
		json!({
			"max_slots": self.max_slots,
			"reserved": self.reserved.keys().map(|peer_id| peer_id.to_base58()).collect::<Vec<_>>(),
			"common": self.common.keys().map(|peer_id| peer_id.to_base58()).collect::<Vec<_>>()
		})
	}
}

/// Represents an access to a `PeerId` that is either in the list or not.
pub enum PeerMut<'a> {
	/// `PeerId` is in the `Slots`.
	Occupied(OccupiedPeerMut<'a>),
	/// `PeerId` is not in the `Slots`.
	Vacant(VacantPeerMut<'a>),
}

impl<'a> PeerMut<'a> {
	/// If the variant is `Vacant`, returns `Some`, otherwise `None`.
	// This method is only used in tests, but feel free to remove the `#[cfg(test)]` if you need it.
	#[cfg(test)]
	pub fn into_vacant(self) -> Option<VacantPeerMut<'a>> {
		match self {
			PeerMut::Occupied(_) => None,
			PeerMut::Vacant(p) => Some(p),
		}
	}
}

/// Gives access to an existing entry in the `Slots`.
pub struct OccupiedPeerMut<'a> {
	container: &'a mut Slots,
	peer_id: Cow<'a, PeerId>,
	reserved: bool,
}

impl<'a> OccupiedPeerMut<'a> {
	/// Returns the `PeerId` that was passed to the `peer_mut` method.
	pub fn peer_id(&self) -> &PeerId {
		&self.peer_id
	}

	/// Returns true if the peer is reserved.
	pub fn is_reserved(&self) -> bool {
		self.reserved
	}

	/// Returns the type of slot of this entry.
	pub fn slot_type(&self) -> SlotType {
		if self.reserved {
			SlotType::Reserved
		} else {
			SlotType::Common
		}
	}

	/// Marks the peer as a reserved one. Has no effect if it was already reserved.
	pub fn mark_reserved(&mut self) {
		if self.reserved {
			return;
		}

		let was_in = self.container.common.remove(&self.peer_id);
		debug_assert!(was_in.is_some());
		self.container.reserved.insert(self.peer_id.as_ref().clone(), ());
	}

	/// Marks given peer as not reserved one.
	pub fn mark_not_reserved(&mut self) {
		if !self.reserved {
			return;
		}

		let was_in = self.container.reserved.remove(&self.peer_id);
		debug_assert!(was_in.is_some());
		self.container.common.insert(self.peer_id.as_ref().clone(), ());
	}

	/// Removes the peer from the list
	pub fn remove(self) -> VacantPeerMut<'a> {
		if self.reserved {
			let was_in = self.container.reserved.remove(&self.peer_id);
			debug_assert!(was_in.is_some());
		} else {
			let was_in = self.container.common.remove(&self.peer_id);
			debug_assert!(was_in.is_some());
		}

		VacantPeerMut {
			container: self.container,
			peer_id: self.peer_id,
		}
	}
}

/// Gives access to a vacant entry in the `Slots`.
pub struct VacantPeerMut<'a> {
	container: &'a mut Slots,
	peer_id: Cow<'a, PeerId>,
}

impl<'a> VacantPeerMut<'a> {
	/// Tries to find a slot for a given peer and returns `SlotState`.
	///
	/// - If there is no slot for a reserved peer, we try to drop one common peer
	/// and it a new reserved one in it's place, function returns `SlotState::Swaped`.
	/// - If there is no place for a peer, function returns `SlotState::MaxCapacity`.
	/// - If the peer was simply added, `SlotState::Added` is returned.
	///
	pub fn insert(self, slot_type: SlotType) -> SlotState<'a> {
		if self.container.max_slots == (self.container.common.len() + self.container.reserved.len()) {
			if let SlotType::Reserved = slot_type {
				if let Some((to_remove, _)) = self.container.common.pop_front() {
					self.container.reserved.insert(self.peer_id.as_ref().clone(), ());
					return SlotState::Swaped {
						removed: to_remove,
						added: OccupiedPeerMut {
							container: self.container,
							peer_id: self.peer_id,
							reserved: true,
						},
					};
				}
			}

			return SlotState::MaxCapacity(self);
		}

		match slot_type {
			SlotType::Common => self.container.common.insert(self.peer_id.as_ref().clone(), ()),
			SlotType::Reserved => self.container.reserved.insert(self.peer_id.as_ref().clone(), ()),
		};

		SlotState::Added(OccupiedPeerMut {
			container: self.container,
			peer_id: self.peer_id,
			reserved: match slot_type {
				SlotType::Common => false,
				SlotType::Reserved => true,
			},
		})
	}
}

#[cfg(test)]
mod tests {
	use libp2p::PeerId;
	use serde_json::json;
	use super::{Slots, SlotType};

	#[test]
	fn test_slots_debug_info() {
		let reserved_peer = PeerId::random();
		let reserved_peer2 = PeerId::random();
		let common_peer = PeerId::random();
		let mut slots = Slots::new(10);

		let _ = slots.peer_mut(&reserved_peer).into_vacant().unwrap().insert(SlotType::Reserved);
		let _ = slots.peer_mut(&reserved_peer2).into_vacant().unwrap().insert(SlotType::Reserved);
		let _ = slots.peer_mut(&common_peer).into_vacant().unwrap().insert(SlotType::Common);

		let expected = json!({
			"max_slots": 10,
			"reserved": vec![reserved_peer.to_base58(), reserved_peer2.to_base58()],
			"common": vec![common_peer.to_base58()],
		});

		assert_eq!(expected, slots.debug_info());
	}
}
