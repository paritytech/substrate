// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

/// 2nd level prefix for the length of list of set items.
const LIST_LEN_KEY_PREFIX: &'static [u8] = b":list:len";
/// 2nd level prefix for the items of list of set items.
const LIST_ITEM_KEY_PREFIX: &'static [u8] = b":list:item";
/// 2nd level prefix for the map of set items.
const MAP_ITEM_PREFIX: &'static [u8] = b":map:";

/// Keys set storage. Should write and read raw values (without adding/stripping the prefix).
pub trait Storage {
	/// Read `key` from the storage.
	fn read(&self, key: &[u8]) -> Option<Vec<u8>>;
	/// Set value under `key` to the storage.
	fn set(&mut self, key: &[u8], value: &[u8]);
	/// Clear value under `key`.
	fn clear(&mut self, key: &[u8]);
}

/// A set of keys. Holds unique set of storage keys.
/// Allows to enumerate + optionally remove filtered keys (Vec::retain sematics).
pub struct Set<'a, S: 'a> {
	/// Prefix for this map.
	prefix: &'a [u8],
	/// Set storage
	storage: &'a mut S,
}

impl<'a, S: 'a + Storage> Set<'a, S> {
	/// Initialize with given prefix.
	pub fn new(prefix: &'a [u8], storage: &'a mut S) -> Self {
		Set { prefix, storage }
	}

	/// Insert item into the set.
	pub fn insert(&mut self, item: &[u8]) {
		// check if value is already in the set
		let map_item_key = compose_key3(self.prefix, MAP_ITEM_PREFIX, item);
		match self.storage.read(&map_item_key) {
			Some(_) => return,
			None => self.storage.set(&map_item_key, &[1]),
		}

		// increase list length
		let list_len_key = compose_key2(self.prefix, LIST_LEN_KEY_PREFIX);
		let list_len: u32 = self.storage.read(&list_len_key)
			.and_then(|len| Decode::decode(&mut &len[..]))
			.unwrap_or(0);
		self.storage.set(&list_len_key, &(list_len + 1).encode());

		// set item at list length
		let list_item_key = compose_key3(self.prefix, LIST_ITEM_KEY_PREFIX, &list_len.encode());
		self.storage.set(&list_item_key, item);
	}

	/// Retains only the elements specified by the predicate, which takes key, prefix and value.
	#[allow(dead_code)] // part of the Set, but used only by runtime => allow dead code to keep it together
	pub fn retain<F: FnMut(&mut S, &[u8]) -> bool>(&mut self, mut f: F) {
		// read list length
		let list_len_key = compose_key2(self.prefix, LIST_LEN_KEY_PREFIX);
		let mut list_len: u32 = self.storage.read(&list_len_key)
			.and_then(|len| Decode::decode(&mut &len[..]))
			.unwrap_or(0);

		// for each list item: run f and remove item if required
		let mut idx = 0u32;
		while idx < list_len {
			let list_item_key = compose_key3(self.prefix, LIST_ITEM_KEY_PREFIX, &idx.encode());
			let list_item = self.storage.read(&list_item_key)
				.expect("idx < list_len; list items from 0 to list_len should exist; qed");
			if f(self.storage, &list_item) {
				idx += 1;
				continue;
			}

			// swap_remove item from the list
			if idx != list_len - 1 {
				let last_list_item_key = compose_key3(self.prefix, LIST_ITEM_KEY_PREFIX, &(list_len - 1).encode());
				let last_list_item = self.storage.read(&last_list_item_key)
					.expect("list_len - 1 < list_len; list items from 0 to list_len should exist; qed");
				self.storage.set(&list_item_key, &last_list_item)
			}

			// decrease list length
			list_len -= 1;

			// clear entry for item in the map
			let map_item_key = compose_key3(self.prefix, MAP_ITEM_PREFIX, &list_item);
			self.storage.clear(&map_item_key);
		}

		self.storage.set(&list_len_key, &list_len.encode());
	}
}

/// Compose key of the prefix and the key itself.
fn compose_key2(prefix: &[u8], key: &[u8]) -> Vec<u8> {
	let mut prefixed_key = prefix.to_vec();
	prefixed_key.extend(key);
	prefixed_key
}

/// Get composite key.
fn compose_key3(prefix1: &[u8], prefix2: &[u8], key: &[u8]) -> Vec<u8> {
	let mut prefixed_key = prefix1.to_vec();
	prefixed_key.extend(prefix2);
	prefixed_key.extend(key);
	prefixed_key
}

// This file is compiled by both susbtrate && runtime => to avoid duplicate tests execution:
// see tests in prefix.rs
