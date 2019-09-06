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

//! Operation on runtime child storages.
//!
//! This module is a currently only a variant of unhashed with additional `storage_key`.
//! Note that `storage_key` must be unique and strong (strong in the sense of being long enough to
//! avoid collision from a resistant hash function (which unique implies)).
// NOTE: could replace unhashed by having only one kind of storage (root being null storage key (storage_key can become Option<&[u8]>).

use super::{Codec, Decode, Vec};
use primitives::child_trie::ChildTrie;
use primitives::child_trie::ChildTrieReadRef;
use primitives::storage::well_known_keys;
pub use super::unhashed::StorageVec;

/// Method for fetching or initiating a new child trie.
pub fn next_keyspace() -> u128 {
	let key = well_known_keys::CHILD_STORAGE_KEYSPACE_COUNTER;
	// do start at 1 (0 is reserved for top trie)
	let previous = super::unhashed::get(key).unwrap_or(0u128);
	let new = previous + 1;
	super::unhashed::put(key, &new);
	new
}

/// Method for fetching or initiating a new child trie.
pub fn fetch_or_new(
	parent: &[u8],
) -> ChildTrie {
	ChildTrie::fetch_or_new(
		|pk| { child_trie(pk) },
		|ct| {
			let updated = set_child_trie(ct);
			// fetch or new create a new child trie
			// so the child trie creation condition
			// cannot fail at this point.
			debug_assert!(updated);
		},
		parent,
		|| next_keyspace(),
	)
}

/// Fetch a child trie return None if no child trie for
/// this storage key.
pub fn child_trie(storage_key: &[u8]) -> Option<ChildTrie> {
	runtime_io::child_trie(storage_key)
}

/// Update or create an existing child trie.
/// Warning in case of update this function does not allow:
/// - root change
/// Return false and do nothing in those cases.
pub fn set_child_trie(ct: ChildTrie) -> bool {
	runtime_io::set_child_trie(ct)
}

/// Return the value of the item in storage under `key`, or `None` if there is no explicit entry.
pub fn get<T: Codec + Sized>(child_trie: ChildTrieReadRef, key: &[u8]) -> Option<T> {
	runtime_io::child_storage(child_trie.clone(), key).map(|v| {
		Decode::decode(&mut &v[..]).expect("storage is not null, therefore must be a valid type")
	})
}

/// Return the value of the item in storage under `key`, or the type's default if there is no
/// explicit entry.
pub fn get_or_default<T: Codec + Sized + Default>(child_trie: ChildTrieReadRef, key: &[u8]) -> T {
	get(child_trie, key).unwrap_or_else(Default::default)
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry.
pub fn get_or<T: Codec + Sized>(child_trie: ChildTrieReadRef, key: &[u8], default_value: T) -> T {
	get(child_trie, key).unwrap_or(default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry.
pub fn get_or_else<T: Codec + Sized, F: FnOnce() -> T>(
	child_trie: ChildTrieReadRef,
	key: &[u8],
	default_value: F,
) -> T {
	get(child_trie, key).unwrap_or_else(default_value)
}

/// Put `value` in storage under `key`.
pub fn put<T: Codec>(child_trie: &ChildTrie, key: &[u8], value: &T) {
	value.using_encoded(|slice| runtime_io::set_child_storage(child_trie, key, slice));
}

/// Remove `key` from storage, returning its value if it had an explicit entry or `None` otherwise.
pub fn take<T: Codec + Sized>(child_trie: &ChildTrie, key: &[u8]) -> Option<T> {
	let r = get(child_trie.node_ref(), key);
	if r.is_some() {
		kill(child_trie, key);
	}
	r
}

/// Remove `key` from storage, returning its value, or, if there was no explicit entry in storage,
/// the default for its type.
pub fn take_or_default<T: Codec + Sized + Default>(child_trie: &ChildTrie, key: &[u8]) -> T {
	take(child_trie, key).unwrap_or_else(Default::default)
}

/// Return the value of the item in storage under `key`, or `default_value` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or<T: Codec + Sized>(child_trie: &ChildTrie,key: &[u8], default_value: T) -> T {
	take(child_trie, key).unwrap_or(default_value)
}

/// Return the value of the item in storage under `key`, or `default_value()` if there is no
/// explicit entry. Ensure there is no explicit entry on return.
pub fn take_or_else<T: Codec + Sized, F: FnOnce() -> T>(
	child_trie: &ChildTrie,
	key: &[u8],
	default_value: F,
) -> T {
	take(child_trie, key).unwrap_or_else(default_value)
}

/// Check to see if `key` has an explicit entry in storage.
pub fn exists(child_trie: ChildTrieReadRef, key: &[u8]) -> bool {
	runtime_io::read_child_storage(child_trie, key, &mut [0;0][..], 0).is_some()
}

/// Remove all `storage_key` key/values
pub fn kill_storage(child_trie: &ChildTrie) {
	runtime_io::kill_child_storage(child_trie)
}

/// Ensure `key` has no explicit entry in storage.
pub fn kill(child_trie: &ChildTrie, key: &[u8]) {
	runtime_io::clear_child_storage(child_trie, key);
}

/// Get a Vec of bytes from storage.
pub fn get_raw(child_trie: ChildTrieReadRef, key: &[u8]) -> Option<Vec<u8>> {
	runtime_io::child_storage(child_trie, key)
}

/// Put a raw byte slice into storage.
pub fn put_raw(child_trie: &ChildTrie, key: &[u8], value: &[u8]) {
	runtime_io::set_child_storage(child_trie, key, value)
}

