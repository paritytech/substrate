// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Storage value prefix related functions.

/// The storage entry at this key contains the prefix, which is prepended to all
/// storage values that we're storing.
pub const PREFIX_KEY: &'static [u8] = b":prefix";
/// The storage prefix of the set of deleted keys. When storage value
/// prefixes are enabled, values are not deleted immediately, but instead marked as
/// deleted (inserted into this set).
/// Runtime could perform purge at some intervals by calling purge_storage().
pub const DELETED_SET_KEY_PREFIX: &'static [u8] = b":deleted";

pub use self::shared::PREFIX_LEN_KEY;
pub use self::api::{is_prefix_configured, read_prefix_len, add_prefix,
	strip_prefix, purge, schedule_purge};

/// Result of purge filter function.
pub enum PurgeFilterResult {
	/// Remove key from both deleted set and storage.
	Purge,
	/// Remove key from set only.
	RemoveFromSet,
	/// Leave key in set and in the storage.
	LeaveAsIs,
}

#[cfg(feature = "std")]
mod api {
	use substrate_state_machine::Externalities;
	use super::keys_set::{Set, Storage as SetStorage};
	use super::{PREFIX_LEN_KEY, PREFIX_KEY, DELETED_SET_KEY_PREFIX, shared};
	use {PurgeFilterResult, raw};

	struct RawSetStorage<'a>(&'a mut Externalities);

	impl<'a> SetStorage for RawSetStorage<'a> {
		fn read(&self, key: &[u8]) -> Option<Vec<u8>> { raw::storage(self.0, key) }
		fn set(&mut self, key: &[u8], value: &[u8]) { raw::set_storage(self.0, key, value); }
		fn clear(&mut self, key: &[u8]) { raw::clear_storage(self.0, key); }
	}

	/// Returns true if storage value prefix is configured in this runtime.
	pub fn is_prefix_configured(ext: &Externalities) -> bool {
		raw::storage(ext, PREFIX_LEN_KEY).is_some()
	}

	/// Read storage value at the PREFIX_LEN_KEY.
	pub fn read_prefix_len(ext: &Externalities) -> Option<u32> {
		shared::parse_prefix_len(raw::storage(ext, PREFIX_LEN_KEY))
			.expect("Externalities failure is intercepted by executor")
	}

	/// Add prefix to the value.
	pub fn add_prefix(ext: &Externalities, value: &[u8]) -> Vec<u8> {
		shared::add_prefix(
			raw::storage(ext, PREFIX_KEY),
			read_prefix_len(ext),
			value)
	}

	/// Strip prefix from the value.
	pub fn strip_prefix(ext: &Externalities, value: Vec<u8>) -> (Option<Vec<u8>>, Option<Vec<u8>>) {
		shared::strip_prefix(raw::storage(ext, PREFIX_LEN_KEY), value)
			.expect("Externalities failure is intercepted by executor")
	}

	/// Purge scheduled values.
	pub fn purge<F: Fn(&[u8], Option<Vec<u8>>, Option<Vec<u8>>) -> PurgeFilterResult>(ext: &mut Externalities, f: F) {
		let prefix_len = raw::storage(ext, PREFIX_LEN_KEY);
		Set::new(DELETED_SET_KEY_PREFIX, &mut RawSetStorage(ext)).retain(|storage, key| {
			let (prefix, value) = storage.read(key)
				.map(|value| shared::strip_prefix(prefix_len.clone(), value)
					.expect("Externalities failure is intercepted by executor"))
				.unwrap_or_default();
			match f(key, prefix, value) {
				PurgeFilterResult::Purge => {
					storage.clear(key);
					false
				},
				PurgeFilterResult::RemoveFromSet => false,
				PurgeFilterResult::LeaveAsIs => true,
			}
		});
	}

	/// Schedule value at given `key` for future purge.
	pub fn schedule_purge(ext: &mut Externalities, key: &[u8]) {
		Set::new(DELETED_SET_KEY_PREFIX, &mut RawSetStorage(ext)).insert(key);
	}
}

#[cfg(not(feature = "std"))]
mod api {
	use rstd::vec::Vec;
	use super::keys_set::{Set, Storage as SetStorage};
	use super::{PREFIX_LEN_KEY, PREFIX_KEY, DELETED_SET_KEY_PREFIX, shared};
	use {PurgeFilterResult, raw};

	struct RawSetStorage;

	impl SetStorage for RawSetStorage {
		fn read(&self, key: &[u8]) -> Option<Vec<u8>> { raw::storage(key) }
		fn set(&mut self, key: &[u8], value: &[u8]) { raw::set_storage(key, value); }
		fn clear(&mut self, key: &[u8]) { raw::clear_storage(key); }
	}

	/// Returns true if storage value prefix is configured in this runtime.
	pub fn is_prefix_configured() -> bool {
		raw::storage(PREFIX_LEN_KEY).is_some()
	}

	/// Read storage value at the PREFIX_LEN_KEY.
	pub fn read_prefix_len() -> Option<u32> {
		shared::parse_prefix_len(raw::storage(PREFIX_LEN_KEY))
			.expect("Externalities failure is intercepted by executor")
	}

	/// Add prefix to the value.
	pub fn add_prefix(value: &[u8]) -> Vec<u8> {
		shared::add_prefix(
			raw::storage(PREFIX_KEY),
			read_prefix_len(),
			value)
	}

	/// Strip prefix from the value.
	pub fn strip_prefix(value: Vec<u8>) -> (Option<Vec<u8>>, Option<Vec<u8>>) {
		shared::strip_prefix(raw::storage(PREFIX_LEN_KEY), value)
			.expect("Externalities failure is intercepted by executor")
	}

	/// Purge scheduled values.
	pub fn purge<F: Fn(&[u8], Option<Vec<u8>>, Option<Vec<u8>>) -> PurgeFilterResult>(f: F) {
		let prefix_len = raw::storage(PREFIX_LEN_KEY);
		Set::new(DELETED_SET_KEY_PREFIX, &mut RawSetStorage).retain(|storage, key| {
			let (prefix, value) = storage.read(key)
				.map(|value| shared::strip_prefix(prefix_len.clone(), value)
					.expect("Externalities failure is intercepted by executor"))
				.unwrap_or_default();
			match f(key, prefix, value) {
				PurgeFilterResult::Purge => {
					storage.clear(key);
					false
				},
				PurgeFilterResult::RemoveFromSet => false,
				PurgeFilterResult::LeaveAsIs => true,
			}
		});
	}

	/// Schedule value at given `key` for future purge.
	pub fn schedule_purge(key: &[u8]) {
		Set::new(DELETED_SET_KEY_PREFIX, &mut RawSetStorage).insert(key);
	}
}

mod shared {
	#[cfg(not(feature = "std"))]
	use rstd::vec::Vec;

	pub fn add_prefix(prefix_value: Option<Vec<u8>>, prefix_len: Option<u32>, value: &[u8]) -> Vec<u8> {
		assert_eq!(prefix_value.is_some(), prefix_len.is_some());

		prefix_value
			.map(|prefix| {
				let prefix_len = prefix_len.expect("asserted above") as usize;
				let mut prefixed_value = prefix[..prefix_len].to_vec();
				prefixed_value.extend(value);
				prefixed_value
			})
			.unwrap_or_else(|| value.to_vec())
	}

	include!("./prefix_shared.rs");
}

pub mod keys_set {
	#[cfg(not(feature = "std"))]
	use rstd::vec::Vec;
	use codec::{Decode, Encode};

	include!("./keys_set.rs");
}


#[cfg(all(feature = "std", test))]
mod tests {
	use std::collections::BTreeSet;
	use codec::Encode;
	use substrate_state_machine::{Externalities, TestExternalities};
	use super::{PREFIX_KEY, PREFIX_LEN_KEY, is_prefix_configured,
		read_prefix_len, add_prefix, strip_prefix, PurgeFilterResult};
	use super::shared::parse_prefix_len;
	use super::keys_set::{Set as KeysSet, Storage as KeysSetStorage};

	impl<'a> KeysSetStorage for &'a mut TestExternalities {
		fn read(&self, key: &[u8]) -> Option<Vec<u8>> { self.storage(key) }
		fn set(&mut self, key: &[u8], value: &[u8]) { self.place_storage(key.to_vec(), Some(value.to_vec())); }
		fn clear(&mut self, key: &[u8]) { self.place_storage(key.to_vec(), None); }
	}

	#[test]
	fn is_prefix_configured_works() {
		let mut ext = TestExternalities::default();
		assert!(!is_prefix_configured(&ext));
		ext.set_storage(PREFIX_LEN_KEY.to_vec(), 4u64.encode());
		assert!(is_prefix_configured(&ext));
	}

	#[test]
	fn read_prefix_len_works() {
		let mut ext = TestExternalities::default();
		assert_eq!(read_prefix_len(&ext), None);
		ext.set_storage(PREFIX_LEN_KEY.to_vec(), vec![0, 0, 0, 0, 4, 0, 0, 0]);
		assert_eq!(read_prefix_len(&ext), Some(4));
	}

	#[test]
	fn add_prefix_works() {
		let mut ext = TestExternalities::default();
		assert_eq!(add_prefix(&ext, &[42]), vec![42]);
		ext.set_storage(PREFIX_LEN_KEY.to_vec(), vec![0, 0, 0, 3, 0, 0, 0]);
		ext.set_storage(PREFIX_KEY.to_vec(), vec![1, 2, 3]);
		assert_eq!(read_prefix_len(&ext), Some(3));
		assert_eq!(add_prefix(&ext, &[42]), vec![1, 2, 3, 42]);
	}

	#[test]
	fn strip_prefix_works() {
		let mut ext = TestExternalities::default();
		assert_eq!(strip_prefix(&ext, vec![1, 2, 3, 42]), (None, Some(vec![1, 2, 3, 42])));
		ext.set_storage(PREFIX_LEN_KEY.to_vec(), vec![0, 0, 0, 3, 0, 0, 0]);
		assert_eq!(strip_prefix(&ext, vec![1, 2, 3, 42]), (Some(vec![1, 2, 3]), Some(vec![42])));
		assert_eq!(strip_prefix(&ext, vec![1, 2, 3]), (Some(vec![1, 2, 3]), None));
	}

	#[test]
	fn parse_prefix_len_succeds() {
		assert_eq!(parse_prefix_len(None), Ok(None));
		assert_eq!(parse_prefix_len(Some(vec![])), Ok(None));
		assert_eq!(parse_prefix_len(Some(vec![0, 0, 0, 0])), Ok(None));
		assert_eq!(parse_prefix_len(Some(vec![0, 0, 0, 0, 4, 0, 0, 0])), Ok(Some(4)));
		assert_eq!(parse_prefix_len(Some(vec![0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0])), Ok(Some(8)));
		assert_eq!(parse_prefix_len(Some(vec![5, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0])), Ok(Some(8)));
	}

	#[test]
	fn parse_prefix_len_fails() {
		assert!(parse_prefix_len(Some(vec![0])).is_err());
		assert!(parse_prefix_len(Some(vec![0, 0, 0])).is_err());
		assert!(parse_prefix_len(Some(vec![0, 0, 4, 0, 0, 0])).is_err());
	}

	fn with_keys_set<F: FnMut(&mut KeysSet<&mut TestExternalities>)>(mut f: F) -> Vec<Vec<u8>> {
		let mut ext = TestExternalities::default();
		let mut storage = &mut ext;
		let mut set = KeysSet::new(b"set", &mut storage);
		f(&mut set);

		let mut keys = BTreeSet::new();
		set.retain(|_, key| {
			keys.insert(key.to_vec());
			false
		});

		keys.into_iter().collect()
	}

	#[test]
	fn keys_are_inserted_into_keys_set() {
		assert_eq!(with_keys_set(|set| {
			set.insert(b"key1");
			set.insert(b"key2");
			set.insert(b"key3");
		}), vec![b"key1".to_vec(), b"key2".to_vec(), b"key3".to_vec()]);
	}

	#[test]
	fn keys_are_retained_from_the_middle_of_keys_set() {
		assert_eq!(with_keys_set(|set| {
			set.insert(b"key1");
			set.insert(b"key2");
			set.insert(b"key3");
			set.retain(|_, key| key != b"key2");
		}), vec![b"key1".to_vec(), b"key3".to_vec()]);
	}

	#[test]
	fn keys_are_retained_from_the_beginning_of_keys_set() {
		assert_eq!(with_keys_set(|set| {
			set.insert(b"key1");
			set.insert(b"key2");
			set.insert(b"key3");
			set.retain(|_, key| key != b"key1");
		}), vec![b"key2".to_vec(), b"key3".to_vec()]);
	}

	#[test]
	fn keys_are_retained_from_the_end_of_keys_set() {
		assert_eq!(with_keys_set(|set| {
			set.insert(b"key1");
			set.insert(b"key2");
			set.insert(b"key3");
			set.retain(|_, key| key != b"key3");
		}), vec![b"key1".to_vec(), b"key2".to_vec()]);
	}

	#[test]
	fn keys_are_fully_retained_from_keys_set() {
		assert!(with_keys_set(|set| {
			set.insert(b"key1");
			set.insert(b"key2");
			set.insert(b"key3");
			set.retain(|_, _| false);
		}).is_empty());
	}

	#[test]
	fn duplicate_keys_are_not_inserted_into_keys_set() {
		assert_eq!(with_keys_set(|set| {
			set.insert(b"key1");
			set.insert(b"key1");
		}), vec![b"key1".to_vec()]);
	}

	#[test]
	fn keys_are_inserted_after_removal() {
		assert_eq!(with_keys_set(|set| {
			set.insert(b"key1");
			set.retain(|_, _| false);
			set.insert(b"key1");
			set.insert(b"key2");
		}), vec![b"key1".to_vec(), b"key2".to_vec()]);
	}
}
