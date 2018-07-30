// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Concrete externalities implementation.

use std::{error, fmt, cell::RefCell, collections::HashMap};
use backend::Backend;
use keys_set::{Set as KeysSet, Storage as KeysSetStorage};
use {Externalities, OverlayedChanges};

/// Errors that can occur when interacting with the externalities.
#[derive(Debug, Copy, Clone)]
pub enum Error<B, E> {
	/// Failure to load state data from the backend.
	#[allow(unused)]
	Backend(B),
	/// Failure to execute a function.
	#[allow(unused)]
	Executor(E),
}

impl<B: fmt::Display, E: fmt::Display> fmt::Display for Error<B, E> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		match *self {
			Error::Backend(ref e) => write!(f, "Storage backend error: {}", e),
			Error::Executor(ref e) => write!(f, "Sub-call execution error: {}", e),
		}
	}
}

impl<B: error::Error, E: error::Error> error::Error for Error<B, E> {
	fn description(&self) -> &str {
		match *self {
			Error::Backend(..) => "backend error",
			Error::Executor(..) => "executor error",
		}
	}
}

/// Wraps a read-only backend, call executor, and current overlayed changes.
pub struct Ext<'a, B: 'a + Backend> {
	// The overlayed changes to write to.
	overlay: &'a mut OverlayedChanges,
	// The storage backend to read from.
	backend: &'a B,
	// The transaction necessary to commit to the backend.
	transaction: Option<(B::Transaction, [u8; 32])>,
	// In-memory cache for frequently used values.
	cache: RefCell<HashMap<Vec<u8>, Option<Vec<u8>>>>,
}

/// Implementation of keys set storage for Backend + OverlayedChanges.
struct ExtKeysSetStorage<'a, B: 'a>(&'a B, &'a mut OverlayedChanges);

impl<'a, B: 'a + Backend> Ext<'a, B> {
	/// Create a new `Ext` from overlayed changes and read-only backend
	pub fn new(overlay: &'a mut OverlayedChanges, backend: &'a B) -> Self {
		Ext {
			overlay,
			backend,
			transaction: None,
			cache: Default::default(),
		}
	}

	/// Get the transaction necessary to update the backend.
	pub fn transaction(mut self) -> B::Transaction {
		let _ = self.storage_root();
		self.transaction.expect("transaction always set after calling storage root; qed").0
	}

	/// Invalidates the currently cached storage root and the db transaction.
	///
	/// Called when there are changes that likely will invalidate the storage root.
	fn mark_dirty(&mut self) {
		self.transaction = None;
	}
}

impl<'a, B: 'a> Externalities for Ext<'a, B>
	where B: Backend
{
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.overlay.storage(key).map(|x| x.map(|x| x.to_vec())).unwrap_or_else(||
			self.backend.storage(key).expect("Externalities not allowed to fail within runtime"))
	}

	fn cached_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.overlay.storage(key)
			.map(|x| x.map(|x| x.to_vec()))
			.unwrap_or_else(|| {
				let value_from_cache = self.cache.borrow().get(key).cloned();
				match value_from_cache {
					Some(value) => value,
					None => {
						let value = self.backend.storage(key)
							.expect("Externalities not allowed to fail within runtime");
						self.cache.borrow_mut().insert(key.to_vec(), value.clone());
						value
					},
				}
			})
	}

	fn exists_storage(&self, key: &[u8]) -> bool {
		match self.overlay.storage(key) {
			Some(x) => x.is_some(),
			_ => self.backend.exists_storage(key).expect("Externalities not allowed to fail within runtime"),
		}
	}

	fn exists_previous_storage(&self, key: &[u8]) -> bool {
		self.backend.exists_storage(key).expect("Externalities not allowed to fail within runtime")
	}

	fn place_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>) {
		self.mark_dirty();
		self.overlay.set_storage(key, value);
	}

	fn place_prefix(&mut self, include_new_keys: bool, prefix: &[u8], value: Option<Vec<u8>>) {
		self.mark_dirty();
		if include_new_keys {
			self.overlay.set_prefix(prefix, value.clone());
		}
		self.backend.for_keys_with_prefix(prefix, |key| {
			self.overlay.set_storage(key.to_vec(), value.clone());
		});
	}

	fn save_pefix_keys(&mut self, include_new_keys: bool, prefix: &[u8], set_prefix: &[u8]) {
		// do not allow overlaps
		// panic is safe here, since this should only be called from the runtime
		assert!(!set_prefix.starts_with(prefix));

		// collecting all keys from OverlayedChanges with filter couldn't
		// take more memory than the OverlayedChanges itself
		// => since we need to iterate OverlayedChanges + insert into OverlayedChanges
		// => collect all affected OverlayedChanges keys before iterating backend
		let mut overlayed_keys: Vec<Vec<u8>> = Vec::new();
		if include_new_keys {
			self.overlay.for_keys_with_prefix(prefix, |key| overlayed_keys.push(key.to_vec()));
		}

		// insert keys to the set
		self.mark_dirty();
		{
			let mut set_storage = ExtKeysSetStorage(self.backend, self.overlay);
			let mut set = KeysSet::new(set_prefix, &mut set_storage);
			for overlayed_key in overlayed_keys {
				set.insert(&overlayed_key);
			}
			self.backend.for_keys_with_prefix(prefix, |key| set.insert(key));
		}
	}

	fn chain_id(&self) -> u64 {
		42
	}

	fn storage_root(&mut self) -> [u8; 32] {
		if let Some((_, ref root)) =  self.transaction {
			return root.clone();
		}

		// compute and memoize
		let delta = self.overlay.committed.iter()
			.chain(self.overlay.prospective.iter())
			.map(|(k, v)| (k.clone(), v.clone()));

		let (root, transaction) = self.backend.storage_root(delta);
		self.transaction = Some((transaction, root));
		root
	}
}

impl<'a, B: 'a + Backend> KeysSetStorage for ExtKeysSetStorage<'a, B> {
	fn read(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.1.storage(key).map(|x| x.map(|x| x.to_vec())).unwrap_or_else(||
			self.0.storage(key).expect("Externalities not allowed to fail within runtime"))
	}

	fn set(&mut self, key: &[u8], value: &[u8]) {
		self.1.set_storage(key.to_vec(), Some(value.to_vec()));
	}

	fn clear(&mut self, key: &[u8]) {
		self.1.set_storage(key.to_vec(), None);
	}
}

#[cfg(test)]
mod tests {
	use backend::InMemory;
	use testing::TestKeysSetStorage;
	use TestExternalities;
	use super::*;

	fn with_backend_based_ext<F: Fn(&mut Externalities)>(f: F) {
		let backend: InMemory = vec![(b"doe".to_vec(), b"reindeer".to_vec()),
			(b"dog".to_vec(), b"puppy".to_vec()),
			(b"dogglesworth".to_vec(), b"cat".to_vec())].into_iter()
			.collect::<::std::collections::HashMap<_, _>>().into();
		let mut changes = OverlayedChanges::default();
		let mut ext = Ext::new(&mut changes, &backend);
		f(&mut ext);
	}

	fn with_testing_ext<F: Fn(&mut Externalities)>(f: F) {
		let mut ext = TestExternalities::new();
		ext.set_storage(b"doe".to_vec(), b"reindeer".to_vec());
		ext.set_storage(b"dog".to_vec(), b"puppy".to_vec());
		ext.set_storage(b"dogglesworth".to_vec(), b"cat".to_vec());
		f(&mut ext);
	}

	#[test]
	fn removal_with_place_prefix_works() {
		fn do_test(ext: &mut Externalities) {
			ext.place_prefix(true, b"dog", None);
			assert!(ext.storage(b"doe").is_some());
			assert!(ext.storage(b"dog").is_none());
			assert!(ext.storage(b"dogglesworth").is_none());
		}

		with_backend_based_ext(do_test);
		with_testing_ext(do_test);
	}

	#[test]
	fn ext_update_with_place_prefix_works() {
		fn do_test(ext: &mut Externalities) {
			ext.place_storage(b"doggy".to_vec(), Some(b"new_key".to_vec()));
			ext.place_prefix(true, b"dog", Some(b"puma".to_vec()));
			assert_eq!(ext.storage(b"doe"), Some(b"reindeer".to_vec()));
			assert_eq!(ext.storage(b"dog"), Some(b"puma".to_vec()));
			assert_eq!(ext.storage(b"dogglesworth"), Some(b"puma".to_vec()));
			assert_eq!(ext.storage(b"doggy"), Some(b"puma".to_vec()));
		}

		with_backend_based_ext(do_test);
		with_testing_ext(do_test);
	}

	#[test]
	fn ext_update_with_place_prefix_does_not_include_new_keys() {
		fn do_test(ext: &mut Externalities) {
			ext.place_storage(b"doggy".to_vec(), Some(b"new_key".to_vec()));
			ext.place_prefix(false, b"dog", Some(b"puma".to_vec()));
			assert_eq!(ext.storage(b"doe"), Some(b"reindeer".to_vec()));
			assert_eq!(ext.storage(b"dog"), Some(b"puma".to_vec()));
			assert_eq!(ext.storage(b"dogglesworth"), Some(b"puma".to_vec()));
			assert_eq!(ext.storage(b"doggy"), Some(b"new_key".to_vec()));
		}

		with_backend_based_ext(do_test);
	}

	#[test]
	fn testing_ext_save_prefix_keys_works() {
		let mut ext = TestExternalities::new();
		ext.set_storage(b"doe".to_vec(), b"reindeer".to_vec());
		ext.set_storage(b"dog".to_vec(), b"puppy".to_vec());
		ext.set_storage(b"dogglesworth".to_vec(), b"cat".to_vec());

		ext.save_pefix_keys(true, b"dog", b":deleted");

		let mut set_storage = TestKeysSetStorage(&mut ext);
		let mut set = KeysSet::new(b":deleted", &mut set_storage);
		let mut saved_keys = ::std::collections::BTreeSet::new();
		set.retain(|_, key| { saved_keys.insert(key.to_vec()); false });
		assert_eq!(vec![b"dog".to_vec(), b"dogglesworth".to_vec()],
			saved_keys.into_iter().collect::<Vec<_>>());
	}

	#[test]
	fn backend_ext_save_prefix_keys_works() {
		let backend: InMemory = vec![
			(b"doe".to_vec(), b"reindeer".to_vec()),
			(b"dog".to_vec(), b"puppy".to_vec()),
			(b"dogglesworth".to_vec(), b"cat".to_vec())].into_iter()
			.collect::<::std::collections::HashMap<_, _>>().into();
		let mut changes = OverlayedChanges::default();
		let mut ext = Ext::new(&mut changes, &backend);

		ext.save_pefix_keys(true, b"dog", b":deleted");

		let mut set_storage = ExtKeysSetStorage(ext.backend, ext.overlay);
		let mut set = KeysSet::new(b":deleted", &mut set_storage);
		let mut saved_keys = ::std::collections::BTreeSet::new();
		set.retain(|_, key| { saved_keys.insert(key.to_vec()); false });
		assert_eq!(vec![b"dog".to_vec(), b"dogglesworth".to_vec()],
			saved_keys.into_iter().collect::<Vec<_>>());
	}

	#[test]
	fn backend_ext_save_prefix_keys_does_not_include_new_keys() {
		let backend: InMemory = vec![
			(b"doe".to_vec(), b"reindeer".to_vec()),
			(b"dog".to_vec(), b"puppy".to_vec()),
			(b"dogglesworth".to_vec(), b"cat".to_vec())].into_iter()
			.collect::<::std::collections::HashMap<_, _>>().into();
		let mut changes = OverlayedChanges::default();
		let mut ext = Ext::new(&mut changes, &backend);

		ext.place_storage(b"dog".to_vec(), Some(b"old_key".to_vec()));
		ext.place_storage(b"doggy".to_vec(), Some(b"new_key".to_vec()));
		ext.save_pefix_keys(false, b"dog", b":deleted");

		let mut set_storage = ExtKeysSetStorage(ext.backend, ext.overlay);
		let mut set = KeysSet::new(b":deleted", &mut set_storage);
		let mut saved_keys = ::std::collections::BTreeSet::new();
		set.retain(|_, key| { saved_keys.insert(key.to_vec()); false });
		assert_eq!(vec![b"dog".to_vec(), b"dogglesworth".to_vec()],
			saved_keys.into_iter().collect::<Vec<_>>());
	}

	#[test]
	#[should_panic]
	fn backend_ext_save_prefix_panics_when_used_wrong() {
		with_backend_based_ext(|ext| ext.save_pefix_keys(false, b":de", b":deleted"));
	}

	#[test]
	#[should_panic]
	fn testing_ext_save_prefix_panics_when_used_wrong() {
		TestExternalities::new().save_pefix_keys(false, b":de", b":deleted")
	}
}
