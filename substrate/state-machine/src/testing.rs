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

//! Test implementation for Externalities.

use std::collections::HashMap;
use triehash::trie_root;
use keys_set::{Set as KeysSet, Storage as KeysSetStorage};
use Externalities;

/// Simple HashMap based Externalities impl.
pub type TestExternalities = HashMap<Vec<u8>, Vec<u8>>;

/// Implementation of keys set storage for TestExternalities.
pub(crate) struct TestKeysSetStorage<'a>(pub &'a mut TestExternalities);

impl Externalities for TestExternalities {
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.get(key).map(|x| x.to_vec())
	}

	fn exists_previous_storage(&self, key: &[u8]) -> bool {
		// we do not really need this in testing, since storage in testing is
		// created for single block only => just work as exists_storage() here
		self.get(key).is_some()
	}

	fn place_storage(&mut self, key: Vec<u8>, maybe_value: Option<Vec<u8>>) {
		match maybe_value {
			Some(value) => { self.insert(key, value); }
			None => { self.remove(&key); }
		}
	}

	fn place_prefix(&mut self, _include_new_keys: bool, prefix: &[u8], value: Option<Vec<u8>>) {
		match value {
			None => self.retain(|key, _| !key.starts_with(prefix)),
			Some(value) => {
				for (key, data_value) in self.iter_mut() {
					if key.starts_with(prefix) {
						*data_value = value.clone();
					}
				}
			},
		}
	}

	fn save_pefix_keys(&mut self, _include_new_keys: bool, prefix: &[u8], set_prefix: &[u8]) {
		// in test implementation, prefix overlap won't lead to inifinite execution
		// but other implementations could suffer
		// => do not allow overlaps
		// panic is safe here, since this should only be called from the runtime
		assert!(!set_prefix.starts_with(prefix));

		// it is safe to collect here, since TestExternalities are used in tests only
		let keys_to_save: Vec<_> = self.keys()
			.filter(|key| key.starts_with(prefix))
			.cloned()
			.collect();

		// insert keys to the set
		let mut set_storage = TestKeysSetStorage(self);
		let mut set = KeysSet::new(set_prefix, &mut set_storage);
		for key in keys_to_save {
			set.insert(&key);
		}
	}

	fn chain_id(&self) -> u64 { 42 }

	fn storage_root(&mut self) -> [u8; 32] {
		trie_root(self.clone()).0
	}
}

impl<'a> KeysSetStorage for TestKeysSetStorage<'a> {
	fn read(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.0.storage(key)
	}

	fn set(&mut self, key: &[u8], value: &[u8]) {
		self.0.place_storage(key.to_vec(), Some(value.to_vec()));
	}

	fn clear(&mut self, key: &[u8]) {
		self.0.place_storage(key.to_vec(), None);
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn commit_should_work() {
		let mut ext = TestExternalities::new();
		ext.set_storage(b"doe".to_vec(), b"reindeer".to_vec());
		ext.set_storage(b"dog".to_vec(), b"puppy".to_vec());
		ext.set_storage(b"dogglesworth".to_vec(), b"cat".to_vec());
		const ROOT: [u8; 32] = hex!("8aad789dff2f538bca5d8ea56e8abe10f4c7ba3a5dea95fea4cd6e7c3a1168d3");
		assert_eq!(ext.storage_root(), ROOT);
	}
}
