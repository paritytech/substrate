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
use std::sync::Arc;
use changes_trie::{compute_changes_trie_root, Configuration as ChangesTrieConfig, Storage as ChangesTrieStorage};
use super::{Externalities, OverlayedChanges};
use triehash::trie_root;

/// Simple HashMap based Externalities impl.
#[derive(Default)]
pub struct TestExternalities {
	data: HashMap<Vec<u8>, Vec<u8>>,
	changes_trie_storage: Option<Arc<ChangesTrieStorage>>,
	changes: OverlayedChanges,
}

impl TestExternalities {
	/// Create new test externalities.
	pub fn new(data: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		Self { data, ..Default::default() }
	}

	/// Consumes self, returning data map.
	pub fn into_data(self) -> HashMap<Vec<u8>, Vec<u8>> {
		self.data
	}
}

impl From<HashMap<Vec<u8>, Vec<u8>>> for TestExternalities {
	fn from(data: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		Self { data, ..Default::default() }
	}
}

impl Externalities for TestExternalities {
	fn set_changes_trie_config(&mut self, block: u64, digest_interval: u64, digest_levels: u8) {
		self.changes.set_changes_trie_config(block, ChangesTrieConfig {
			digest_interval,
			digest_levels,
		});
	}

	fn bind_to_extrinsic(&mut self, extrinsic_index: u32) {
		self.changes.set_extrinsic_index(extrinsic_index);
	}

	fn storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.data.get(key).map(|x| x.to_vec())
	}

	fn place_storage(&mut self, key: Vec<u8>, maybe_value: Option<Vec<u8>>) {
		self.changes.set_storage(key.clone(), maybe_value.clone());
		match maybe_value {
			Some(value) => { self.data.insert(key, value); }
			None => { self.data.remove(&key); }
		}
	}

	fn clear_prefix(&mut self, prefix: &[u8]) {
		self.changes.clear_prefix(prefix);
		self.data.retain(|key, _| !key.starts_with(prefix));
	}

	fn chain_id(&self) -> u64 { 42 }

	fn storage_root(&mut self) -> [u8; 32] {
		trie_root(self.data.clone()).0
	}

	fn storage_changes_root(&mut self) -> Option<[u8; 32]> {
		compute_changes_trie_root(self.changes_trie_storage.clone(), &self.changes)
			.map(|(root, _)| root.clone())
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn commit_should_work() {
		let mut ext = TestExternalities::default();
		ext.set_storage(b"doe".to_vec(), b"reindeer".to_vec());
		ext.set_storage(b"dog".to_vec(), b"puppy".to_vec());
		ext.set_storage(b"dogglesworth".to_vec(), b"cat".to_vec());
		const ROOT: [u8; 32] = hex!("8aad789dff2f538bca5d8ea56e8abe10f4c7ba3a5dea95fea4cd6e7c3a1168d3");
		assert_eq!(ext.storage_root(), ROOT);
	}
}
