// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Basic implementation for Externalities.

use std::collections::HashMap;
use std::iter::FromIterator;
use crate::backend::{Backend, InMemory, MapTransaction};
use hash_db::Hasher;
use trie::{TrieConfiguration, default_child_trie_root};
use trie::trie_types::Layout;
use primitives::offchain;
use primitives::storage::well_known_keys::is_child_storage_key;
use primitives::child_trie::{ChildTrie, ChildTrieReadRef, KeySpace};
use super::Externalities;
use log::warn;

/// Simple HashMap-based Externalities impl.
#[derive(Debug)]
pub struct BasicExternalities {
	top: HashMap<Vec<u8>, Vec<u8>>,
	children: HashMap<KeySpace, (HashMap<Vec<u8>, Vec<u8>>, ChildTrie)>,
	pending_child: HashMap<Vec<u8>, Option<KeySpace>>,
}

impl BasicExternalities {

	/// Create a new instance of `BasicExternalities`
	pub fn new(map: MapTransaction) -> Self {
		let pending_child = map.children.values()
			.map(|(_, child_trie)| (
					child_trie.parent_slice().to_vec(),
					Some(child_trie.keyspace().clone())
			)).collect();

		BasicExternalities {
			top: map.top,
			children: map.children,
			pending_child,
		}
	}

	/// Insert key/value
	pub fn insert(&mut self, k: Vec<u8>, v: Vec<u8>) -> Option<Vec<u8>> {
		self.top.insert(k, v)
	}

	/// Consume self and returns inner storages
	pub fn into_storages(self) -> MapTransaction {
		MapTransaction {top: self.top, children: self.children}
	}
}

impl PartialEq for BasicExternalities {
	fn eq(&self, other: &BasicExternalities) -> bool {
		self.top.eq(&other.top) && self.children.eq(&other.children)
	}
}

impl FromIterator<(Vec<u8>, Vec<u8>)> for BasicExternalities {
	fn from_iter<I: IntoIterator<Item=(Vec<u8>, Vec<u8>)>>(iter: I) -> Self {
		let mut t = Self::default();
		t.top.extend(iter);
		t
	}
}

impl Default for BasicExternalities {
	fn default() -> Self { Self::new(Default::default()) }
}

impl From<HashMap<Vec<u8>, Vec<u8>>> for BasicExternalities {
	fn from(hashmap: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		BasicExternalities {
			top: hashmap,
			children: Default::default(),
			pending_child: Default::default(),
		}
	}
}

impl<H: Hasher> Externalities<H> for BasicExternalities where H::Out: Ord {
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.top.get(key).cloned()
	}

	fn original_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		Externalities::<H>::storage(self, key)
	}

	fn child_storage(&self, child_trie: ChildTrieReadRef, key: &[u8]) -> Option<Vec<u8>> {
		let keyspace = child_trie.keyspace();
		self.children.get(keyspace).and_then(|child| child.0.get(key)).cloned()
	}

	fn child_trie(&self, storage_key: &[u8]) -> Option<ChildTrie> {
		match self.pending_child.get(storage_key) {
			Some(Some(keyspace)) => {
				let map = self.children.get(keyspace)
					.expect("pending entry always have a children association; qed");
				return Some(map.1.clone());
			},
			Some(None) => None,
			None => None,
		}
	}

	fn original_child_storage(&self, child_trie: ChildTrieReadRef, key: &[u8]) -> Option<Vec<u8>> {
		Externalities::<H>::child_storage(self, child_trie, key)
	}

	fn place_storage(&mut self, key: Vec<u8>, maybe_value: Option<Vec<u8>>) {
		if is_child_storage_key(&key) {
			warn!(target: "trie", "Refuse to set child storage key via main storage");
			return;
		}

		match maybe_value {
			Some(value) => { self.top.insert(key, value); }
			None => { self.top.remove(&key); }
		}
	}

	fn place_child_storage(
		&mut self,
		child_trie: &ChildTrie,
		key: Vec<u8>,
		value: Option<Vec<u8>>
	) {
		let p = &mut self.children;
		let pc = &mut self.pending_child;
		let child_map = p.entry(child_trie.keyspace().clone())
			.or_insert_with(|| {
				let parent = child_trie.parent_slice().to_vec();
				pc.insert(parent, Some(child_trie.keyspace().clone()));
				(Default::default(), child_trie.clone())
			});

		if let Some(value) = value {
			child_map.0.insert(key, value);
		} else {
			child_map.0.remove(&key);
		}
	}

	fn kill_child_storage(&mut self, child_trie: &ChildTrie) {
		let keyspace = child_trie.keyspace();
		if let Some((map_val, _ct)) = self.children.get_mut(keyspace) {
			map_val.clear();
		}
	}

	fn set_child_trie(&mut self, child_trie: ChildTrie) -> bool {
		let keyspace = child_trie.keyspace();
		if let Some((_, old_ct)) = self.children.get_mut(keyspace) {
			if old_ct.is_updatable_with(&child_trie) {
				*old_ct = child_trie;
			} else {
				return false;
			}
		} else {
			self.pending_child.insert(child_trie.parent_slice().to_vec(), Some(child_trie.keyspace().clone()));
			self.children.insert(keyspace.to_vec(), (Default::default(), child_trie));
		}
		true
	}
	
	fn clear_prefix(&mut self, prefix: &[u8]) {
		if is_child_storage_key(prefix) {
			warn!(
				target: "trie",
				"Refuse to clear prefix that is part of child storage key via main storage"
			);
			return;
		}

		self.top.retain(|key, _| !key.starts_with(prefix));
	}

	fn clear_child_prefix(&mut self, child_trie: &ChildTrie, prefix: &[u8]) {
		let keyspace = child_trie.keyspace();
		if let Some(child) = self.children.get_mut(keyspace) {
			child.0.retain(|key, _| !key.starts_with(prefix));
		}
	}

	fn chain_id(&self) -> u64 { 42 }

	fn storage_root(&mut self) -> H::Out {

		let mut top = self.top.clone();
		let child_tries: Vec<_> = self.children.values().map(|v| v.1.clone()).collect();
		// Single child trie implementation currently allows using the same child
		// empty root for all child trie. Using null storage key until multiple
		// type of child trie support.
		let empty_hash = default_child_trie_root::<Layout<H>>();
		for child_trie in child_tries {
			let child_root = <Self as Externalities<H>>::child_storage_root(self, &child_trie);
			if &empty_hash[..] == &child_root[..] && child_trie.extension().len() > 0 {
				top.remove(child_trie.parent_trie());
			} else {
				top.insert(child_trie.parent_trie().to_vec(), child_trie.encoded_with_root(&child_root));
			}
		}
		Layout::<H>::trie_root(self.top.clone())
	}

	fn child_storage_root(&mut self, child_trie: &ChildTrie) -> Vec<u8> {
		let keyspace = child_trie.keyspace();
		if let Some(child) = self.children.get(keyspace) {
			let delta = child.0.clone().into_iter().map(|(k, v)| (k, Some(v)));

			InMemory::<H>::default().child_storage_root(&child.1, delta).0
		} else {
			default_child_trie_root::<Layout<H>>()
		}
	}

	fn storage_changes_root(&mut self, _parent: H::Out) -> Result<Option<H::Out>, ()> {
		Ok(None)
	}

	fn offchain(&mut self) -> Option<&mut dyn offchain::Externalities> {
		warn!("Call to non-existent offchain externalities set.");
		None
	}

	fn keystore(&self) -> Option<primitives::traits::BareCryptoStorePtr> {
		warn!("Call to non-existent keystore.");
		None
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use primitives::{Blake2Hasher, H256, map};
	use primitives::storage::well_known_keys::CODE;
	use hex_literal::hex;

	#[test]
	fn commit_should_work() {
		let mut ext = BasicExternalities::default();
		let ext = &mut ext as &mut dyn Externalities<Blake2Hasher>;
		ext.set_storage(b"doe".to_vec(), b"reindeer".to_vec());
		ext.set_storage(b"dog".to_vec(), b"puppy".to_vec());
		ext.set_storage(b"dogglesworth".to_vec(), b"cat".to_vec());
		const ROOT: [u8; 32] = hex!("39245109cef3758c2eed2ccba8d9b370a917850af3824bc8348d505df2c298fa");

		assert_eq!(ext.storage_root(), H256::from(ROOT));
	}

	#[test]
	fn set_and_retrieve_code() {
		let mut ext = BasicExternalities::default();
		let ext = &mut ext as &mut dyn Externalities<Blake2Hasher>;

		let code = vec![1, 2, 3];
		ext.set_storage(CODE.to_vec(), code.clone());

		assert_eq!(&ext.storage(CODE).unwrap(), &code);
	}

	#[test]
	fn children_works() {
		let child_storage = b":child_storage:default:test";

		// use a dummy child trie (keyspace and undefined trie).
		let child_trie = ChildTrie::fetch_or_new(|_| None, |_| (), child_storage, || 1u128);
		let mut ext = BasicExternalities::new(MapTransaction {
			top: Default::default(),
			children: map![
				child_trie.keyspace().to_vec() => (map![
					b"doe".to_vec() => b"reindeer".to_vec()
				], child_trie.clone())
			],
		});

		let ext = &mut ext as &mut dyn Externalities<Blake2Hasher>;

		assert_eq!(ext.child_storage(child_trie.node_ref(), b"doe"), Some(b"reindeer".to_vec()));

		ext.set_child_storage(&child_trie, b"dog".to_vec(), b"puppy".to_vec());
		assert_eq!(ext.child_storage(child_trie.node_ref(), b"dog"), Some(b"puppy".to_vec()));

		ext.clear_child_storage(&child_trie, b"dog");
		assert_eq!(ext.child_storage(child_trie.node_ref(), b"dog"), None);

		ext.kill_child_storage(&child_trie);
		assert_eq!(ext.child_storage(child_trie.node_ref(), b"doe"), None);
	}

	#[test]
	fn basic_externalities_is_empty() {
		// Make sure no values are set by default in `BasicExternalities`.
		let storages = BasicExternalities::new(Default::default()).into_storages();
		assert!(storages.top.is_empty());
		assert!(storages.children.is_empty());
	}
}
