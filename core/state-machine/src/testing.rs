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

//! Test implementation for Externalities.

use std::collections::HashMap;
use std::iter::FromIterator;
use hash_db::Hasher;
use trie::trie_root;
use crate::backend::InMemory;
use crate::changes_trie::{compute_changes_trie_root, InMemoryStorage as ChangesTrieInMemoryStorage, AnchorBlockId};
use primitives::storage::well_known_keys::{CHANGES_TRIE_CONFIG, CODE, HEAP_PAGES};
use parity_codec::Encode;
use super::{ChildStorageKey, Externalities, OverlayedChanges};

/// Simple HashMap-based Externalities impl.
pub struct TestExternalities<H: Hasher> {
	inner: HashMap<Vec<u8>, Vec<u8>>,
	changes_trie_storage: ChangesTrieInMemoryStorage<H>,
	changes: OverlayedChanges,
	code: Option<Vec<u8>>,
}

impl<H: Hasher> TestExternalities<H> {
	/// Create a new instance of `TestExternalities`
	pub fn new(inner: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		Self::new_with_code(&[], inner)
	}

	/// Create a new instance of `TestExternalities`
	pub fn new_with_code(code: &[u8], mut inner: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		let mut overlay = OverlayedChanges::default();
		super::set_changes_trie_config(
			&mut overlay,
			inner.get(&CHANGES_TRIE_CONFIG.to_vec()).cloned(),
			false,
		).expect("changes trie configuration is correct in test env; qed");

		inner.insert(HEAP_PAGES.to_vec(), 8u64.encode());

		TestExternalities {
			inner,
			changes_trie_storage: ChangesTrieInMemoryStorage::new(),
			changes: overlay,
			code: Some(code.to_vec()),
		}
	}

	/// Insert key/value
	pub fn insert(&mut self, k: Vec<u8>, v: Vec<u8>) -> Option<Vec<u8>> {
		self.inner.insert(k, v)
	}
}

impl<H: Hasher> ::std::fmt::Debug for TestExternalities<H> {
	fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
		write!(f, "{:?}", self.inner)
	}
}

impl<H: Hasher> PartialEq for TestExternalities<H> {
	fn eq(&self, other: &TestExternalities<H>) -> bool {
		self.inner.eq(&other.inner)
	}
}

impl<H: Hasher> FromIterator<(Vec<u8>, Vec<u8>)> for TestExternalities<H> {
	fn from_iter<I: IntoIterator<Item=(Vec<u8>, Vec<u8>)>>(iter: I) -> Self {
		let mut t = Self::new(Default::default());
		t.inner.extend(iter);
		t
	}
}

impl<H: Hasher> Default for TestExternalities<H> {
	fn default() -> Self { Self::new(Default::default()) }
}

impl<H: Hasher> From<TestExternalities<H>> for HashMap<Vec<u8>, Vec<u8>> {
	fn from(tex: TestExternalities<H>) -> Self {
		tex.inner.into()
	}
}

impl<H: Hasher> From< HashMap<Vec<u8>, Vec<u8>> > for TestExternalities<H> {
	fn from(hashmap: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		TestExternalities {
			inner: hashmap,
			changes_trie_storage: ChangesTrieInMemoryStorage::new(),
			changes: Default::default(),
			code: None,
		}
	}
}

// TODO child test primitives are currently limited to `changes` (for non child the way
// things are defined seems utterly odd to (put changes in changes but never make them
// available for read through inner)
impl<H: Hasher> Externalities<H> for TestExternalities<H> where H::Out: Ord {
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		match key {
			CODE => self.code.clone(),
			_ => self.inner.get(key).cloned(),
		}
	}

	fn original_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.storage(key)
	}

	fn child_storage(&self, storage_key: ChildStorageKey<H>, key: &[u8]) -> Option<Vec<u8>> {
		self.changes.child_storage(storage_key.as_ref(), key)?.map(Vec::from)
	}

	fn place_storage(&mut self, key: Vec<u8>, maybe_value: Option<Vec<u8>>) {
		self.changes.set_storage(key.clone(), maybe_value.clone());
		match key.as_ref() {
			CODE => self.code = maybe_value,
			_ => {
				match maybe_value {
					Some(value) => { self.inner.insert(key, value); }
					None => { self.inner.remove(&key); }
				}
			}
		}
	}

	fn place_child_storage(&mut self, storage_key: ChildStorageKey<H>, key: Vec<u8>, value: Option<Vec<u8>>) {
		self.changes.set_child_storage(storage_key.into_owned(), key, value);
	}

	fn kill_child_storage(&mut self, storage_key: ChildStorageKey<H>) {
		self.changes.clear_child_storage(storage_key.as_ref());
	}

	fn clear_prefix(&mut self, prefix: &[u8]) {
		self.changes.clear_prefix(prefix);
		self.inner.retain(|key, _| !key.starts_with(prefix));
	}

	fn chain_id(&self) -> u64 { 42 }

	fn storage_root(&mut self) -> H::Out {
		trie_root::<H, _, _, _>(self.inner.clone())
	}

	fn child_storage_root(&mut self, _storage_key: ChildStorageKey<H>) -> Vec<u8> {
		vec![]
	}

	fn storage_changes_root(&mut self, parent: H::Out, parent_num: u64) -> Option<H::Out> {
		compute_changes_trie_root::<_, _, H>(
			&InMemory::default(),
			Some(&self.changes_trie_storage),
			&self.changes,
			&AnchorBlockId { hash: parent, number: parent_num },
		).map(|(root, _)| root.clone())
	}

	fn submit_extrinsic(&mut self, _extrinsic: Vec<u8>) -> Result<(), ()> {
		unimplemented!()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use primitives::{Blake2Hasher, H256};
	use hex_literal::hex;

	#[test]
	fn commit_should_work() {
		let mut ext = TestExternalities::<Blake2Hasher>::default();
		ext.set_storage(b"doe".to_vec(), b"reindeer".to_vec());
		ext.set_storage(b"dog".to_vec(), b"puppy".to_vec());
		ext.set_storage(b"dogglesworth".to_vec(), b"cat".to_vec());
		const ROOT: [u8; 32] = hex!("0b33ed94e74e0f8e92a55923bece1ed02d16cf424e124613ddebc53ac3eeeabe");
		assert_eq!(ext.storage_root(), H256::from(ROOT));
	}

	#[test]
	fn set_and_retrieve_code() {
		let mut ext = TestExternalities::<Blake2Hasher>::default();

		let code = vec![1, 2, 3];
		ext.set_storage(CODE.to_vec(), code.clone());

		assert_eq!(&ext.storage(CODE).unwrap(), &code);
	}
}
