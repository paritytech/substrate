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
use std::cmp::Ord;
use super::Externalities;
use triehash::trie_root;
use hashdb::Hasher;
use rlp::Encodable;
use std::marker::PhantomData;
use std::iter::FromIterator;

/// Simple HashMap-based Externalities impl.
#[derive(Debug)]
pub struct TestExternalities<H> {
	inner: HashMap<Vec<u8>, Vec<u8>>,
	_hasher: PhantomData<H>,
}

impl<H: Hasher> TestExternalities<H> {
	/// Create a new instance of `TestExternalities`
	pub fn new() -> Self {
		TestExternalities {inner: HashMap::new(), _hasher: PhantomData}
	}
	/// Insert key/value
	pub fn insert(&mut self, k: Vec<u8>, v: Vec<u8>) -> Option<Vec<u8>> {
		self.inner.insert(k, v)
	}
}

impl<H: Hasher> PartialEq for TestExternalities<H> {
	fn eq(&self, other: &TestExternalities<H>) -> bool {
		self.inner.eq(&other.inner)
	}
}

impl<H: Hasher> FromIterator<(Vec<u8>, Vec<u8>)> for TestExternalities<H> {
	fn from_iter<I: IntoIterator<Item=(Vec<u8>, Vec<u8>)>>(iter: I) -> Self {
		let mut t = Self::new();
		for i in iter {
			t.inner.insert(i.0, i.1);
		}
		t
	}
}

impl<H: Hasher> Default for TestExternalities<H> {
	fn default() -> Self { Self::new() }
}

impl<H: Hasher> From<TestExternalities<H>> for HashMap<Vec<u8>, Vec<u8>> {
	fn from(tex: TestExternalities<H>) -> Self {
		tex.inner.into()
	}
}

impl<H: Hasher> From< HashMap<Vec<u8>, Vec<u8>> > for TestExternalities<H> {
	fn from(hashmap: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		TestExternalities { inner: hashmap, _hasher: PhantomData }
	}
}


impl<H: Hasher> Externalities<H> for TestExternalities<H> where H::Out: Ord + Encodable {
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.inner.get(key).map(|x| x.to_vec())
	}

	fn place_storage(&mut self, key: Vec<u8>, maybe_value: Option<Vec<u8>>) {
		match maybe_value {
			Some(value) => { self.inner.insert(key, value); }
			None => { self.inner.remove(&key); }
		}
	}

	fn clear_prefix(&mut self, prefix: &[u8]) {
		self.inner.retain(|key, _|
			!key.starts_with(prefix)
		)
	}

	fn chain_id(&self) -> u64 { 42 }

	fn storage_root(&mut self) -> H::Out {
		trie_root::<H, _, _, _>(self.inner.clone())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use primitives::{Blake2Hasher, H256};

	#[test]
	fn commit_should_work() {
		let mut ext = TestExternalities::<Blake2Hasher>::new();
		ext.set_storage(b"doe".to_vec(), b"reindeer".to_vec());
		ext.set_storage(b"dog".to_vec(), b"puppy".to_vec());
		ext.set_storage(b"dogglesworth".to_vec(), b"cat".to_vec());
		const ROOT: [u8; 32] = hex!("6ca394ff9b13d6690a51dea30b1b5c43108e52944d30b9095227c49bae03ff8b");
		assert_eq!(ext.storage_root(), H256(ROOT));
	}
}
