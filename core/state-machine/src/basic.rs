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
use hash_db::Hasher;
use trie::trie_root;
use primitives::storage::well_known_keys::{CHANGES_TRIE_CONFIG, CODE, HEAP_PAGES};
use parity_codec::Encode;
use super::{ChildStorageKey, Externalities, OverlayedChanges};
use log::warn;

/// Simple HashMap-based Externalities impl.
pub struct BasicExternalities {
	inner: HashMap<Vec<u8>, Vec<u8>>,
	changes: OverlayedChanges,
	code: Option<Vec<u8>>,
}

impl BasicExternalities {
	/// Create a new instance of `BasicExternalities`
	pub fn new(inner: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		Self::new_with_code(&[], inner)
	}

	/// Create a new instance of `BasicExternalities`
	pub fn new_with_code(code: &[u8], mut inner: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		let mut overlay = OverlayedChanges::default();
		super::set_changes_trie_config(
			&mut overlay,
			inner.get(&CHANGES_TRIE_CONFIG.to_vec()).cloned(),
			false,
		).expect("changes trie configuration is correct in test env; qed");

		inner.insert(HEAP_PAGES.to_vec(), 8u64.encode());

		BasicExternalities {
			inner,
			changes: overlay,
			code: Some(code.to_vec()),
		}
	}

	/// Insert key/value
	pub fn insert(&mut self, k: Vec<u8>, v: Vec<u8>) -> Option<Vec<u8>> {
		self.inner.insert(k, v)
	}
}

impl ::std::fmt::Debug for BasicExternalities {
	fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
		write!(f, "{:?}", self.inner)
	}
}

impl PartialEq for BasicExternalities {
	fn eq(&self, other: &BasicExternalities) -> bool {
		self.inner.eq(&other.inner)
	}
}

impl FromIterator<(Vec<u8>, Vec<u8>)> for BasicExternalities {
	fn from_iter<I: IntoIterator<Item=(Vec<u8>, Vec<u8>)>>(iter: I) -> Self {
		let mut t = Self::new(Default::default());
		t.inner.extend(iter);
		t
	}
}

impl Default for BasicExternalities {
	fn default() -> Self { Self::new(Default::default()) }
}

impl From<BasicExternalities> for HashMap<Vec<u8>, Vec<u8>> {
	fn from(tex: BasicExternalities) -> Self {
		tex.inner.into()
	}
}

impl From< HashMap<Vec<u8>, Vec<u8>> > for BasicExternalities {
	fn from(hashmap: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		BasicExternalities {
			inner: hashmap,
			changes: Default::default(),
			code: None,
		}
	}
}

impl<H: Hasher> Externalities<H> for BasicExternalities where H::Out: Ord {
	fn storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		match key {
			CODE => self.code.clone(),
			_ => self.inner.get(key).cloned(),
		}
	}

	fn original_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		Externalities::<H>::storage(self, key)
	}

	fn child_storage(&self, _storage_key: ChildStorageKey<H>, _key: &[u8]) -> Option<Vec<u8>> {
		None
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

	fn place_child_storage(&mut self, _storage_key: ChildStorageKey<H>, _key: Vec<u8>, _value: Option<Vec<u8>>) {
	}

	fn kill_child_storage(&mut self, _storage_key: ChildStorageKey<H>) { }

	fn clear_prefix(&mut self, prefix: &[u8]) {
		self.changes.clear_prefix(prefix);
		self.inner.retain(|key, _| !key.starts_with(prefix));
	}

	fn chain_id(&self) -> u64 { 42 }

	fn storage_root(&mut self) -> H::Out {
		trie_root::<H, _, _, _>(self.inner.clone())
	}

	fn child_storage_root(&mut self, _storage_key: ChildStorageKey<H>) -> Vec<u8> {
		vec![42]
	}

	fn storage_changes_root(&mut self, _parent: H::Out, _parent_num: u64) -> Option<H::Out> {
		None
	}

	fn submit_extrinsic(&mut self, _extrinsic: Vec<u8>) -> Result<(), ()> {
		warn!("Call to submit_extrinsic without offchain externalities set.");
		Err(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use primitives::{Blake2Hasher, H256};
	use hex_literal::hex;

	#[test]
	fn commit_should_work() {
		let mut ext = BasicExternalities::default();
		let ext = &mut ext as &mut Externalities<Blake2Hasher>;
		ext.set_storage(b"doe".to_vec(), b"reindeer".to_vec());
		ext.set_storage(b"dog".to_vec(), b"puppy".to_vec());
		ext.set_storage(b"dogglesworth".to_vec(), b"cat".to_vec());
		const ROOT: [u8; 32] = hex!("0b33ed94e74e0f8e92a55923bece1ed02d16cf424e124613ddebc53ac3eeeabe");
		assert_eq!(ext.storage_root(), H256::from(ROOT));
	}

	#[test]
	fn set_and_retrieve_code() {
		let mut ext = BasicExternalities::default();
		let ext = &mut ext as &mut Externalities<Blake2Hasher>;

		let code = vec![1, 2, 3];
		ext.set_storage(CODE.to_vec(), code.clone());

		assert_eq!(&ext.storage(CODE).unwrap(), &code);
	}
}
