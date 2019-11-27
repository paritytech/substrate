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

//! State machine in memory backend.

use crate::{trie_backend::TrieBackend, backend::{Backend, insert_into_memory_db}};
use std::{error, fmt, collections::HashMap, marker::PhantomData};
use hash_db::Hasher;
use trie::{
	MemoryDB, child_trie_root, default_child_trie_root, TrieConfiguration, trie_types::Layout,
};

/// Error impossible.
// FIXME: use `!` type when stabilized. https://github.com/rust-lang/rust/issues/35121
#[derive(Debug)]
pub enum Void {}

impl fmt::Display for Void {
	fn fmt(&self, _: &mut fmt::Formatter) -> fmt::Result {
		match *self {}
	}
}

impl error::Error for Void {
	fn description(&self) -> &str { "unreachable error" }
}

/// In-memory backend. Fully recomputes tries each time `as_trie_backend` is called but useful for
/// tests and proof checking.
pub struct InMemory<H: Hasher> {
	inner: HashMap<Option<Vec<u8>>, HashMap<Vec<u8>, Vec<u8>>>,
	// This field is only needed for returning reference in `as_trie_backend`.
	trie: Option<TrieBackend<MemoryDB<H>, H>>,
	_hasher: PhantomData<H>,
}

impl<H: Hasher> std::fmt::Debug for InMemory<H> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		write!(f, "InMemory ({} values)", self.inner.len())
	}
}

impl<H: Hasher> Default for InMemory<H> {
	fn default() -> Self {
		InMemory {
			inner: Default::default(),
			trie: None,
			_hasher: PhantomData,
		}
	}
}

impl<H: Hasher> Clone for InMemory<H> {
	fn clone(&self) -> Self {
		InMemory {
			inner: self.inner.clone(),
			trie: None,
			_hasher: PhantomData,
		}
	}
}

impl<H: Hasher> PartialEq for InMemory<H> {
	fn eq(&self, other: &Self) -> bool {
		self.inner.eq(&other.inner)
	}
}

impl<H: Hasher> InMemory<H> {
	/// Copy the state, with applied updates
	pub fn update<T: IntoIterator<Item = (Option<Vec<u8>>, Vec<u8>, Option<Vec<u8>>)>>(
		&self,
		changes: T,
	) -> Self {
		let mut inner: HashMap<_, _> = self.inner.clone();
		for (storage_key, key, val) in changes.into_iter() {
			match val {
				Some(v) => { inner.entry(storage_key).or_default().insert(key, v); },
				None => { inner.entry(storage_key).or_default().remove(&key); },
			}
		}

		inner.into()
	}
}

impl<H: Hasher> From<HashMap<Option<Vec<u8>>, HashMap<Vec<u8>, Vec<u8>>>> for InMemory<H> {
	fn from(inner: HashMap<Option<Vec<u8>>, HashMap<Vec<u8>, Vec<u8>>>) -> Self {
		InMemory {
			inner: inner,
			trie: None,
			_hasher: PhantomData,
		}
	}
}

impl<H: Hasher> From<(
		HashMap<Vec<u8>, Vec<u8>>,
		HashMap<Vec<u8>, HashMap<Vec<u8>, Vec<u8>>>,
)> for InMemory<H> {
	fn from(inners: (
		HashMap<Vec<u8>, Vec<u8>>,
		HashMap<Vec<u8>, HashMap<Vec<u8>, Vec<u8>>>,
	)) -> Self {
		let mut inner: HashMap<Option<Vec<u8>>, HashMap<Vec<u8>, Vec<u8>>>
			= inners.1.into_iter().map(|(k, v)| (Some(k), v)).collect();
		inner.insert(None, inners.0);
		InMemory {
			inner: inner,
			trie: None,
			_hasher: PhantomData,
		}
	}
}

impl<H: Hasher> From<HashMap<Vec<u8>, Vec<u8>>> for InMemory<H> {
	fn from(inner: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		let mut expanded = HashMap::new();
		expanded.insert(None, inner);
		InMemory {
			inner: expanded,
			trie: None,
			_hasher: PhantomData,
		}
	}
}

impl<H: Hasher> From<Vec<(Option<Vec<u8>>, Vec<u8>, Option<Vec<u8>>)>> for InMemory<H> {
	fn from(inner: Vec<(Option<Vec<u8>>, Vec<u8>, Option<Vec<u8>>)>) -> Self {
		let mut expanded: HashMap<Option<Vec<u8>>, HashMap<Vec<u8>, Vec<u8>>> = HashMap::new();
		for (child_key, key, value) in inner {
			if let Some(value) = value {
				expanded.entry(child_key).or_default().insert(key, value);
			}
		}
		expanded.into()
	}
}

impl<H: Hasher> InMemory<H> {
	/// child storage key iterator
	pub fn child_storage_keys(&self) -> impl Iterator<Item=&[u8]> {
		self.inner.iter().filter_map(|item| item.0.as_ref().map(|v|&v[..]))
	}
}

impl<H: Hasher> Backend<H> for InMemory<H> {
	type Error = Void;
	type Transaction = Vec<(Option<Vec<u8>>, Vec<u8>, Option<Vec<u8>>)>;
	type TrieBackendStorage = MemoryDB<H>;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		Ok(self.inner.get(&None).and_then(|map| map.get(key).map(Clone::clone)))
	}

	fn child_storage(
		&self,
		storage_key: &[u8],
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		Ok(
			self.inner
				.get(&Some(storage_key.to_vec()))
				.and_then(|map| map.get(key).map(Clone::clone))
		)
	}

	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		Ok(self.inner.get(&None).map(|map| map.get(key).is_some()).unwrap_or(false))
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.inner.get(&None)
			.map(|map| map.keys().filter(|key| key.starts_with(prefix)).map(|k| &**k).for_each(f));
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], mut f: F) {
		self.inner.get(&None).map(|map| map.iter().filter(|(key, _val)| key.starts_with(prefix))
			.for_each(|(k, v)| f(k, v)));
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(&self, storage_key: &[u8], mut f: F) {
		self.inner.get(&Some(storage_key.to_vec())).map(|map| map.keys().for_each(|k| f(&k)));
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(&self, storage_key: &[u8], prefix: &[u8], f: F) {
		self.inner.get(&Some(storage_key.to_vec()))
			.map(|map| map.keys().filter(|key| key.starts_with(prefix)).map(|k| &**k).for_each(f));
	}

	fn storage_root<I>(&self, delta: I) -> (H::Out, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		<H as Hasher>::Out: Ord,
	{
		let existing_pairs = self.inner.get(&None)
			.into_iter()
			.flat_map(|map| map.iter().map(|(k, v)| (k.clone(), Some(v.clone()))));

		let transaction: Vec<_> = delta.into_iter().collect();
		let root = Layout::<H>::trie_root(existing_pairs.chain(transaction.iter().cloned())
			.collect::<HashMap<_, _>>()
			.into_iter()
			.filter_map(|(k, maybe_val)| maybe_val.map(|val| (k, val)))
		);

		let transaction = transaction.into_iter().map(|(k, v)| (None, k, v)).collect();

		(root, transaction)
	}

	fn child_storage_root<I>(&self, storage_key: &[u8], delta: I) -> (Vec<u8>, bool, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		H::Out: Ord
	{
		let storage_key = storage_key.to_vec();

		let existing_pairs = self.inner.get(&Some(storage_key.clone()))
			.into_iter()
			.flat_map(|map| map.iter().map(|(k, v)| (k.clone(), Some(v.clone()))));

		let transaction: Vec<_> = delta.into_iter().collect();
		let root = child_trie_root::<Layout<H>, _, _, _>(
			&storage_key,
			existing_pairs.chain(transaction.iter().cloned())
				.collect::<HashMap<_, _>>()
				.into_iter()
				.filter_map(|(k, maybe_val)| maybe_val.map(|val| (k, val)))
		);

		let transaction = transaction.into_iter()
			.map(|(k, v)| (Some(storage_key.clone()), k, v))
			.collect();

		let is_default = root == default_child_trie_root::<Layout<H>>(&storage_key);

		(root, is_default, transaction)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.inner.get(&None)
			.into_iter()
			.flat_map(|map| map.iter().map(|(k, v)| (k.clone(), v.clone())))
			.collect()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.inner.get(&None)
			.into_iter()
			.flat_map(|map| map.keys().filter(|k| k.starts_with(prefix)).cloned())
			.collect()
	}

	fn child_keys(&self, storage_key: &[u8], prefix: &[u8]) -> Vec<Vec<u8>> {
		self.inner.get(&Some(storage_key.to_vec()))
			.into_iter()
			.flat_map(|map| map.keys().filter(|k| k.starts_with(prefix)).cloned())
			.collect()
	}

	fn as_trie_backend(&mut self)-> Option<&TrieBackend<Self::TrieBackendStorage, H>> {
		let mut mdb = MemoryDB::default();
		let mut new_child_roots = Vec::new();
		let mut root_map = None;
		for (storage_key, map) in &self.inner {
			if let Some(storage_key) = storage_key.as_ref() {
				let ch = insert_into_memory_db::<H, _>(&mut mdb, map.clone().into_iter())?;
				new_child_roots.push((storage_key.clone(), ch.as_ref().into()));
			} else {
				root_map = Some(map);
			}
		}
		let root = match root_map {
			Some(map) => insert_into_memory_db::<H, _>(
				&mut mdb,
				map.clone().into_iter().chain(new_child_roots.into_iter()),
			)?,
			None => insert_into_memory_db::<H, _>(
				&mut mdb,
				new_child_roots.into_iter(),
			)?,
		};

		self.trie = Some(TrieBackend::new(mdb, root));
		self.trie.as_ref()
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	/// Assert in memory backend with only child trie keys works as trie backend.
	#[test]
	fn in_memory_with_child_trie_only() {
		let storage = InMemory::<primitives::Blake2Hasher>::default();
		let mut storage = storage.update(
			vec![(Some(b"1".to_vec()), b"2".to_vec(), Some(b"3".to_vec()))]
		);
		let trie_backend = storage.as_trie_backend().unwrap();
		assert_eq!(trie_backend.child_storage(b"1", b"2").unwrap(), Some(b"3".to_vec()));
		assert!(trie_backend.storage(b"1").unwrap().is_some());
	}
}
