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

//! State machine backends. These manage the code and storage of contracts.

use std::{error, fmt};
use std::cmp::Ord;
use std::collections::HashMap;
use std::marker::PhantomData;
use log::warn;
use hash_db::Hasher;
use crate::trie_backend::TrieBackend;
use crate::trie_backend_essence::TrieBackendStorage;
use trie::{TrieDBMut, TrieMut, MemoryDB, trie_root, child_trie_root, default_child_trie_root,
	KeySpacedDBMut};
use primitives::subtrie::{KeySpace, SubTrie, SubTrieReadRef};

// TODO EMCH Option<KeySpace> is bad for ref : TODO keyspace size 0 for root
/// type alias over a in memory transaction storring struct
pub type MapTransaction = HashMap<Option<KeySpace>, (HashMap<Vec<u8>, Vec<u8>>, Option<SubTrie>)>;

/// type alias over a list of in memory changes TODO EMCH highly redundant SubTrie to remove
pub type VecTransaction = Vec<(Option<SubTrie>, Vec<u8>, Option<Vec<u8>>)>;


/// A state backend is used to read state data and can have changes committed
/// to it.
///
/// The clone operation (if implemented) should be cheap.
pub trait Backend<H: Hasher> {
	/// An error type when fetching data is not possible.
	type Error: super::Error;

	/// Storage changes to be applied if committing
	type Transaction: Consolidate + Default;

	/// Type of trie backend storage.
	type TrieBackendStorage: TrieBackendStorage<H>;

	/// Get keyed storage or None if there is nothing associated.
	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error>;

	/// Get keyed storage value hash or None if there is nothing associated.
	fn storage_hash(&self, key: &[u8]) -> Result<Option<H::Out>, Self::Error> {
		self.storage(key).map(|v| v.map(|v| H::hash(&v)))
	}

	/// get SubTrie information
	fn child_trie(&self, storage_key: &[u8]) -> Result<Option<SubTrie>, Self::Error> {
		let prefixed_key = SubTrie::prefix_parent_key(storage_key);
		Ok(self.storage(&prefixed_key)?
			.and_then(|n|SubTrie::decode_node_prefixed_parent(&n[..], prefixed_key)))
	}

	/// Get keyed child storage or None if there is nothing associated.
	fn child_storage(&self, subtrie: SubTrieReadRef, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error>;

	/// true if a key exists in storage.
	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		Ok(self.storage(key)?.is_some())
	}

	/// true if a key exists in child storage.
	fn exists_child_storage(&self, subtrie: SubTrieReadRef, key: &[u8]) -> Result<bool, Self::Error> {
		Ok(self.child_storage(subtrie, key)?.is_some())
	}

	/// Retrieve all entries keys of child storage and call `f` for each of those keys.
	fn for_keys_in_child_storage<F: FnMut(&[u8])>(&self, subtrie: SubTrieReadRef, f: F);

	/// Retrieve all entries keys of which start with the given prefix and
	/// call `f` for each of those keys.
	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F);

	/// Calculate the storage root, with given delta over what is already stored in
	/// the backend, and produce a "transaction" that can be used to commit.
	/// Does not include child storage updates.
	fn storage_root<I>(&self, delta: I) -> (H::Out, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		H::Out: Ord;

	/// Calculate the child storage root, with given delta over what is already stored in
	/// the backend, and produce a "transaction" that can be used to commit. The second argument
	/// is true if child storage root equals default storage root.
	fn child_storage_root<I>(&self, subtrie: &SubTrie, delta: I) -> (Vec<u8>, bool, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		H::Out: Ord;

	/// Get all key/value pairs into a Vec.
	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)>;

	/// Get all keys with given prefix
	fn keys(&self, prefix: &Vec<u8>) -> Vec<Vec<u8>>;

	/// Try convert into trie backend.
	fn try_into_trie_backend(self) -> Option<TrieBackend<Self::TrieBackendStorage, H>>;

	/// Calculate the storage root, with given delta over what is already stored
	/// in the backend, and produce a "transaction" that can be used to commit.
	/// Does include child storage updates.
	fn full_storage_root<I1, I2i, I2, TR>(
		&self,
		delta: I1,
		child_deltas: I2)
	-> (H::Out, Self::Transaction)
	where
		I1: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		I2i: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		TR: AsRef<SubTrie>,
		I2: IntoIterator<Item=(TR, I2i)>,
		<H as Hasher>::Out: Ord,
	{
		let mut txs: Self::Transaction = Default::default();
		let mut child_roots: Vec<_> = Default::default();
		// child first
		for (subtrie, child_delta) in child_deltas {
			let (child_root, empty, child_txs) =
				self.child_storage_root(subtrie.as_ref(), child_delta);
			txs.consolidate(child_txs);
			if empty {
				child_roots.push((subtrie.as_ref().parent_prefixed_key().to_vec(), None));
			} else {
				child_roots.push(
					(subtrie.as_ref().parent_prefixed_key().to_vec(),
					Some(subtrie.as_ref().encoded_with_root(&child_root[..])))
				);
			}
		}
		let (root, parent_txs) = self.storage_root(
			delta.into_iter().chain(child_roots.into_iter())
		);
		txs.consolidate(parent_txs);
		(root, txs)
	}

}

/// Trait that allows consolidate two transactions together.
pub trait Consolidate {
	/// Consolidate two transactions into one.
	fn consolidate(&mut self, other: Self);
}

impl Consolidate for () {
	fn consolidate(&mut self, _: Self) {
		()
	}
}

impl Consolidate for VecTransaction {
	fn consolidate(&mut self, mut other: Self) {
		self.append(&mut other);
	}
}

impl<H: Hasher, KF: trie::KeyFunction<H>> Consolidate for trie::GenericMemoryDB<H, KF> {
	fn consolidate(&mut self, other: Self) {
		trie::GenericMemoryDB::consolidate(self, other)
	}
}

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

/// In-memory backend. Fully recomputes tries on each commit but useful for
/// tests.
#[derive(Eq)]
pub struct InMemory<H> {
	inner: MapTransaction,
	_hasher: PhantomData<H>,
}

impl<H> Default for InMemory<H> {
	fn default() -> Self {
		InMemory {
			inner: Default::default(),
			_hasher: PhantomData,
		}
	}
}

impl<H> Clone for InMemory<H> {
	fn clone(&self) -> Self {
		InMemory {
			inner: self.inner.clone(),
			_hasher: PhantomData,
		}
	}
}

impl<H> PartialEq for InMemory<H> {
	fn eq(&self, other: &Self) -> bool {
		self.inner.eq(&other.inner)
	}
}

impl<H: Hasher> InMemory<H> {
	/// Copy the state, with applied updates
	pub fn update(&self, changes: <Self as Backend<H>>::Transaction) -> Self {
		// costy clone
		let mut inner: HashMap<_, _> = self.inner.clone();
		for (subtrie, key, val) in changes {
			match val {
				Some(v) => {
					let mut entry = inner.entry(subtrie.as_ref().map(|s|s.keyspace().clone()))
						.or_insert_with(||(Default::default(), subtrie.clone()));
					entry.0.insert(key, v);
					// very costy clone
					entry.1 = subtrie.as_ref().cloned();
				},
				None => {
					inner.entry(subtrie.as_ref().map(|s|s.keyspace().clone()))
						.or_insert_with(||(Default::default(), subtrie.clone()))
						.0.remove(&key);
				},
			}
		}

		inner.into()
	}
}

impl<H> From<MapTransaction> for InMemory<H> {
	fn from(inner: MapTransaction) -> Self {
		InMemory {
			inner: inner,
			_hasher: PhantomData,
		}
	}
}

impl<H> From<HashMap<Vec<u8>, Vec<u8>>> for InMemory<H> {
	fn from(inner: HashMap<Vec<u8>, Vec<u8>>) -> Self {
		let mut expanded = HashMap::new();
		expanded.insert(None, (inner, None));
		InMemory {
			inner: expanded,
			_hasher: PhantomData,
		}
	}
}

impl<H> From<VecTransaction> for InMemory<H> {
	fn from(inner: VecTransaction) -> Self {
		let mut expanded: MapTransaction = HashMap::new();
		for (child_key, key, value) in inner {
			if let Some(value) = value {
				let mut entry = expanded.entry(child_key.as_ref().map(|s|s.keyspace().clone()))
					.or_insert_with(||(Default::default(), child_key.clone()));
				entry.0.insert(key, value);
				entry.1 = child_key;
			}
		}
		expanded.into()
	}
}

impl super::Error for Void {}

#[cfg(test)]
impl<H: Hasher> InMemory<H> {
	/// child subtrie iterator
	pub fn child_storage_subtrie(&self) -> impl Iterator<Item=&SubTrie> {
		self.inner.iter().filter_map(|item| (item.1).1.as_ref())
	}
}

impl<H: Hasher> Backend<H> for InMemory<H> {
	type Error = Void;
	type Transaction = VecTransaction;
	type TrieBackendStorage = MemoryDB<H>;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		Ok(self.inner.get(&None).and_then(|map| map.0.get(key).map(Clone::clone)))
	}

	fn child_storage(&self, subtrie: SubTrieReadRef, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		Ok(self.inner.get(&Some(subtrie.keyspace.to_vec())).and_then(|map| map.0.get(key).map(Clone::clone)))
	}

	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		Ok(self.inner.get(&None).map(|map| map.0.get(key).is_some()).unwrap_or(false))
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.inner.get(&None).map(|map| map.0.keys().filter(|key| key.starts_with(prefix)).map(|k| &**k).for_each(f));
	}

	fn for_keys_in_child_storage<F: FnMut(&[u8])>(&self, subtrie: SubTrieReadRef, mut f: F) {
		self.inner.get(&Some(subtrie.keyspace.clone())).map(|map| map.0.keys().for_each(|k| f(&k)));
	}

	fn storage_root<I>(&self, delta: I) -> (H::Out, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		<H as Hasher>::Out: Ord,
	{
		let existing_pairs = self.inner.get(&None).into_iter().flat_map(|map| map.0.iter().map(|(k, v)| (k.clone(), Some(v.clone()))));
		let transaction: Vec<_> = delta.into_iter().collect();
		let map_input = existing_pairs.chain(transaction.iter().cloned())
			.collect::<HashMap<_, _>>();

		let root = trie_root::<H, _, _, _>(map_input
			.into_iter()
			.filter_map(|(k, maybe_val)| maybe_val.map(|val| (k, val)))
		);

		let full_transaction = transaction.into_iter().map(|(k, v)| (None, k, v)).collect();

		(root, full_transaction)
	}

	fn child_storage_root<I>(&self, subtrie: &SubTrie, delta: I) -> (Vec<u8>, bool, Self::Transaction)
	where
		I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		H::Out: Ord
	{
		// costy clone
		let existing_pairs = self.inner.get(&Some(subtrie.keyspace().clone())).into_iter().flat_map(|map| map.0.iter().map(|(k, v)| (k.clone(), Some(v.clone()))));

		let transaction: Vec<_> = delta.into_iter().collect();
		let root = child_trie_root::<H, _, _, _>(
			existing_pairs.chain(transaction.iter().cloned())
				.collect::<HashMap<_, _>>()
				.into_iter()
				.filter_map(|(k, maybe_val)| maybe_val.map(|val| (k, val)))
		);

		let full_transaction = transaction.into_iter().map(|(k, v)| (Some(subtrie.clone()), k, v)).collect();

		let is_default = root == default_child_trie_root::<H>();

		(root, is_default, full_transaction)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.inner.get(&None).into_iter().flat_map(|map| map.0.iter().map(|(k, v)| (k.clone(), v.clone()))).collect()
	}

	fn keys(&self, prefix: &Vec<u8>) -> Vec<Vec<u8>> {
		self.inner.get(&None).into_iter().flat_map(|map| map.0.keys().filter(|k| k.starts_with(prefix)).cloned()).collect()
	}

	fn try_into_trie_backend(
		self
	)-> Option<TrieBackend<Self::TrieBackendStorage, H>> {
		let mut mdb = MemoryDB::default();
		let mut root = None;
		let mut new_child_roots = Vec::new();
		let mut root_map = None;
		for (_o_keyspace, (map, o_subtrie)) in self.inner {
			if o_subtrie.is_some() {
				let ch = insert_into_memory_db::<H, _>(
					&mut mdb, map.into_iter(),
					o_subtrie.as_ref().map(|s|s.node_ref())
				)?;
				new_child_roots.push(
					o_subtrie.as_ref().map(|s|(
						s.parent_prefixed_key().to_vec(),
						s.encoded_with_root(ch.as_ref()))
					).expect("is_some previously checked;qed"),
				);
			} else {
				root_map = Some(map);
			}
		}
		// root handling
		if let Some(map) = root_map.take() {
			root = Some(insert_into_memory_db::<H, _>(
				&mut mdb,
				map.into_iter().chain(new_child_roots.into_iter()),
				None
			)?);
		}
		let root = match root {
			Some(root) => root,
			None => insert_into_memory_db::<H, _>(&mut mdb, ::std::iter::empty(), None)?,
		};
		Some(TrieBackend::new(mdb, root))
	}
}

/// Insert input pairs into memory db.
pub(crate) fn insert_into_memory_db<H, I>(mdb: &mut MemoryDB<H>, input: I, subtrie: Option<SubTrieReadRef>) -> Option<H::Out>
	where
		H: Hasher,
		I: IntoIterator<Item=(Vec<u8>, Vec<u8>)>,
{
	let mut root = <H as Hasher>::Out::default();
	{
		if let Some(subtrie) = subtrie.as_ref() {
			let mut mdb = KeySpacedDBMut::new(&mut *mdb, subtrie.keyspace);
			let mut trie = TrieDBMut::<H>::new(&mut mdb, &mut root);
			for (key, value) in input {
				if let Err(e) = trie.insert(&key, &value) {
					warn!(target: "trie", "Failed to write to trie: {}", e);
					return None;
				}
			}
		} else {
			let mut trie = TrieDBMut::<H>::new(mdb, &mut root);
			for (key, value) in input {
				if let Err(e) = trie.insert(&key, &value) {
					warn!(target: "trie", "Failed to write to trie: {}", e);
					return None;
				}
			}
		}
	}

	Some(root)
}
