// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::Layout;
use hash_db::Hasher;
use parking_lot::{MappedRwLockWriteGuard, Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::{
	collections::{hash_map::Entry, HashMap},
	sync::Arc,
};
use trie_db::{node::NodeOwned, Bytes, CError};

#[derive(Clone)]
pub struct SharedTrieNodeCache<H: Hasher> {
	node_cache: Arc<RwLock<HashMap<H::Out, NodeOwned<H::Out>>>>,
	data_cache: Arc<RwLock<HashMap<H::Out, HashMap<Vec<u8>, Option<Bytes>>>>>,
}

impl<H: Hasher> Default for SharedTrieNodeCache<H> {
	fn default() -> Self {
		Self { node_cache: Default::default(), data_cache: Default::default() }
	}
}

pub struct LocalTrieNodeCache<H: Hasher> {
	shared: SharedTrieNodeCache<H>,
	local: Mutex<HashMap<H::Out, NodeOwned<H::Out>>>,
	enable_data_cache: bool,
}

impl<H: Hasher> LocalTrieNodeCache<H> {
	pub fn new(shared: SharedTrieNodeCache<H>, enable_fast_cache: bool) -> Self {
		Self { enable_data_cache: enable_fast_cache, local: Default::default(), shared }
	}

	pub fn as_cache<'a>(&'a self, hash: H::Out) -> TrieNodeCache<'a, H> {
		TrieNodeCache {
			shared_cache: self.shared.node_cache.read(),
			local_cache: self.local.lock(),
			data_cache: RwLockWriteGuard::map(self.shared.data_cache.write(), |cache| {
				cache.entry(hash).or_default()
			}),
			enable_data_cache: self.enable_data_cache,
		}
	}
}

impl<H: Hasher> Drop for LocalTrieNodeCache<H> {
	fn drop(&mut self) {
		let mut shared = self.shared.node_cache.write();
		shared.extend(self.local.lock().drain());
	}
}

pub struct TrieNodeCache<'a, H: Hasher> {
	shared_cache: RwLockReadGuard<'a, HashMap<H::Out, NodeOwned<H::Out>>>,
	local_cache: MutexGuard<'a, HashMap<H::Out, NodeOwned<H::Out>>>,
	enable_data_cache: bool,
	data_cache: MappedRwLockWriteGuard<'a, HashMap<Vec<u8>, Option<Bytes>>>,
}

impl<'a, H: Hasher> trie_db::TrieCache<Layout<H>> for TrieNodeCache<'a, H> {
	fn get_or_insert_node(
		&mut self,
		hash: H::Out,
		fetch_node: &mut dyn FnMut() -> trie_db::Result<
			NodeOwned<H::Out>,
			H::Out,
			CError<Layout<H>>,
		>,
	) -> trie_db::Result<&NodeOwned<H::Out>, H::Out, CError<Layout<H>>> {
		if let Some(res) = self.shared_cache.get(&hash) {
			return Ok(res)
		}

		match self.local_cache.entry(hash) {
			Entry::Occupied(res) => Ok(res.into_mut()),
			Entry::Vacant(vacant) => {
				let node = (*fetch_node)()?;
				Ok(vacant.insert(node))
			},
		}
	}

	fn insert_node(&mut self, hash: H::Out, node: NodeOwned<H::Out>) {
		self.local_cache.insert(hash, node);
	}

	fn get_node(&mut self, hash: &H::Out) -> Option<&NodeOwned<H::Out>> {
		if let Some(node) = self.shared_cache.get(hash) {
			return Some(node)
		}

		self.local_cache.get(hash)
	}

	fn lookup_data_for_key(&self, key: &[u8]) -> Option<&Option<Bytes>> {
		self.enable_data_cache.then(|| self.data_cache.get(key)).flatten()
	}

	fn cache_data_for_key(&mut self, key: &[u8], data: Option<Bytes>) {
		if self.enable_data_cache {
			self.data_cache.insert(key.into(), data);
		}
	}
}
