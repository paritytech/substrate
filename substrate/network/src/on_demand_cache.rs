// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

//! Cache for on-demand service responses.

use std::hash::Hash;
use heapsize::HeapSizeOf;
use linked_hash_map::LinkedHashMap;
use parking_lot::RwLock;
use client::CallResult;
use client::light::fetcher::{RemoteCallRequest, RemoteReadRequest};

/// Total cache memory limit.
const TOTAL_CACHE_LIMIT: usize = 1024 * 1024;

/// Cache for on-demand service responses.
pub struct OnDemandCache {
	remote_reads: RwLock<OnDemandCacheMap<RemoteReadRequest, Option<Vec<u8>>>>,
	remote_calls: RwLock<OnDemandCacheMap<RemoteCallRequest, CallResult>>,
}

/// Cache for single type of on-demand service responses.
#[derive(Default)]
struct OnDemandCacheMap<K: Hash + Eq + HeapSizeOf, V: Clone + HeapSizeOf> {
	mem_limit: usize,
	mem_occupied: usize,
	data: LinkedHashMap<K, V>,
}

impl OnDemandCache {
	/// Creat new cache.
	pub fn new() -> Self {
		OnDemandCache {
			remote_reads: RwLock::new(OnDemandCacheMap::new(TOTAL_CACHE_LIMIT / 2)),
			remote_calls: RwLock::new(OnDemandCacheMap::new(TOTAL_CACHE_LIMIT / 2)),
		}
	}

	/// Try to read remote read response from the cache.
	pub fn remote_read(&self, request: &RemoteReadRequest) -> Option<Option<Vec<u8>>> {
		self.remote_reads.read().get(request)
	}

	/// Try to read remote call response from the cache.
	pub fn remote_call(&self, request: &RemoteCallRequest) -> Option<CallResult> {
		self.remote_calls.read().get(request)
	}

	/// Cache remote read response.
	pub fn cache_remote_read(&self, request: RemoteReadRequest, response: Option<Vec<u8>>) {
		self.remote_reads.write().insert(request, response);
	}

	/// Cache remote call response.
	pub fn cache_remote_call(&self, request: RemoteCallRequest, response: CallResult) {
		self.remote_calls.write().insert(request, response);
	}
}

impl<K: Hash + Eq + HeapSizeOf, V: Clone + HeapSizeOf> OnDemandCacheMap<K, V> {
	/// Create new cache map with given memory limit.
	pub fn new(mem_limit: usize) -> Self {
		OnDemandCacheMap {
			mem_limit: mem_limit,
			mem_occupied: 0,
			data: LinkedHashMap::new(),
		}
	}

	/// Try to get response from the cache.
	pub fn get(&self, key: &K) -> Option<V> {
		self.data.get(key).cloned()
	}

	/// Insert response to the cache, reducing occupied memory below given limit.
	pub fn insert(&mut self, key: K, value: V) {
		let size = key.heap_size_of_children() + value.heap_size_of_children();
		if size > self.mem_limit {
			return;
		}

		self.data.insert(key, value);
		self.mem_occupied += size;
		while self.mem_occupied > self.mem_limit {
			let (key, value) = self.data.pop_front()
				.expect("cache entries are non-mutable; mem_occupied is non-zero; entry exists; qed");
			let size = key.heap_size_of_children() + value.heap_size_of_children();
			self.mem_occupied -= size;
		}
	}
}
