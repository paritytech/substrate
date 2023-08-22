// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! In-memory implementation of offchain workers database.

use crate::offchain::{DbExternalities, OffchainStorage, StorageKind, STORAGE_PREFIX};
use std::{
	collections::hash_map::{Entry, HashMap},
	iter::Iterator,
};

const LOG_TARGET: &str = "offchain-worker::storage";

/// In-memory storage for offchain workers.
#[derive(Debug, Clone, Default)]
pub struct InMemOffchainStorage {
	storage: HashMap<Vec<u8>, Vec<u8>>,
}

impl InMemOffchainStorage {
	/// Consume the offchain storage and iterate over all key value pairs.
	pub fn into_iter(self) -> impl Iterator<Item = (Vec<u8>, Vec<u8>)> {
		self.storage.into_iter()
	}

	/// Iterate over all key value pairs by reference.
	pub fn iter(&self) -> impl Iterator<Item = (&Vec<u8>, &Vec<u8>)> {
		self.storage.iter()
	}

	/// Remove a key and its associated value from the offchain database.
	pub fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
		self.storage.remove(&key);
	}
}

impl OffchainStorage for InMemOffchainStorage {
	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		let key = prefix.iter().chain(key).cloned().collect();
		self.storage.insert(key, value.to_vec());
	}

	fn remove(&mut self, prefix: &[u8], key: &[u8]) {
		let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
		self.storage.remove(&key);
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		let key: Vec<u8> = prefix.iter().chain(key).cloned().collect();
		self.storage.get(&key).cloned()
	}

	fn compare_and_set(
		&mut self,
		prefix: &[u8],
		key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		let key = prefix.iter().chain(key).cloned().collect();

		match self.storage.entry(key) {
			Entry::Vacant(entry) =>
				if old_value.is_none() {
					entry.insert(new_value.to_vec());
					true
				} else {
					false
				},
			Entry::Occupied(ref mut entry) if Some(entry.get().as_slice()) == old_value => {
				entry.insert(new_value.to_vec());
				true
			},
			_ => false,
		}
	}
}

fn unavailable_yet<R: Default>(name: &str) -> R {
	tracing::error!(
		target: LOG_TARGET,
		"The {:?} API is not available for offchain workers yet. Follow \
		https://github.com/paritytech/substrate/issues/1458 for details",
		name
	);
	Default::default()
}

const LOCAL_DB: &str = "LOCAL (fork-aware) DB";

/// Offchain DB that implements [`DbExternalities`] for [`OffchainStorage`].
#[derive(Debug, Clone)]
pub struct OffchainDb<Storage> {
	/// Persistent storage database.
	persistent: Storage,
}

impl<Storage> OffchainDb<Storage> {
	/// Create new instance of Offchain DB.
	pub fn new(persistent: Storage) -> Self {
		Self { persistent }
	}
}

impl<Storage: OffchainStorage> DbExternalities for OffchainDb<Storage> {
	fn local_storage_set(&mut self, kind: StorageKind, key: &[u8], value: &[u8]) {
		tracing::debug!(
			target: LOG_TARGET,
			?kind,
			key = ?array_bytes::bytes2hex("", key),
			value = ?array_bytes::bytes2hex("", value),
			"Write",
		);
		match kind {
			StorageKind::PERSISTENT => self.persistent.set(STORAGE_PREFIX, key, value),
			StorageKind::LOCAL => unavailable_yet(LOCAL_DB),
		}
	}

	fn local_storage_clear(&mut self, kind: StorageKind, key: &[u8]) {
		tracing::debug!(
			target: LOG_TARGET,
			?kind,
			key = ?array_bytes::bytes2hex("", key),
			"Clear",
		);
		match kind {
			StorageKind::PERSISTENT => self.persistent.remove(STORAGE_PREFIX, key),
			StorageKind::LOCAL => unavailable_yet(LOCAL_DB),
		}
	}

	fn local_storage_compare_and_set(
		&mut self,
		kind: StorageKind,
		key: &[u8],
		old_value: Option<&[u8]>,
		new_value: &[u8],
	) -> bool {
		tracing::debug!(
			target: LOG_TARGET,
			?kind,
			key = ?array_bytes::bytes2hex("", key),
			new_value = ?array_bytes::bytes2hex("", new_value),
			old_value = ?old_value.as_ref().map(|s| array_bytes::bytes2hex("", s)),
			"CAS",
		);
		match kind {
			StorageKind::PERSISTENT =>
				self.persistent.compare_and_set(STORAGE_PREFIX, key, old_value, new_value),
			StorageKind::LOCAL => unavailable_yet(LOCAL_DB),
		}
	}

	fn local_storage_get(&mut self, kind: StorageKind, key: &[u8]) -> Option<Vec<u8>> {
		let result = match kind {
			StorageKind::PERSISTENT => self.persistent.get(STORAGE_PREFIX, key),
			StorageKind::LOCAL => unavailable_yet(LOCAL_DB),
		};
		tracing::debug!(
			target: LOG_TARGET,
			?kind,
			key = ?array_bytes::bytes2hex("", key),
			result = ?result.as_ref().map(|s| array_bytes::bytes2hex("", s)),
			"Read",
		);
		result
	}
}
