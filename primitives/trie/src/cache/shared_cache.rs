// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

///! Provides the [`SharedNodeCache`], the [`SharedValueCache`] and the [`SharedTrieCache`]
///! that combines both caches and is exported to the outside.
use super::{CacheSize, LOG_TARGET};
use hash_db::Hasher;
use hashbrown::{hash_set::Entry as SetEntry, HashSet};
use lru::LruCache;
use parking_lot::RwLock;
use std::{mem, sync::Arc};
use trie_db::{node::NodeOwned, CachedValue};

/// The shared node cache.
///
/// Internally this stores all cached nodes in a [`LruCache`]. It ensures that when updating the
/// cache, that the cache stays within its allowed bounds.
pub(super) struct SharedNodeCache<H: Hasher> {
	/// The cached nodes, ordered by least recently used.
	pub(super) lru: LruCache<H::Out, NodeOwned<H::Out>>,
	/// The size of [`Self::lru`] in bytes.
	pub(super) size_in_bytes: usize,
	/// The maximum cache size of [`Self::lru`].
	maximum_cache_size: CacheSize,
}

impl<H: Hasher> SharedNodeCache<H> {
	/// Create a new instance.
	fn new(cache_size: CacheSize) -> Self {
		Self { lru: LruCache::unbounded(), size_in_bytes: 0, maximum_cache_size: cache_size }
	}

	/// Get the node for `key`.
	///
	/// This doesn't change the least recently order in the internal [`LruCache`].
	pub fn get(&self, key: &H::Out) -> Option<&NodeOwned<H::Out>> {
		self.lru.peek(key)
	}

	/// Update the cache with the `added` nodes and the `accessed` nodes.
	///
	/// The `added` nodes are the ones that have been collected by doing operations on the trie and
	/// now should be stored in the shared cache. The `accessed` nodes are only referenced by hash
	/// and represent the nodes that were retrieved from this shared cache through [`Self::get`].
	/// These `accessed` nodes are being put to the front of the internal [`LruCache`] like the
	/// `added` ones.
	///
	/// After the internal [`LruCache`] was updated, it is ensured that the internal [`LruCache`] is
	/// inside its bounds ([`Self::maximum_size_in_bytes`]).
	pub fn update(
		&mut self,
		added: impl IntoIterator<Item = (H::Out, NodeOwned<H::Out>)>,
		accessed: impl IntoIterator<Item = H::Out>,
	) {
		let update_size_in_bytes =
			|size_in_bytes: &mut usize, key: &H::Out, node: &NodeOwned<H::Out>| {
				if let Some(new_size_in_bytes) =
					size_in_bytes.checked_sub(key.as_ref().len() + node.size_in_bytes())
				{
					*size_in_bytes = new_size_in_bytes;
				} else {
					*size_in_bytes = 0;
					tracing::error!(target: LOG_TARGET, "`SharedNodeCache` underflow detected!",);
				}
			};

		accessed.into_iter().for_each(|key| {
			// Access every node in the lru to put it to the front.
			self.lru.get(&key);
		});
		added.into_iter().for_each(|(key, node)| {
			self.size_in_bytes += key.as_ref().len() + node.size_in_bytes();

			if let Some((r_key, r_node)) = self.lru.push(key, node) {
				update_size_in_bytes(&mut self.size_in_bytes, &r_key, &r_node);
			}

			// Directly ensure that we respect the maximum size. By doing it directly here we ensure
			// that the internal map of the [`LruCache`] doesn't grow too much.
			while self.maximum_cache_size.exceeds(self.size_in_bytes) {
				// This should always be `Some(_)`, otherwise something is wrong!
				if let Some((key, node)) = self.lru.pop_lru() {
					update_size_in_bytes(&mut self.size_in_bytes, &key, &node);
				}
			}
		});
	}

	/// Reset the cache.
	fn reset(&mut self) {
		self.size_in_bytes = 0;
		self.lru.clear();
	}
}

/// The key type that is being used to uniquely address a [`CachedValue`].
///
/// This type is implemented as enum to work around some limitations of the [`LruCache`] api
/// when it comes to `peek`ing into the structure. Given current stable rust you can not implement
/// `Borrow` properly for their wrapper type. For still supporting to `peek` into the [`LruCache`]
/// that stores the [`CachedValue`]s without allocating an [`Arc<[u8]>`] this type has the `Ref`
/// variant. We implement [`PartialEq`] and [`Hash`] manually to ensure that both variants can
/// point to the same value as long as `storage_root` and `storage_hash` are equal.
#[derive(Clone, Eq)]
pub(super) enum ValueCacheKey<'a, H> {
	/// Variant that stores the `storage_key` by value.
	Value {
		/// The storage root of the trie this key belongs to.
		storage_root: H,
		/// The key to access the value in the storage.
		storage_key: Arc<[u8]>,
	},
	/// Variant that only references the `storage_key`.
	Ref {
		/// The storage root of the trie this key belongs to.
		storage_root: H,
		/// The key to access the value in the storage.
		storage_key: &'a [u8],
	},
}

impl<H> ValueCacheKey<'_, H> {
	/// Convert `self` into `Self::Value`
	pub fn into_value(self) -> ValueCacheKey<'static, H>
	where
		H: Clone,
	{
		match self {
			Self::Value { storage_root, storage_key } =>
				ValueCacheKey::Value { storage_root, storage_key },
			Self::Ref { storage_root, storage_key } => ValueCacheKey::Value {
				storage_root: storage_root.clone(),
				storage_key: storage_key.into(),
			},
		}
	}

	/// Returns the stored storage root.
	pub fn storage_root(&self) -> &H {
		match self {
			Self::Ref { storage_root, .. } => storage_root,
			Self::Value { storage_root, .. } => storage_root,
		}
	}

	/// Returns the stored storage key.
	pub fn storage_key(&self) -> &[u8] {
		match self {
			Self::Ref { storage_key, .. } => &storage_key,
			Self::Value { storage_key, .. } => &*storage_key,
		}
	}
}

// Implement manually to ensure that the `Value` and `Ref` are treated equally.
impl<H: std::hash::Hash> std::hash::Hash for ValueCacheKey<'_, H> {
	fn hash<Hasher: std::hash::Hasher>(&self, state: &mut Hasher) {
		match self {
			Self::Ref { storage_root, storage_key } => {
				storage_root.hash(state);
				storage_key.hash(state);
			},
			Self::Value { storage_root, storage_key } => {
				storage_root.hash(state);
				storage_key.hash(state);
			},
		}
	}
}

// Implement manually to ensure that the `Value` and `Ref` are treated equally.
impl<H: PartialEq> PartialEq for ValueCacheKey<'_, H> {
	fn eq(&self, other: &Self) -> bool {
		self.storage_root() == other.storage_root() && self.storage_key() == other.storage_key()
	}
}

/// The shared value cache.
///
/// The cache ensures that it stays in the configured size bounds.
pub(super) struct SharedValueCache<H> {
	/// The cached nodes, ordered by least recently used.
	pub(super) lru: LruCache<ValueCacheKey<'static, H>, CachedValue<H>>,
	/// The size of [`Self::lru`] in bytes.
	pub(super) size_in_bytes: usize,
	/// The maximum cache size of [`Self::lru`].
	maximum_cache_size: CacheSize,
	/// All known storage keys that are stored in [`Self::lru`].
	///
	/// This is used to de-duplicate keys in memory that use the
	/// same [`SharedValueCache::storage_key`], but have a different
	/// [`SharedValueCache::storage_root`].
	known_storage_keys: HashSet<Arc<[u8]>>,
}

impl<H: Eq + std::hash::Hash + Clone + Copy> SharedValueCache<H> {
	/// Create a new instance.
	fn new(cache_size: CacheSize) -> Self {
		Self {
			lru: LruCache::unbounded(),
			size_in_bytes: 0,
			maximum_cache_size: cache_size,
			known_storage_keys: Default::default(),
		}
	}

	/// Get the [`CachedValue`] for `key`.
	///
	/// This doesn't change the least recently order in the internal [`LruCache`].
	pub fn get<'a>(&'a self, key: &ValueCacheKey<H>) -> Option<&'a CachedValue<H>> {
		self.lru.peek(unsafe {
			// SAFETY
			//
			// We need to convert the lifetime to make the compiler happy. However, as
			// we only use the `key` to looking up the value this lifetime conversion is
			// safe.
			mem::transmute::<&ValueCacheKey<'_, H>, &ValueCacheKey<'static, H>>(key)
		})
	}

	/// Update the cache with the `added` values and the `accessed` values.
	///
	/// The `added` values are the ones that have been collected by doing operations on the trie and
	/// now should be stored in the shared cache. The `accessed` values are only referenced by the
	/// [`SharedValueCacheKey`] and represent the values that were retrieved from this shared cache
	/// through [`Self::get`]. These `accessed` values are being put to the front of the internal
	/// [`LruCache`] like the `added` ones.
	///
	/// After the internal [`LruCache`] was updated, it is ensured that the internal [`LruCache`] is
	/// inside its bounds ([`Self::maximum_size_in_bytes`]).
	pub fn update(
		&mut self,
		added: impl IntoIterator<Item = (ValueCacheKey<'static, H>, CachedValue<H>)>,
		accessed: impl IntoIterator<Item = ValueCacheKey<'static, H>>,
	) {
		// The base size in memory per ([`SharedValueCacheKey<H>`], [`CachedValue`]).
		let base_size = mem::size_of::<ValueCacheKey<H>>() + mem::size_of::<CachedValue<H>>();
		let known_keys_entry_size = mem::size_of::<Arc<[u8]>>();

		let update_size_in_bytes =
			|size_in_bytes: &mut usize, r_key: Arc<[u8]>, known_keys: &mut HashSet<Arc<[u8]>>| {
				// If the `strong_count == 2`, it means this is the last instance of the key.
				// One being `r_key` and the other being stored in `keys`.
				let last_instance = Arc::strong_count(&r_key) == 2;

				let key_len = if last_instance {
					known_keys.remove(&r_key);
					r_key.len() + known_keys_entry_size
				} else {
					// The key is still in `keys`, because it is still used by another
					// `SharedValueCacheKey<H>`.
					0
				};

				if let Some(new_size_in_bytes) = size_in_bytes.checked_sub(key_len + base_size) {
					*size_in_bytes = new_size_in_bytes;
				} else {
					*size_in_bytes = 0;
					tracing::error!(target: LOG_TARGET, "`SharedValueCache` underflow detected!",);
				}
			};

		accessed.into_iter().for_each(|key| {
			// Access every node in the lru to put it to the front.
			self.lru.get(&key);
		});

		added.into_iter().for_each(|(key, value)| {
			let (storage_root, storage_key) = match key.into_value() {
				ValueCacheKey::Ref { .. } =>
					unreachable!("We just converted the `ValueCacheKey` into a `Value`; qed"),
				ValueCacheKey::Value { storage_root, storage_key } => (storage_root, storage_key),
			};

			let (size_update, storage_key) =
				match self.known_storage_keys.entry(storage_key.clone()) {
					SetEntry::Vacant(v) => {
						let len = v.get().len();
						v.insert();

						// If the key was unknown, we need to also take its length and the size of
						// the entry of `known_keys` into account.
						(len + base_size + known_keys_entry_size, storage_key)
					},
					SetEntry::Occupied(o) => {
						// Key is known
						(base_size, o.get().clone())
					},
				};

			self.size_in_bytes += size_update;

			if let Some((r_key, _)) =
				self.lru.push(ValueCacheKey::Value { storage_root, storage_key }, value)
			{
				if let ValueCacheKey::Value { storage_key, .. } = r_key {
					update_size_in_bytes(
						&mut self.size_in_bytes,
						storage_key,
						&mut self.known_storage_keys,
					);
				}
			}

			// Directly ensure that we respect the maximum size. By doing it directly here we
			// ensure that the internal map of the [`LruCache`] doesn't grow too much.
			while self.maximum_cache_size.exceeds(self.size_in_bytes) {
				// This should always be `Some(_)`, otherwise something is wrong!
				if let Some((r_key, _)) = self.lru.pop_lru() {
					if let ValueCacheKey::Value { storage_key, .. } = r_key {
						update_size_in_bytes(
							&mut self.size_in_bytes,
							storage_key,
							&mut self.known_storage_keys,
						);
					}
				}
			}
		});
	}

	/// Reset the cache.
	fn reset(&mut self) {
		self.size_in_bytes = 0;
		self.lru.clear();
		self.known_storage_keys.clear();
	}
}

/// The shared trie cache.
///
/// It should be instantiated once per node. It will hold the trie nodes and values of all
/// operations to the state. To not use all available memory it will ensure to stay in the
/// bounds given via the [`CacheSize`] at startup.
///
/// The instance of this object can be shared between multiple threads.
pub struct SharedTrieCache<H: Hasher> {
	pub(super) node_cache: Arc<RwLock<SharedNodeCache<H>>>,
	pub(super) value_cache: Arc<RwLock<SharedValueCache<H::Out>>>,
}

impl<H: Hasher> Clone for SharedTrieCache<H> {
	fn clone(&self) -> Self {
		Self { node_cache: self.node_cache.clone(), value_cache: self.value_cache.clone() }
	}
}

impl<H: Hasher> SharedTrieCache<H> {
	/// Create a new [`SharedTrieCache`].
	pub fn new(cache_size: CacheSize) -> Self {
		let (node_cache_size, value_cache_size) = match cache_size {
			CacheSize::Maximum(max) => {
				// Allocate 20% for the value cache.
				let value_cache_size_in_bytes = (max as f32 * 0.20) as usize;

				(
					CacheSize::Maximum(max - value_cache_size_in_bytes),
					CacheSize::Maximum(value_cache_size_in_bytes),
				)
			},
			CacheSize::Unlimited => (CacheSize::Unlimited, CacheSize::Unlimited),
		};

		Self {
			node_cache: Arc::new(RwLock::new(SharedNodeCache::new(node_cache_size))),
			value_cache: Arc::new(RwLock::new(SharedValueCache::new(value_cache_size))),
		}
	}

	/// Create a new [`LocalTrieCache`] instance from this shared cache.
	pub fn local_cache(&self) -> super::LocalTrieCache<H> {
		super::LocalTrieCache {
			shared: self.clone(),
			node_cache: Default::default(),
			value_cache: Default::default(),
			shared_node_cache_access: Default::default(),
			shared_value_cache_access: Default::default(),
		}
	}

	/// Returns the used memory size of this cache in bytes.
	pub fn used_memory_size(&self) -> usize {
		let value_cache_size = self.value_cache.read().size_in_bytes;
		let node_cache_size = self.node_cache.read().size_in_bytes;

		node_cache_size + value_cache_size
	}

	/// Reset the node cache.
	pub fn reset_node_cache(&self) {
		self.node_cache.write().reset();
	}

	/// Reset the value cache.
	pub fn reset_value_cache(&self) {
		self.value_cache.write().reset();
	}

	/// Reset the entire cache.
	pub fn reset(&self) {
		self.reset_node_cache();
		self.reset_value_cache();
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn shared_value_cache_works() {
		use sp_core::H256 as Hash;
		let base_size = mem::size_of::<CachedValue<Hash>>() + mem::size_of::<ValueCacheKey<Hash>>();
		let arc_size = mem::size_of::<Arc<[u8]>>();

		let mut cache = SharedValueCache::<sp_core::H256>::new(CacheSize::Maximum(
			(base_size + arc_size + 10) * 10,
		));

		let key = vec![0; 10];

		let root0 = Hash::repeat_byte(1);
		let root1 = Hash::repeat_byte(2);

		cache.update(
			vec![
				(
					ValueCacheKey::Value { storage_key: key.clone().into(), storage_root: root0 },
					CachedValue::NonExisting,
				),
				(
					ValueCacheKey::Value { storage_key: key.clone().into(), storage_root: root1 },
					CachedValue::NonExisting,
				),
			],
			vec![],
		);

		// Ensure that the basics are working
		assert_eq!(1, cache.known_storage_keys.len());
		assert_eq!(3, Arc::strong_count(cache.known_storage_keys.get(&key[..]).unwrap()));
		assert_eq!(base_size * 2 + key.len() + arc_size, cache.size_in_bytes);

		// Just accessing a key should not change anything on the size and number of entries.
		cache.update(
			vec![],
			vec![ValueCacheKey::Value { storage_key: key.clone().into(), storage_root: root0 }],
		);
		assert_eq!(1, cache.known_storage_keys.len());
		assert_eq!(3, Arc::strong_count(cache.known_storage_keys.get(&key[..]).unwrap()));
		assert_eq!(base_size * 2 + key.len() + arc_size, cache.size_in_bytes);

		// Add 9 other entries and this should move out the key for `root1`.
		cache.update(
			(1..10).map(|i| vec![i; 10]).map(|key| {
				(
					ValueCacheKey::Value { storage_key: key.clone().into(), storage_root: root0 },
					CachedValue::NonExisting,
				)
			}),
			vec![],
		);

		assert_eq!(10, cache.known_storage_keys.len());
		assert_eq!(2, Arc::strong_count(cache.known_storage_keys.get(&key[..]).unwrap()));
		assert_eq!((base_size + key.len() + arc_size) * 10, cache.size_in_bytes);
		assert!(matches!(
			cache
				.get(&ValueCacheKey::Ref { storage_root: root0, storage_key: &key })
				.unwrap(),
			CachedValue::<Hash>::NonExisting
		));
		assert!(cache
			.get(&ValueCacheKey::Ref { storage_root: root1, storage_key: &key })
			.is_none());

		cache.update(
			vec![
				(
					ValueCacheKey::Value { storage_key: vec![10; 10].into(), storage_root: root0 },
					CachedValue::NonExisting,
				)
			],
			vec![],
		);

		assert!(cache.known_storage_keys.get(&key[..]).is_none());
	}
}
