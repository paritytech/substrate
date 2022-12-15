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
use nohash_hasher::BuildNoHashHasher;
use parking_lot::{RwLock, RwLockReadGuard, RwLockWriteGuard};
use std::{
	hash::{BuildHasher, Hasher as _},
	mem,
	sync::Arc,
};
use trie_db::{node::NodeOwned, CachedValue};

lazy_static::lazy_static! {
	static ref RANDOM_STATE: ahash::RandomState = ahash::RandomState::default();
}

/// No hashing [`LruCache`].
type NoHashingLruCache<K, T> = LruCache<K, T, BuildNoHashHasher<K>>;

/// The shared node cache.
///
/// Internally this stores all cached nodes in a [`LruCache`]. It ensures that when updating the
/// cache, that the cache stays within its allowed bounds.
pub(super) struct SharedNodeCache<H> {
	/// The cached nodes, ordered by least recently used.
	pub(super) lru: LruCache<H, NodeOwned<H>>,
	/// The size of [`Self::lru`] in bytes.
	pub(super) size_in_bytes: usize,
	/// The maximum cache size of [`Self::lru`].
	maximum_cache_size: CacheSize,
}

impl<H: AsRef<[u8]> + Eq + std::hash::Hash> SharedNodeCache<H> {
	/// Create a new instance.
	fn new(cache_size: CacheSize) -> Self {
		Self { lru: LruCache::unbounded(), size_in_bytes: 0, maximum_cache_size: cache_size }
	}

	/// Get the node for `key`.
	///
	/// This doesn't change the least recently order in the internal [`LruCache`].
	pub fn get(&self, key: &H) -> Option<&NodeOwned<H>> {
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
		added: impl IntoIterator<Item = (H, NodeOwned<H>)>,
		accessed: impl IntoIterator<Item = H>,
	) {
		let update_size_in_bytes = |size_in_bytes: &mut usize, key: &H, node: &NodeOwned<H>| {
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

/// The hash of [`ValueCacheKey`].
#[derive(Eq, Clone, Copy)]
pub struct ValueCacheKeyHash(u64);

impl ValueCacheKeyHash {
	pub fn from_hasher_and_storage_key(
		mut hasher: impl std::hash::Hasher,
		storage_key: &[u8],
	) -> Self {
		hasher.write(storage_key);

		Self(hasher.finish())
	}
}

impl PartialEq for ValueCacheKeyHash {
	fn eq(&self, other: &Self) -> bool {
		self.0 == other.0
	}
}

impl std::hash::Hash for ValueCacheKeyHash {
	fn hash<Hasher: std::hash::Hasher>(&self, state: &mut Hasher) {
		state.write_u64(self.0);
	}
}

impl nohash_hasher::IsEnabled for ValueCacheKeyHash {}

/// A type that can only be constructed inside of this file.
///
/// It "requires" that the user has read the docs to prevent fuck ups.
#[derive(Eq, PartialEq)]
pub(super) struct IReadTheDocumentation(());

/// The key type that is being used to address a [`CachedValue`].
///
/// This type is implemented as `enum` to improve the performance when accessing the value cache.
/// The problem being that we need to calculate the `hash` of [`Self`] in worst case three times
/// when trying to find a value in the value cache. First to lookup the local cache, then the shared
/// cache and if we found it in the shared cache a third time to insert it into the list of accessed
/// values. To work around each variant stores the `hash` to identify a unique combination of
/// `storage_key` and `storage_root`. However, be aware that this `hash` can lead to collisions when
/// there are two different `storage_key` and `storage_root` pairs that map to the same `hash`. This
/// type also has the `Hash` variant. This variant should only be used for the use case of updating
/// the lru for a key. Because when using only the `Hash` variant to getting a value from a hash map
/// it could happen that a wrong value is returned when there is another key in the same hash map
/// that maps to the same `hash`. The [`PartialEq`] implementation is written in a way that when one
/// of the two compared instances is the `Hash` variant, we will only compare the hashes. This
/// ensures that we can use the `Hash` variant to bring values up in the lru.
#[derive(Eq)]
pub(super) enum ValueCacheKey<'a, H> {
	/// Variant that stores the `storage_key` by value.
	Value {
		/// The storage root of the trie this key belongs to.
		storage_root: H,
		/// The key to access the value in the storage.
		storage_key: Arc<[u8]>,
		/// The hash that identifying this instance of `storage_root` and `storage_key`.
		hash: ValueCacheKeyHash,
	},
	/// Variant that only references the `storage_key`.
	Ref {
		/// The storage root of the trie this key belongs to.
		storage_root: H,
		/// The key to access the value in the storage.
		storage_key: &'a [u8],
		/// The hash that identifying this instance of `storage_root` and `storage_key`.
		hash: ValueCacheKeyHash,
	},
	/// Variant that only stores the hash that represents the `storage_root` and `storage_key`.
	///
	/// This should be used by caution, because it can lead to accessing the wrong value in a
	/// hash map/set when there exists two different `storage_root`s and `storage_key`s that
	/// map to the same `hash`.
	Hash { hash: ValueCacheKeyHash, _i_read_the_documentation: IReadTheDocumentation },
}

impl<'a, H> ValueCacheKey<'a, H> {
	/// Constructs [`Self::Value`].
	pub fn new_value(storage_key: impl Into<Arc<[u8]>>, storage_root: H) -> Self
	where
		H: AsRef<[u8]>,
	{
		let storage_key = storage_key.into();
		let hash = Self::hash_data(&storage_key, &storage_root);
		Self::Value { storage_root, storage_key, hash }
	}

	/// Constructs [`Self::Ref`].
	pub fn new_ref(storage_key: &'a [u8], storage_root: H) -> Self
	where
		H: AsRef<[u8]>,
	{
		let storage_key = storage_key.into();
		let hash = Self::hash_data(storage_key, &storage_root);
		Self::Ref { storage_root, storage_key, hash }
	}

	/// Returns a hasher prepared to build the final hash to identify [`Self`].
	///
	/// See [`Self::hash_data`] for building the hash directly.
	pub fn hash_partial_data(storage_root: &H) -> impl std::hash::Hasher + Clone
	where
		H: AsRef<[u8]>,
	{
		let mut hasher = RANDOM_STATE.build_hasher();
		hasher.write(storage_root.as_ref());
		hasher
	}

	/// Hash the `key` and `storage_root` that identify [`Self`].
	///
	/// Returns a `u64` which represents the unique hash for the given inputs.
	pub fn hash_data(key: &[u8], storage_root: &H) -> ValueCacheKeyHash
	where
		H: AsRef<[u8]>,
	{
		let hasher = Self::hash_partial_data(storage_root);

		ValueCacheKeyHash::from_hasher_and_storage_key(hasher, key)
	}

	/// Returns the `hash` that identifies the current instance.
	pub fn get_hash(&self) -> ValueCacheKeyHash {
		match self {
			Self::Value { hash, .. } | Self::Ref { hash, .. } | Self::Hash { hash, .. } => *hash,
		}
	}

	/// Returns the stored storage root.
	pub fn storage_root(&self) -> Option<&H> {
		match self {
			Self::Value { storage_root, .. } | Self::Ref { storage_root, .. } => Some(storage_root),
			Self::Hash { .. } => None,
		}
	}

	/// Returns the stored storage key.
	pub fn storage_key(&self) -> Option<&[u8]> {
		match self {
			Self::Ref { storage_key, .. } => Some(&storage_key),
			Self::Value { storage_key, .. } => Some(storage_key),
			Self::Hash { .. } => None,
		}
	}
}

// Implement manually to ensure that the `Value` and `Hash` are treated equally.
impl<H: std::hash::Hash> std::hash::Hash for ValueCacheKey<'_, H> {
	fn hash<Hasher: std::hash::Hasher>(&self, state: &mut Hasher) {
		self.get_hash().hash(state)
	}
}

impl<H> nohash_hasher::IsEnabled for ValueCacheKey<'_, H> {}

// Implement manually to ensure that the `Value` and `Hash` are treated equally.
impl<H: PartialEq> PartialEq for ValueCacheKey<'_, H> {
	fn eq(&self, other: &Self) -> bool {
		// First check if `self` or `other` is only the `Hash`.
		// Then we only compare the `hash`. So, there could actually be some collision
		// if two different storage roots and keys are mapping to the same key. See the
		// [`ValueCacheKey`] docs for more information.
		match (self, other) {
			(Self::Hash { hash, .. }, Self::Hash { hash: other_hash, .. }) => hash == other_hash,
			(Self::Hash { hash, .. }, _) => *hash == other.get_hash(),
			(_, Self::Hash { hash: other_hash, .. }) => self.get_hash() == *other_hash,
			// If both are not the `Hash` variant, we compare all the values.
			_ =>
				self.get_hash() == other.get_hash() &&
					self.storage_root() == other.storage_root() &&
					self.storage_key() == other.storage_key(),
		}
	}
}

/// The shared value cache.
///
/// The cache ensures that it stays in the configured size bounds.
pub(super) struct SharedValueCache<H> {
	/// The cached nodes, ordered by least recently used.
	pub(super) lru: NoHashingLruCache<ValueCacheKey<'static, H>, CachedValue<H>>,
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

impl<H: Eq + std::hash::Hash + Clone + Copy + AsRef<[u8]>> SharedValueCache<H> {
	/// Create a new instance.
	fn new(cache_size: CacheSize) -> Self {
		Self {
			lru: NoHashingLruCache::unbounded_with_hasher(Default::default()),
			size_in_bytes: 0,
			maximum_cache_size: cache_size,
			known_storage_keys: Default::default(),
		}
	}

	/// Get the [`CachedValue`] for `key`.
	///
	/// This doesn't change the least recently order in the internal [`LruCache`].
	pub fn get<'a>(&'a self, key: &ValueCacheKey<H>) -> Option<&'a CachedValue<H>> {
		debug_assert!(
			!matches!(key, ValueCacheKey::Hash { .. }),
			"`get` can not be called with `Hash` variant as this may returns the wrong value."
		);

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
	/// [`ValueCacheKeyHash`] and represent the values that were retrieved from this shared cache
	/// through [`Self::get`]. These `accessed` values are being put to the front of the internal
	/// [`LruCache`] like the `added` ones.
	///
	/// After the internal [`LruCache`] was updated, it is ensured that the internal [`LruCache`] is
	/// inside its bounds ([`Self::maximum_size_in_bytes`]).
	pub fn update(
		&mut self,
		added: impl IntoIterator<Item = (ValueCacheKey<'static, H>, CachedValue<H>)>,
		accessed: impl IntoIterator<Item = ValueCacheKeyHash>,
	) {
		// The base size in memory per ([`ValueCacheKey<H>`], [`CachedValue`]).
		let base_size = mem::size_of::<ValueCacheKey<H>>() + mem::size_of::<CachedValue<H>>();
		let known_keys_entry_size = mem::size_of::<Arc<[u8]>>();

		let update_size_in_bytes =
			|size_in_bytes: &mut usize, r_key: Arc<[u8]>, known_keys: &mut HashSet<Arc<[u8]>>| {
				// If the `strong_count == 2`, it means this is the last instance of the key.
				// One being `r_key` and the other being stored in `known_storage_keys`.
				let last_instance = Arc::strong_count(&r_key) == 2;

				let key_len = if last_instance {
					known_keys.remove(&r_key);
					r_key.len() + known_keys_entry_size
				} else {
					// The key is still in `keys`, because it is still used by another
					// `ValueCacheKey<H>`.
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
			// As we are using the `Hash` variant here, it may leads to putting the wrong value to
			// the top. However, the only consequence of this is that we may prune a recently used
			// value to early.
			self.lru.get(&ValueCacheKey::Hash {
				hash: key,
				_i_read_the_documentation: IReadTheDocumentation(()),
			});
		});

		added.into_iter().for_each(|(key, value)| {
			let (storage_root, storage_key, key_hash) = match key {
				ValueCacheKey::Hash { .. } => {
					// Ignore the hash variant and try the next.
					tracing::error!(
						target: LOG_TARGET,
						"`SharedValueCached::update` was called with a key to add \
						that uses the `Hash` variant. This would lead to potential hash collision!",
					);
					return
				},
				ValueCacheKey::Ref { storage_key, storage_root, hash } =>
					(storage_root, storage_key.into(), hash),
				ValueCacheKey::Value { storage_root, storage_key, hash } =>
					(storage_root, storage_key, hash),
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

			if let Some((r_key, _)) = self
				.lru
				.push(ValueCacheKey::Value { storage_key, storage_root, hash: key_hash }, value)
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

/// The inner of [`SharedTrieCache`].
pub(super) struct SharedTrieCacheInner<H: Hasher> {
	node_cache: SharedNodeCache<H::Out>,
	value_cache: SharedValueCache<H::Out>,
}

impl<H: Hasher> SharedTrieCacheInner<H> {
	/// Returns a reference to the [`SharedValueCache`].
	pub(super) fn value_cache(&self) -> &SharedValueCache<H::Out> {
		&self.value_cache
	}

	/// Returns a mutable reference to the [`SharedValueCache`].
	pub(super) fn value_cache_mut(&mut self) -> &mut SharedValueCache<H::Out> {
		&mut self.value_cache
	}

	/// Returns a reference to the [`SharedNodeCache`].
	pub(super) fn node_cache(&self) -> &SharedNodeCache<H::Out> {
		&self.node_cache
	}

	/// Returns a mutable reference to the [`SharedNodeCache`].
	pub(super) fn node_cache_mut(&mut self) -> &mut SharedNodeCache<H::Out> {
		&mut self.node_cache
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
	inner: Arc<RwLock<SharedTrieCacheInner<H>>>,
}

impl<H: Hasher> Clone for SharedTrieCache<H> {
	fn clone(&self) -> Self {
		Self { inner: self.inner.clone() }
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
			inner: Arc::new(RwLock::new(SharedTrieCacheInner {
				node_cache: SharedNodeCache::new(node_cache_size),
				value_cache: SharedValueCache::new(value_cache_size),
			})),
		}
	}

	/// Create a new [`LocalTrieCache`](super::LocalTrieCache) instance from this shared cache.
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
		let inner = self.inner.read();
		let value_cache_size = inner.value_cache.size_in_bytes;
		let node_cache_size = inner.node_cache.size_in_bytes;

		node_cache_size + value_cache_size
	}

	/// Reset the node cache.
	pub fn reset_node_cache(&self) {
		self.inner.write().node_cache.reset();
	}

	/// Reset the value cache.
	pub fn reset_value_cache(&self) {
		self.inner.write().value_cache.reset();
	}

	/// Reset the entire cache.
	pub fn reset(&self) {
		self.reset_node_cache();
		self.reset_value_cache();
	}

	/// Returns the read locked inner.
	pub(super) fn read_lock_inner(&self) -> RwLockReadGuard<'_, SharedTrieCacheInner<H>> {
		self.inner.read()
	}

	/// Returns the write locked inner.
	pub(super) fn write_lock_inner(&self) -> RwLockWriteGuard<'_, SharedTrieCacheInner<H>> {
		self.inner.write()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::H256 as Hash;

	#[test]
	fn shared_value_cache_works() {
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
				(ValueCacheKey::new_value(&key[..], root0), CachedValue::NonExisting),
				(ValueCacheKey::new_value(&key[..], root1), CachedValue::NonExisting),
			],
			vec![],
		);

		// Ensure that the basics are working
		assert_eq!(1, cache.known_storage_keys.len());
		assert_eq!(3, Arc::strong_count(cache.known_storage_keys.get(&key[..]).unwrap()));
		assert_eq!(base_size * 2 + key.len() + arc_size, cache.size_in_bytes);

		// Just accessing a key should not change anything on the size and number of entries.
		cache.update(vec![], vec![ValueCacheKey::hash_data(&key[..], &root0)]);
		assert_eq!(1, cache.known_storage_keys.len());
		assert_eq!(3, Arc::strong_count(cache.known_storage_keys.get(&key[..]).unwrap()));
		assert_eq!(base_size * 2 + key.len() + arc_size, cache.size_in_bytes);

		// Add 9 other entries and this should move out the key for `root1`.
		cache.update(
			(1..10)
				.map(|i| vec![i; 10])
				.map(|key| (ValueCacheKey::new_value(&key[..], root0), CachedValue::NonExisting)),
			vec![],
		);

		assert_eq!(10, cache.known_storage_keys.len());
		assert_eq!(2, Arc::strong_count(cache.known_storage_keys.get(&key[..]).unwrap()));
		assert_eq!((base_size + key.len() + arc_size) * 10, cache.size_in_bytes);
		assert!(matches!(
			cache.get(&ValueCacheKey::new_ref(&key, root0)).unwrap(),
			CachedValue::<Hash>::NonExisting
		));
		assert!(cache.get(&ValueCacheKey::new_ref(&key, root1)).is_none());

		cache.update(
			vec![(ValueCacheKey::new_value(vec![10; 10], root0), CachedValue::NonExisting)],
			vec![],
		);

		assert!(cache.known_storage_keys.get(&key[..]).is_none());
	}

	#[test]
	fn value_cache_key_eq_works() {
		let storage_key = &b"something"[..];
		let storage_key2 = &b"something2"[..];
		let storage_root = Hash::random();

		let value = ValueCacheKey::new_value(storage_key, storage_root);
		// Ref gets the same hash, but a different storage key
		let ref_ =
			ValueCacheKey::Ref { storage_root, storage_key: storage_key2, hash: value.get_hash() };
		let hash = ValueCacheKey::Hash {
			hash: value.get_hash(),
			_i_read_the_documentation: IReadTheDocumentation(()),
		};

		// Ensure that the hash variants is equal to `value`, `ref_` and itself.
		assert!(hash == value);
		assert!(value == hash);
		assert!(hash == ref_);
		assert!(ref_ == hash);
		assert!(hash == hash);

		// But when we compare `value` and `ref_` the different storage key is detected.
		assert!(value != ref_);
		assert!(ref_ != value);
	}
}
