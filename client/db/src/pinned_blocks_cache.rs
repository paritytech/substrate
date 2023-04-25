// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use schnellru::{Limiter, LruMap};
use sp_runtime::{traits::Block as BlockT, Justifications};

const LOG_TARGET: &str = "db::pin";
const PINNING_CACHE_SIZE: usize = 1024;

/// Entry for pinned blocks cache.
struct PinnedBlockCacheEntry<Block: BlockT> {
	/// How many times this item has been pinned
	ref_count: u32,

	/// Cached justifications for this block
	pub justifications: Option<Option<Justifications>>,

	/// Cached body for this block
	pub body: Option<Option<Vec<Block::Extrinsic>>>,
}

impl<Block: BlockT> Default for PinnedBlockCacheEntry<Block> {
	fn default() -> Self {
		Self { ref_count: 0, justifications: None, body: None }
	}
}

impl<Block: BlockT> PinnedBlockCacheEntry<Block> {
	pub fn decrease_ref(&mut self) {
		self.ref_count = self.ref_count.saturating_sub(1);
	}

	pub fn increase_ref(&mut self) {
		self.ref_count = self.ref_count.saturating_add(1);
	}

	pub fn has_no_references(&self) -> bool {
		self.ref_count == 0
	}
}

/// A limiter for a map which is limited by the number of elements.
#[derive(Copy, Clone, Debug)]
struct LoggingByLengthLimiter {
	max_length: usize,
}

impl LoggingByLengthLimiter {
	/// Creates a new length limiter with a given `max_length`.
	pub const fn new(max_length: usize) -> LoggingByLengthLimiter {
		LoggingByLengthLimiter { max_length }
	}
}

impl<Block: BlockT> Limiter<Block::Hash, PinnedBlockCacheEntry<Block>> for LoggingByLengthLimiter {
	type KeyToInsert<'a> = Block::Hash;
	type LinkType = usize;

	fn is_over_the_limit(&self, length: usize) -> bool {
		length > self.max_length
	}

	fn on_insert(
		&mut self,
		_length: usize,
		key: Self::KeyToInsert<'_>,
		value: PinnedBlockCacheEntry<Block>,
	) -> Option<(Block::Hash, PinnedBlockCacheEntry<Block>)> {
		if self.max_length > 0 {
			Some((key, value))
		} else {
			None
		}
	}

	fn on_replace(
		&mut self,
		_length: usize,
		_old_key: &mut Block::Hash,
		_new_key: Block::Hash,
		_old_value: &mut PinnedBlockCacheEntry<Block>,
		_new_value: &mut PinnedBlockCacheEntry<Block>,
	) -> bool {
		true
	}

	fn on_removed(&mut self, key: &mut Block::Hash, value: &mut PinnedBlockCacheEntry<Block>) {
		// If reference count was larger than 0 on removal,
		// the item was removed due to capacity limitations.
		// Since the cache should be large enough for pinned items,
		// we want to know about these evictions.
		if value.ref_count > 0 {
			log::warn!(
				target: LOG_TARGET,
				"Pinned block cache limit reached. Evicting value. hash = {}",
				key
			);
		} else {
			log::trace!(
				target: LOG_TARGET,
				"Evicting value from pinned block cache. hash = {}",
				key
			)
		}
	}

	fn on_cleared(&mut self) {}

	fn on_grow(&mut self, _new_memory_usage: usize) -> bool {
		true
	}
}

/// Reference counted cache for pinned block bodies and justifications.
pub struct PinnedBlocksCache<Block: BlockT> {
	cache: LruMap<Block::Hash, PinnedBlockCacheEntry<Block>, LoggingByLengthLimiter>,
}

impl<Block: BlockT> PinnedBlocksCache<Block> {
	pub fn new() -> Self {
		Self { cache: LruMap::new(LoggingByLengthLimiter::new(PINNING_CACHE_SIZE)) }
	}

	/// Increase reference count of an item.
	/// Create an entry with empty value in the cache if necessary.
	pub fn pin(&mut self, hash: Block::Hash) {
		match self.cache.get_or_insert(hash, Default::default) {
			Some(entry) => {
				entry.increase_ref();
				log::trace!(
					target: LOG_TARGET,
					"Bumped cache refcount. hash = {}, num_entries = {}",
					hash,
					self.cache.len()
				);
			},
			None => {
				log::warn!(target: LOG_TARGET, "Unable to bump reference count. hash = {}", hash)
			},
		};
	}

	/// Clear the cache
	pub fn clear(&mut self) {
		self.cache.clear();
	}

	/// Check if item is contained in the cache
	pub fn contains(&self, hash: Block::Hash) -> bool {
		self.cache.peek(&hash).is_some()
	}

	/// Attach body to an existing cache item
	pub fn insert_body(&mut self, hash: Block::Hash, extrinsics: Option<Vec<Block::Extrinsic>>) {
		match self.cache.peek_mut(&hash) {
			Some(mut entry) => {
				entry.body = Some(extrinsics);
				log::trace!(
					target: LOG_TARGET,
					"Cached body. hash = {}, num_entries = {}",
					hash,
					self.cache.len()
				);
			},
			None => log::warn!(
				target: LOG_TARGET,
				"Unable to insert body for uncached item. hash = {}",
				hash
			),
		}
	}

	/// Attach justification to an existing cache item
	pub fn insert_justifications(
		&mut self,
		hash: Block::Hash,
		justifications: Option<Justifications>,
	) {
		match self.cache.peek_mut(&hash) {
			Some(mut entry) => {
				entry.justifications = Some(justifications);
				log::trace!(
					target: LOG_TARGET,
					"Cached justification. hash = {}, num_entries = {}",
					hash,
					self.cache.len()
				);
			},
			None => log::warn!(
				target: LOG_TARGET,
				"Unable to insert justifications for uncached item. hash = {}",
				hash
			),
		}
	}

	/// Decreases reference count of an item.
	/// If the count hits 0, the item is removed.
	pub fn unpin(&mut self, hash: Block::Hash) {
		if let Some(entry) = self.cache.peek_mut(&hash) {
			entry.decrease_ref();
			if entry.has_no_references() {
				self.cache.remove(&hash);
			}
		}
	}

	/// Get justifications for cached block
	pub fn justifications(&self, hash: &Block::Hash) -> Option<&Option<Justifications>> {
		self.cache.peek(hash).and_then(|entry| entry.justifications.as_ref())
	}

	/// Get body for cached block
	pub fn body(&self, hash: &Block::Hash) -> Option<&Option<Vec<Block::Extrinsic>>> {
		self.cache.peek(hash).and_then(|entry| entry.body.as_ref())
	}
}
