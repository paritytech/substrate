// This file is part of Substrate.

// Copyright (C) 2017-2023 Parity Technologies (UK) Ltd.
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

use crate::LOG_TARGET;
use schnellru::{Limiter, LruMap};
use sp_runtime::{traits::Block as BlockT, Justifications};

const PINNING_CACHE_SIZE: u32 = 1024;

struct PinnedBlockCacheEntry<Block: BlockT> {
	ref_count: u32,
	pub justifications: Option<Option<Justifications>>,
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
struct LoggingByLength {
	max_length: u32,
}

/// Limiter that limits the cache by length and logs removed items.
impl LoggingByLength {
	/// Creates a new length limiter with a given `max_length`.
	///
	/// If you don't need to strictly cap the number of elements and just want to limit
	/// the memory usage then prefer using [`ByMemoryUsage`].
	pub const fn new(max_length: u32) -> LoggingByLength {
		LoggingByLength { max_length }
	}
}

impl<Block: BlockT> Limiter<Block::Hash, PinnedBlockCacheEntry<Block>> for LoggingByLength {
	type KeyToInsert<'a> = Block::Hash;
	type LinkType = u32;

	fn is_over_the_limit(&self, length: usize) -> bool {
		length > self.max_length as usize
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

pub struct PinnedBlocksCache<Block: BlockT> {
	cache: LruMap<Block::Hash, PinnedBlockCacheEntry<Block>, LoggingByLength>,
}

impl<Block: BlockT> PinnedBlocksCache<Block> {
	pub fn new() -> Self {
		Self { cache: LruMap::new(LoggingByLength::new(PINNING_CACHE_SIZE)) }
	}

	pub fn bump_ref(&mut self, hash: Block::Hash) {
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
			None =>
				log::warn!(target: LOG_TARGET, "Unable to bump reference count. hash = {}", hash),
		};
	}

	pub fn clear(&mut self) {
		self.cache.clear();
	}

	pub fn contains(&self, hash: Block::Hash) -> bool {
		self.cache.peek(&hash).is_some()
	}

	pub fn insert_body(&mut self, hash: Block::Hash, extrinsics: Option<Vec<Block::Extrinsic>>) {
		match self.cache.get_or_insert(hash, Default::default) {
			Some(mut entry) => {
				entry.body = Some(extrinsics);
				log::trace!(
					target: LOG_TARGET,
					"Cached body. hash = {}, num_entries = {}",
					hash,
					self.cache.len()
				);
			},
			None => log::warn!(target: LOG_TARGET, "Unable to insert body. hash = {}", hash),
		}
	}

	pub fn insert_justifications(
		&mut self,
		hash: Block::Hash,
		justifications: Option<Justifications>,
	) {
		match self.cache.get_or_insert(hash, Default::default) {
			Some(mut entry) => {
				entry.justifications = Some(justifications);
				log::trace!(
					target: LOG_TARGET,
					"Cached justification. hash = {}, num_entries = {}",
					hash,
					self.cache.len()
				);
			},
			None =>
				log::warn!(target: LOG_TARGET, "Unable to insert justification. hash = {}", hash),
		}
	}

	pub fn remove(&mut self, hash: Block::Hash) {
		if let Some(entry) = self.cache.peek_mut(&hash) {
			entry.decrease_ref();
			if entry.has_no_references() {
				self.cache.remove(&hash);
			}
		}
	}

	pub fn justifications(&self, hash: &Block::Hash) -> Option<Option<Justifications>> {
		self.cache.peek(hash).and_then(|entry| entry.justifications.clone())
	}

	pub fn body(&self, hash: &Block::Hash) -> Option<Option<Vec<Block::Extrinsic>>> {
		self.cache.peek(hash).and_then(|entry| entry.body.clone())
	}
}
