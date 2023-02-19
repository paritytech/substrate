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

//! Provides [`RecordStatsState`] for recording stats about state access.

use crate::stats::StateUsageStats;
use sp_core::storage::ChildInfo;
use sp_runtime::{
	traits::{Block as BlockT, HashFor},
	StateVersion,
};
use sp_state_machine::{
	backend::{AsTrieBackend, Backend as StateBackend},
	TrieBackend,
};
use std::sync::Arc;

/// State abstraction for recording stats about state access.
pub struct RecordStatsState<S, B: BlockT> {
	/// Usage statistics
	usage: StateUsageStats,
	/// State machine registered stats
	overlay_stats: sp_state_machine::StateMachineStats,
	/// Backing state.
	state: S,
	/// The hash of the block is state belongs to.
	block_hash: Option<B::Hash>,
	/// The usage statistics of the backend. These will be updated on drop.
	state_usage: Arc<StateUsageStats>,
}

impl<S, B: BlockT> std::fmt::Debug for RecordStatsState<S, B> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "Block {:?}", self.block_hash)
	}
}

impl<S, B: BlockT> Drop for RecordStatsState<S, B> {
	fn drop(&mut self) {
		self.state_usage.merge_sm(self.usage.take());
	}
}

impl<S: StateBackend<HashFor<B>>, B: BlockT> RecordStatsState<S, B> {
	/// Create a new instance wrapping generic State and shared cache.
	pub(crate) fn new(
		state: S,
		block_hash: Option<B::Hash>,
		state_usage: Arc<StateUsageStats>,
	) -> Self {
		RecordStatsState {
			usage: StateUsageStats::new(),
			overlay_stats: sp_state_machine::StateMachineStats::default(),
			state,
			block_hash,
			state_usage,
		}
	}
}

impl<S: StateBackend<HashFor<B>>, B: BlockT> StateBackend<HashFor<B>> for RecordStatsState<S, B> {
	type Error = S::Error;
	type Transaction = S::Transaction;
	type TrieBackendStorage = S::TrieBackendStorage;

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		let value = self.state.storage(key)?;
		self.usage.tally_key_read(key, value.as_ref(), false);
		Ok(value)
	}

	fn storage_hash(&self, key: &[u8]) -> Result<Option<B::Hash>, Self::Error> {
		self.state.storage_hash(key)
	}

	fn child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		let key = (child_info.storage_key().to_vec(), key.to_vec());
		let value = self.state.child_storage(child_info, &key.1)?;

		// just pass it through the usage counter
		let value = self.usage.tally_child_key_read(&key, value, false);

		Ok(value)
	}

	fn child_storage_hash(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<B::Hash>, Self::Error> {
		self.state.child_storage_hash(child_info, key)
	}

	fn exists_storage(&self, key: &[u8]) -> Result<bool, Self::Error> {
		self.state.exists_storage(key)
	}

	fn exists_child_storage(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<bool, Self::Error> {
		self.state.exists_child_storage(child_info, key)
	}

	fn apply_to_key_values_while<F: FnMut(Vec<u8>, Vec<u8>) -> bool>(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		start_at: Option<&[u8]>,
		f: F,
		allow_missing: bool,
	) -> Result<bool, Self::Error> {
		self.state
			.apply_to_key_values_while(child_info, prefix, start_at, f, allow_missing)
	}

	fn apply_to_keys_while<F: FnMut(&[u8]) -> bool>(
		&self,
		child_info: Option<&ChildInfo>,
		prefix: Option<&[u8]>,
		start_at: Option<&[u8]>,
		f: F,
	) {
		self.state.apply_to_keys_while(child_info, prefix, start_at, f)
	}

	fn next_storage_key(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.next_storage_key(key)
	}

	fn next_child_storage_key(
		&self,
		child_info: &ChildInfo,
		key: &[u8],
	) -> Result<Option<Vec<u8>>, Self::Error> {
		self.state.next_child_storage_key(child_info, key)
	}

	fn for_keys_with_prefix<F: FnMut(&[u8])>(&self, prefix: &[u8], f: F) {
		self.state.for_keys_with_prefix(prefix, f)
	}

	fn for_key_values_with_prefix<F: FnMut(&[u8], &[u8])>(&self, prefix: &[u8], f: F) {
		self.state.for_key_values_with_prefix(prefix, f)
	}

	fn for_child_keys_with_prefix<F: FnMut(&[u8])>(
		&self,
		child_info: &ChildInfo,
		prefix: &[u8],
		f: F,
	) {
		self.state.for_child_keys_with_prefix(child_info, prefix, f)
	}

	fn storage_root<'a>(
		&self,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (B::Hash, Self::Transaction)
	where
		B::Hash: Ord,
	{
		self.state.storage_root(delta, state_version)
	}

	fn child_storage_root<'a>(
		&self,
		child_info: &ChildInfo,
		delta: impl Iterator<Item = (&'a [u8], Option<&'a [u8]>)>,
		state_version: StateVersion,
	) -> (B::Hash, bool, Self::Transaction)
	where
		B::Hash: Ord,
	{
		self.state.child_storage_root(child_info, delta, state_version)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		self.state.pairs()
	}

	fn keys(&self, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.state.keys(prefix)
	}

	fn child_keys(&self, child_info: &ChildInfo, prefix: &[u8]) -> Vec<Vec<u8>> {
		self.state.child_keys(child_info, prefix)
	}

	fn register_overlay_stats(&self, stats: &sp_state_machine::StateMachineStats) {
		self.overlay_stats.add(stats);
	}

	fn usage_info(&self) -> sp_state_machine::UsageInfo {
		let mut info = self.usage.take();
		info.include_state_machine_states(&self.overlay_stats);
		info
	}
}

impl<S: StateBackend<HashFor<B>> + AsTrieBackend<HashFor<B>>, B: BlockT> AsTrieBackend<HashFor<B>>
	for RecordStatsState<S, B>
{
	type TrieBackendStorage = <S as AsTrieBackend<HashFor<B>>>::TrieBackendStorage;

	fn as_trie_backend(&self) -> &TrieBackend<Self::TrieBackendStorage, HashFor<B>> {
		self.state.as_trie_backend()
	}
}
