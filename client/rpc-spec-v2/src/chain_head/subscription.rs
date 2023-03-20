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

//! Subscription management for tracking subscription IDs to pinned blocks.

use futures::channel::oneshot;
use parking_lot::RwLock;
use sc_client_api::Backend;
use sp_blockchain::Error;
use sp_runtime::traits::Block as BlockT;
use std::{
	collections::{hash_map::Entry, HashMap},
	sync::Arc,
	time::{Duration, Instant},
};

/// Subscription management error.
#[derive(Debug, thiserror::Error)]
pub enum SubscriptionManagementError {
	/// The block cannot be pinned into memory because
	/// the subscription has exceeded the maximum number
	/// of blocks pinned.
	#[error("Exceeded pinning limits")]
	ExceededLimits,
	/// Error originated from the blockchain (client or backend).
	#[error("Blockchain error {0}")]
	Blockchain(Error),
	/// The database does not contain a block number.
	#[error("Block number is absent")]
	BlockNumberAbsent,
	/// The database does not contain a block hash.
	#[error("Block hash is absent")]
	BlockHashAbsent,
	/// The specified subscription ID is not present.
	#[error("Subscription is absent")]
	SubscriptionAbsent,
	/// Custom error.
	#[error("Subscription error {0}")]
	Custom(String),
}

// Blockchain error does not implement `PartialEq` needed for testing.
impl PartialEq for SubscriptionManagementError {
	fn eq(&self, other: &SubscriptionManagementError) -> bool {
		match (self, other) {
			(Self::ExceededLimits, Self::ExceededLimits) |
			// Not needed for testing.
			(Self::Blockchain(_), Self::Blockchain(_)) |
			(Self::BlockNumberAbsent, Self::BlockNumberAbsent) |
			(Self::BlockHashAbsent, Self::BlockHashAbsent) |
			(Self::SubscriptionAbsent, Self::SubscriptionAbsent) => true,
			(Self::Custom(lhs), Self::Custom(rhs)) => lhs == rhs,
			_ => false,
		}
	}
}

impl From<Error> for SubscriptionManagementError {
	fn from(err: Error) -> Self {
		SubscriptionManagementError::Blockchain(err)
	}
}

/// The state of a block of a single subscription ID.
struct BlockState {
	/// True if the block can be unregistered from the
	/// internal memory of the subscription.
	///
	/// Each block is registered twice: once from the `BestBlock` event
	/// and once from the `Finalized` event. This becomes true when
	/// both events registered the block.
	///
	/// Field is added to avoid losing track of the block for the following
	/// timeline:
	///  T0. BestBlock event: hash is tracked and pinned in backend.
	///  T1. User calls unpin: hash is untracked and unpinned in backend.
	///  T2. Finalized event: hash is tracked (no previous history) and pinned again.
	can_unregister: bool,
	/// True if the block was unpinned.
	///
	/// Because of the previous condition, a block can be unregistered
	/// only when both `can_unregister` and `was_unpinned` are true.
	was_unpinned: bool,
	/// The timestamp when the block was inserted.
	timestamp: Instant,
}

/// The state of a single subscription ID.
struct SubscriptionState<Block: BlockT> {
	/// The `runtime_updates` parameter flag of the subscription.
	runtime_updates: bool,
	/// Signals the "Stop" event.
	tx_stop: Option<oneshot::Sender<()>>,
	/// Track the block hashes available for this subscription.
	///
	/// This implementation assumes:
	/// - most of the time subscriptions keep a few blocks of the chain's head pinned
	/// - iteration through the blocks happens only when the hard limit is exceeded.
	///
	/// Considering the assumption, iterating (in the unlike case) the hashmap O(N) is
	/// more time efficient and code friendly than paying for:
	/// - extra space: an extra BTreeMap<Instant, Hash> to older hashes by oldest insertion
	/// - extra time: O(log(N)) for insert/remove/find each `pin` block time per subscriptions
	blocks: HashMap<Block::Hash, BlockState>,
}

impl<Block: BlockT> SubscriptionState<Block> {
	/// Trigger the stop event for the current subscription.
	///
	/// This can happen on internal failure (ie, the pruning deleted the block from memory)
	/// or if the subscription exceeded the available pinned blocks.
	fn stop(&mut self) {
		if let Some(tx_stop) = self.tx_stop.take() {
			let _ = tx_stop.send(());
		}
	}

	/// Keep track of the given block hash for this subscription.
	///
	/// This does not handle pinning in the backend.
	///
	/// Returns:
	/// - true if this is the first time that the block is registered
	/// - false if the block was already registered
	fn register_block(&mut self, hash: Block::Hash) -> bool {
		match self.blocks.entry(hash) {
			Entry::Occupied(mut occupied) => {
				let mut block_state = occupied.get_mut();
				if block_state.was_unpinned {
					// If `unpin` was called between two events
					// unregister the block now.
					occupied.remove();
				} else {
					// Both `BestBlock` and `Finalized` events registered the block.
					// Unregister the block on `unpin`.
					block_state.can_unregister = true;
				}

				false
			},
			Entry::Vacant(vacant) => {
				vacant.insert(BlockState {
					can_unregister: false,
					was_unpinned: false,
					timestamp: Instant::now(),
				});

				true
			},
		}
	}

	/// A block is unregistered when the user calls `unpin`.
	///
	/// Returns:
	/// - true if the block can be unpinned.
	/// - false if the subscription does not contain the block.
	fn unregister_block(&mut self, hash: Block::Hash) -> bool {
		match self.blocks.entry(hash) {
			Entry::Occupied(mut occupied) => {
				let mut block_state = occupied.get_mut();

				// Cannot unpin a block twice.
				if block_state.was_unpinned {
					return false
				}

				// If `pin` was called twice unregister the block now.
				if block_state.can_unregister {
					occupied.remove();
				} else {
					block_state.was_unpinned = true;
				}

				true
			},
			// Block was not tracked.
			Entry::Vacant(_) => false,
		}
	}

	/// A subscription contains a block when the block was
	/// registered (`pin` was called) and the block was not `unpinned` yet.
	///
	/// Returns `true` if the subscription contains the block.
	fn contains_block(&self, hash: Block::Hash) -> bool {
		let Some(state) = self.blocks.get(&hash) else {
			// Block was not tracked.
			return false
		};

		// Subscription no longer contains the block if `unpin` was called.
		!state.was_unpinned
	}

	fn oldest_block_timestamp(&self) -> Instant {
		let mut timestamp = Instant::now();
		for (_, state) in self.blocks.iter() {
			timestamp = std::cmp::min(timestamp, state.timestamp);
		}
		timestamp
	}
}

pub struct BlockGuard<Block: BlockT, BE: Backend<Block> + 'static> {
	hash: Block::Hash,
	runtime_updates: bool,
	backend: Arc<BE>,
}

// Custom implementation of Debug to avoid bounds on `backend: Debug` for `unwrap_err()` needed for
// testing.
impl<Block: BlockT, BE: Backend<Block> + 'static> std::fmt::Debug for BlockGuard<Block, BE> {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "BlockGuard hash {:?} runtime_updates {:?}", self.hash, self.runtime_updates)
	}
}

impl<Block: BlockT, BE: Backend<Block> + 'static> BlockGuard<Block, BE> {
	/// Construct a new [`BlockGuard`] .
	fn new(
		hash: Block::Hash,
		runtime_updates: bool,
		backend: Arc<BE>,
	) -> Result<Self, SubscriptionManagementError> {
		backend
			.pin_block(hash)
			.map_err(|err| SubscriptionManagementError::Custom(err.to_string()))?;

		Ok(Self { hash, runtime_updates, backend })
	}

	/// The `runtime_updates` flag of the subscription.
	pub fn has_runtime_updates(&self) -> bool {
		self.runtime_updates
	}
}

impl<Block: BlockT, BE: Backend<Block> + 'static> Drop for BlockGuard<Block, BE> {
	fn drop(&mut self) {
		self.backend.unpin_block(self.hash);
	}
}

struct SubscriptionsInner<Block: BlockT, BE: Backend<Block> + 'static> {
	/// Reference count the block hashes across all subscriptions.
	///
	/// The pinned blocks cannot exceed the [`Self::global_limit`] limit.
	/// When the limit is exceeded subscriptions are stopped via the `Stop` event.
	global_blocks: HashMap<Block::Hash, usize>,
	/// The maximum number of pinned blocks across all subscriptions.
	global_max_pinned_blocks: usize,
	/// The maximum duration that a block is allowed to be pinned per subscription.
	local_max_pin_duration: Duration,
	/// Map the subscription ID to internal details of the subscription.
	subs: HashMap<String, SubscriptionState<Block>>,
	/// Backend pinning / unpinning blocks.
	///
	/// The `Arc` is handled one level-above, but substrate exposes the backend as Arc<T>.
	backend: Arc<BE>,
}

impl<Block: BlockT, BE: Backend<Block> + 'static> SubscriptionsInner<Block, BE> {
	/// Construct a new [`GlobalSubscriptionInner`] from the specified limits.
	fn new(
		global_max_pinned_blocks: usize,
		local_max_pin_duration: Duration,
		backend: Arc<BE>,
	) -> Self {
		SubscriptionsInner {
			global_blocks: Default::default(),
			global_max_pinned_blocks,
			local_max_pin_duration,
			subs: Default::default(),
			backend,
		}
	}

	/// Insert a new subscription ID.
	fn insert_subscription(
		&mut self,
		sub_id: String,
		runtime_updates: bool,
	) -> Option<oneshot::Receiver<()>> {
		if let Entry::Vacant(entry) = self.subs.entry(sub_id) {
			let (tx_stop, rx_stop) = oneshot::channel();
			let state = SubscriptionState::<Block> {
				runtime_updates,
				tx_stop: Some(tx_stop),
				blocks: Default::default(),
			};
			entry.insert(state);
			Some(rx_stop)
		} else {
			None
		}
	}

	/// Remove the subscription ID with associated pinned blocks.
	fn remove_subscription(&mut self, sub_id: &str) {
		let Some(mut sub) = self.subs.remove(sub_id) else {
			return
		};

		// The `Stop` event can be generated only once.
		sub.stop();

		for (hash, state) in sub.blocks.iter() {
			if !state.was_unpinned {
				self.global_unpin_block(*hash);
			}
		}
	}

	/// Ensure that a new block could be pinned.
	///
	/// If the global number of blocks has been reached this method
	/// will remove all subscriptions that have blocks older than the
	/// specified pin duration.
	///
	/// If after removing all subscriptions that exceed the pin duration
	/// there is no space for pinning a new block, then all subscriptions
	/// are terminated.
	///
	/// Returns true if the given subscription is also terminated.
	fn ensure_block_space(&mut self, request_sub_id: &str) -> bool {
		if self.global_blocks.len() < self.global_max_pinned_blocks {
			return false
		}

		// Terminate all subscriptions that have blocks older than
		// the specified pin duration.
		let now = Instant::now();

		let to_remove: Vec<_> = self
			.subs
			.iter_mut()
			.filter_map(|(sub_id, sub)| {
				let sub_time = sub.oldest_block_timestamp();
				// Subscriptions older than the specified pin duration should be removed.
				let should_remove = match now.checked_duration_since(sub_time) {
					Some(duration) => duration > self.local_max_pin_duration,
					None => true,
				};
				should_remove.then_some(sub_id.clone())
			})
			.collect();

		let mut is_terminated = false;
		for sub_id in to_remove.into_iter() {
			if sub_id == request_sub_id {
				is_terminated = true;
			}
			self.remove_subscription(&sub_id);
		}

		// Make sure we have enough space after first pass of terminating subscriptions.
		if self.global_blocks.len() < self.global_max_pinned_blocks {
			return is_terminated
		}

		// Sanity check: cannot uphold `chainHead` guarantees anymore. We have not
		// found any subscriptions that have older pinned blocks to terminate.
		let to_remove: Vec<_> = self.subs.iter().map(|(sub_id, _)| sub_id.clone()).collect();
		for sub_id in to_remove.into_iter() {
			if sub_id == request_sub_id {
				is_terminated = true;
			}
			self.remove_subscription(&sub_id);
		}
		return is_terminated
	}

	fn pin_block(
		&mut self,
		sub_id: &str,
		hash: Block::Hash,
	) -> Result<bool, SubscriptionManagementError> {
		let Some(sub) = self.subs.get_mut(sub_id) else {
			return Err(SubscriptionManagementError::SubscriptionAbsent)
		};

		// Block was already registered for this subscription and therefore
		// globally tracked.
		if !sub.register_block(hash) {
			return Ok(false)
		}

		// Ensure we have enough space only if the hash is not globally registered.
		if !self.global_blocks.contains_key(&hash) {
			// Subscription ID was terminated while ensuring enough space.
			if self.ensure_block_space(sub_id) {
				return Err(SubscriptionManagementError::ExceededLimits)
			}
		}

		self.global_pin_block(hash)?;
		Ok(true)
	}

	fn global_pin_block(&mut self, hash: Block::Hash) -> Result<(), SubscriptionManagementError> {
		match self.global_blocks.entry(hash) {
			Entry::Occupied(mut occupied) => {
				*occupied.get_mut() += 1;
			},
			Entry::Vacant(vacant) => {
				self.backend
					.pin_block(hash)
					.map_err(|err| SubscriptionManagementError::Custom(err.to_string()))?;

				vacant.insert(1);
			},
		};
		Ok(())
	}

	fn global_unpin_block(&mut self, hash: Block::Hash) {
		if let Entry::Occupied(mut occupied) = self.global_blocks.entry(hash) {
			let counter = occupied.get_mut();
			if *counter == 1 {
				// Unpin the block from the backend.
				self.backend.unpin_block(hash);
				occupied.remove();
			} else {
				*counter -= 1;
			}
		}
	}

	fn unpin_block(
		&mut self,
		sub_id: &str,
		hash: Block::Hash,
	) -> Result<(), SubscriptionManagementError> {
		let Some(sub) = self.subs.get_mut(sub_id) else {
			return Err(SubscriptionManagementError::SubscriptionAbsent)
		};

		// Check that unpin was not called before and the block was pinned
		// for this subscription.
		if !sub.unregister_block(hash) {
			return Err(SubscriptionManagementError::BlockHashAbsent)
		}

		self.global_unpin_block(hash);
		Ok(())
	}

	fn lock_block(
		&mut self,
		sub_id: &str,
		hash: Block::Hash,
	) -> Result<BlockGuard<Block, BE>, SubscriptionManagementError> {
		let Some(sub) = self.subs.get(sub_id) else {
			return Err(SubscriptionManagementError::SubscriptionAbsent)
		};

		if !sub.contains_block(hash) {
			return Err(SubscriptionManagementError::BlockHashAbsent)
		}

		BlockGuard::new(hash, sub.runtime_updates, self.backend.clone())
	}
}

/// Manage block pinning / unpinning for subscription IDs.
pub struct SubscriptionManagement<Block: BlockT, BE: Backend<Block> + 'static> {
	/// Manage subscription by mapping the subscription ID
	/// to a set of block hashes.
	inner: RwLock<SubscriptionsInner<Block, BE>>,
}

impl<Block: BlockT, BE: Backend<Block> + 'static> SubscriptionManagement<Block, BE> {
	/// Construct a new [`SubscriptionManagement`].
	pub fn new(
		global_max_pinned_blocks: usize,
		local_max_pin_duration: Duration,
		backend: Arc<BE>,
	) -> Self {
		SubscriptionManagement {
			inner: RwLock::new(SubscriptionsInner::new(
				global_max_pinned_blocks,
				local_max_pin_duration,
				backend,
			)),
		}
	}

	/// Insert a new subscription ID.
	///
	/// If the subscription was not previously inserted, returns the receiver that is
	/// triggered upon the "Stop" event. Otherwise, if the subscription ID was already
	/// inserted returns none.
	pub fn insert_subscription(
		&self,
		sub_id: String,
		runtime_updates: bool,
	) -> Option<oneshot::Receiver<()>> {
		let mut inner = self.inner.write();
		inner.insert_subscription(sub_id, runtime_updates)
	}

	/// Remove the subscription ID with associated pinned blocks.
	pub fn remove_subscription(&self, sub_id: &str) {
		let mut inner = self.inner.write();
		inner.remove_subscription(sub_id)
	}

	/// The block is pinned in the backend only once when the block's hash is first encountered.
	///
	/// Each subscription is expected to call this method twice:
	/// - once from the `NewBlock` import
	/// - once from the `Finalized` import
	///
	/// Returns
	/// - Ok(true) if the subscription did not previously contain this block
	/// - Ok(false) if the subscription already contained this this
	/// - Error if the backend failed to pin the block or the subscription ID is invalid
	pub fn pin_block(
		&self,
		sub_id: &str,
		hash: Block::Hash,
	) -> Result<bool, SubscriptionManagementError> {
		let mut inner = self.inner.write();
		inner.pin_block(sub_id, hash)
	}

	/// Unpin the block from the subscription.
	///
	/// The last subscription that unpins the block is also unpinning the block
	/// from the backend.
	///
	/// This method is called only once per subscription.
	///
	/// Returns an error if the block is not pinned for the subscription or
	/// the subscription ID is invalid.
	pub fn unpin_block(
		&self,
		sub_id: &str,
		hash: Block::Hash,
	) -> Result<(), SubscriptionManagementError> {
		let mut inner = self.inner.write();
		inner.unpin_block(sub_id, hash)
	}

	/// Ensure the block remains pinned until the return object is dropped.
	///
	/// Returns a [`BlockGuard`] that pins and unpins the block hash in RAII manner.
	/// Returns an error if the block hash is not pinned for the subscription or
	/// the subscription ID is invalid.
	pub fn lock_block(
		&self,
		sub_id: &str,
		hash: Block::Hash,
	) -> Result<BlockGuard<Block, BE>, SubscriptionManagementError> {
		let mut inner = self.inner.write();
		inner.lock_block(sub_id, hash)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use futures::executor::block_on;
	use sc_block_builder::BlockBuilderProvider;
	use sp_consensus::BlockOrigin;
	use sp_core::H256;
	use substrate_test_runtime_client::{
		prelude::*, runtime::Block, Backend, ClientBlockImportExt,
	};

	#[test]
	fn subscription_check_id() {
		let subs = SubscriptionManagement::<Block, Backend>::new();
		let builder = TestClientBuilder::new();
		let backend = builder.backend();

		let id = "abc".to_string();
		let hash = H256::random();

		let handle = subs.get_subscription(&id);
		assert!(handle.is_none());

		let (_, handle) = subs.insert_subscription(id.clone(), false, 10, backend).unwrap();
		assert!(!handle.contains_block(&hash));

		subs.remove_subscription(&id);

		let handle = subs.get_subscription(&id);
		assert!(handle.is_none());
	}

	#[test]
	fn subscription_check_block() {
		let subs = SubscriptionManagement::<Block, Backend>::new();
		let builder = TestClientBuilder::new();
		let backend = builder.backend();
		let mut client = Arc::new(builder.build());

		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash = block.header.hash();
		block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();

		let id = "abc".to_string();

		// Check with subscription.
		let (_, handle) = subs.insert_subscription(id.clone(), false, 10, backend).unwrap();
		assert!(!handle.contains_block(&hash));
		assert!(!handle.unpin_block(&hash));

		handle.pin_block(hash).unwrap();
		assert!(handle.contains_block(&hash));
		// Unpin an invalid block.
		assert!(!handle.unpin_block(&H256::random()));

		// Unpin the valid block.
		assert!(handle.unpin_block(&hash));
		assert!(!handle.contains_block(&hash));
	}

	#[test]
	fn subscription_check_stop_event() {
		let subs = SubscriptionManagement::<Block, Backend>::new();
		let builder = TestClientBuilder::new();
		let backend = builder.backend();

		let id = "abc".to_string();

		// Check with subscription.
		let (mut rx_stop, handle) =
			subs.insert_subscription(id.clone(), false, 10, backend.clone()).unwrap();

		// Check the stop signal was not received.
		let res = rx_stop.try_recv().unwrap();
		assert!(res.is_none());

		// Inserting a second time returns None.
		let res = subs.insert_subscription(id.clone(), false, 10, backend);
		assert!(res.is_none());

		handle.stop();

		// Check the signal was received.
		let res = rx_stop.try_recv().unwrap();
		assert!(res.is_some());
	}

	#[test]
	fn subscription_check_data() {
		let subs = SubscriptionManagement::<Block, Backend>::new();
		let builder = TestClientBuilder::new();
		let backend = builder.backend();

		let id = "abc".to_string();
		let (_, handle) = subs.insert_subscription(id.clone(), false, 10, backend.clone()).unwrap();
		assert!(!handle.has_runtime_updates());

		let id2 = "abcd".to_string();
		let (_, handle) = subs.insert_subscription(id2.clone(), true, 10, backend).unwrap();
		assert!(handle.has_runtime_updates());
	}

	#[test]
	fn subscription_check_max_pinned() {
		let subs = SubscriptionManagement::<Block, Backend>::new();
		let builder = TestClientBuilder::new();
		let backend = builder.backend();
		let mut client = Arc::new(builder.build());

		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash = block.header.hash();
		block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();

		let id = "abc".to_string();
		let hash_2 = H256::random();
		let (_, handle) = subs.insert_subscription(id.clone(), false, 1, backend).unwrap();

		handle.pin_block(hash).unwrap();
		// The same block can be pinned multiple times.
		handle.pin_block(hash).unwrap();
		// Exceeded number of pinned blocks.
		handle.pin_block(hash_2).unwrap_err();
	}
}
