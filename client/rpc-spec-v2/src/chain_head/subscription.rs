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

	/// Get the timestamp of the oldest inserted block.
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
	use sc_block_builder::BlockBuilderProvider;
	use sc_service::client::new_in_mem;
	use sp_consensus::BlockOrigin;
	use sp_core::{testing::TaskExecutor, H256};
	use substrate_test_runtime_client::{
		prelude::*,
		runtime::{Block, RuntimeApi},
		Client, ClientBlockImportExt, GenesisInit,
	};

	fn init_backend() -> (
		Arc<sc_client_api::in_mem::Backend<Block>>,
		Arc<Client<sc_client_api::in_mem::Backend<Block>>>,
	) {
		let backend = Arc::new(sc_client_api::in_mem::Backend::new());
		let executor = substrate_test_runtime_client::new_native_executor();
		let client_config = sc_service::ClientConfig::default();
		let genesis_block_builder = sc_service::GenesisBlockBuilder::new(
			&substrate_test_runtime_client::GenesisParameters::default().genesis_storage(),
			!client_config.no_genesis,
			backend.clone(),
			executor.clone(),
		)
		.unwrap();
		let client = Arc::new(
			new_in_mem::<_, Block, _, RuntimeApi>(
				backend.clone(),
				executor,
				genesis_block_builder,
				None,
				None,
				None,
				Box::new(TaskExecutor::new()),
				client_config,
			)
			.unwrap(),
		);
		(backend, client)
	}

	#[test]
	fn sub_state_register_twice() {
		let mut sub_state = SubscriptionState::<Block> {
			runtime_updates: false,
			tx_stop: None,
			blocks: Default::default(),
		};

		let hash = H256::random();
		assert_eq!(sub_state.register_block(hash), true);
		let block_state = sub_state.blocks.get(&hash).unwrap();
		// Did not call `register_block` twice.
		assert_eq!(block_state.can_unregister, false);
		assert_eq!(block_state.was_unpinned, false);

		assert_eq!(sub_state.register_block(hash), false);
		let block_state = sub_state.blocks.get(&hash).unwrap();
		assert_eq!(block_state.can_unregister, true);
		assert_eq!(block_state.was_unpinned, false);

		// Block is no longer tracked when: `register_block` is called twice and
		// `unregister_block` is called once.
		assert_eq!(sub_state.unregister_block(hash), true);
		let block_state = sub_state.blocks.get(&hash);
		assert!(block_state.is_none());
	}

	#[test]
	fn sub_state_register_unregister() {
		let mut sub_state = SubscriptionState::<Block> {
			runtime_updates: false,
			tx_stop: None,
			blocks: Default::default(),
		};

		let hash = H256::random();
		// Block was not registered before.
		assert_eq!(sub_state.unregister_block(hash), false);

		assert_eq!(sub_state.register_block(hash), true);
		let block_state = sub_state.blocks.get(&hash).unwrap();
		// Did not call `register_block` twice.
		assert_eq!(block_state.can_unregister, false);
		assert_eq!(block_state.was_unpinned, false);

		// Unregister block before the second `register_block`.
		assert_eq!(sub_state.unregister_block(hash), true);
		let block_state = sub_state.blocks.get(&hash).unwrap();
		assert_eq!(block_state.can_unregister, false);
		assert_eq!(block_state.was_unpinned, true);

		assert_eq!(sub_state.register_block(hash), false);
		let block_state = sub_state.blocks.get(&hash);
		assert!(block_state.is_none());

		// Block is no longer tracked when: `register_block` is called twice and
		// `unregister_block` is called once.
		assert_eq!(sub_state.unregister_block(hash), false);
		let block_state = sub_state.blocks.get(&hash);
		assert!(block_state.is_none());
	}

	#[test]
	fn subscription_lock_block() {
		let builder = TestClientBuilder::new();
		let backend = builder.backend();
		let mut subs = SubscriptionsInner::new(10, Duration::from_secs(10), backend);

		let id = "abc".to_string();
		let hash = H256::random();

		// Subscription not inserted.
		let err = subs.lock_block(&id, hash).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::SubscriptionAbsent);

		let _stop = subs.insert_subscription(id.clone(), true).unwrap();
		// Cannot insert the same subscription ID twice.
		assert!(subs.insert_subscription(id.clone(), true).is_none());

		// No block hash.
		let err = subs.lock_block(&id, hash).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::BlockHashAbsent);

		subs.remove_subscription(&id);

		// No subscription.
		let err = subs.lock_block(&id, hash).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::SubscriptionAbsent);
	}

	#[test]
	fn subscription_check_block() {
		let (backend, mut client) = init_backend();

		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();

		let mut subs = SubscriptionsInner::new(10, Duration::from_secs(10), backend);
		let id = "abc".to_string();

		let _stop = subs.insert_subscription(id.clone(), true).unwrap();

		// First time we are pinning the block.
		assert_eq!(subs.pin_block(&id, hash).unwrap(), true);

		let block = subs.lock_block(&id, hash).unwrap();
		// Subscription started with runtime updates
		assert_eq!(block.has_runtime_updates(), true);

		let invalid_id = "abc-invalid".to_string();
		let err = subs.unpin_block(&invalid_id, hash).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::SubscriptionAbsent);

		// Unpin the block.
		subs.unpin_block(&id, hash).unwrap();
		let err = subs.lock_block(&id, hash).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::BlockHashAbsent);
	}

	#[test]
	fn subscription_ref_count() {
		let (backend, mut client) = init_backend();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();

		let mut subs = SubscriptionsInner::new(10, Duration::from_secs(10), backend);
		let id = "abc".to_string();

		let _stop = subs.insert_subscription(id.clone(), true).unwrap();
		assert_eq!(subs.pin_block(&id, hash).unwrap(), true);
		// Check the global ref count.
		assert_eq!(*subs.global_blocks.get(&hash).unwrap(), 1);
		// Ensure the block propagated to the subscription.
		subs.subs.get(&id).unwrap().blocks.get(&hash).unwrap();

		// Insert the block for the same subscription again (simulate NewBlock + Finalized pinning)
		assert_eq!(subs.pin_block(&id, hash).unwrap(), false);
		// Check the global ref count should not get incremented.
		assert_eq!(*subs.global_blocks.get(&hash).unwrap(), 1);

		// Ensure the hash propagates for the second subscription.
		let id_second = "abcd".to_string();
		let _stop = subs.insert_subscription(id_second.clone(), true).unwrap();
		assert_eq!(subs.pin_block(&id_second, hash).unwrap(), true);
		// Check the global ref count.
		assert_eq!(*subs.global_blocks.get(&hash).unwrap(), 2);
		// Ensure the block propagated to the subscription.
		subs.subs.get(&id_second).unwrap().blocks.get(&hash).unwrap();

		subs.unpin_block(&id, hash).unwrap();
		assert_eq!(*subs.global_blocks.get(&hash).unwrap(), 1);
		// Cannot unpin a block twice for the same subscription.
		let err = subs.unpin_block(&id, hash).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::BlockHashAbsent);

		subs.unpin_block(&id_second, hash).unwrap();
		// Block unregistered from the memory.
		assert!(subs.global_blocks.get(&hash).is_none());
	}

	#[test]
	fn subscription_remove_subscription() {
		let (backend, mut client) = init_backend();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_1 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_2 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_3 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();

		let mut subs = SubscriptionsInner::new(10, Duration::from_secs(10), backend);
		let id_1 = "abc".to_string();
		let id_2 = "abcd".to_string();

		// Pin all blocks for the first subscription.
		let _stop = subs.insert_subscription(id_1.clone(), true).unwrap();
		assert_eq!(subs.pin_block(&id_1, hash_1).unwrap(), true);
		assert_eq!(subs.pin_block(&id_1, hash_2).unwrap(), true);
		assert_eq!(subs.pin_block(&id_1, hash_3).unwrap(), true);

		// Pin only block 2 for the second subscription.
		let _stop = subs.insert_subscription(id_2.clone(), true).unwrap();
		assert_eq!(subs.pin_block(&id_2, hash_2).unwrap(), true);

		// Check reference count.
		assert_eq!(*subs.global_blocks.get(&hash_1).unwrap(), 1);
		assert_eq!(*subs.global_blocks.get(&hash_2).unwrap(), 2);
		assert_eq!(*subs.global_blocks.get(&hash_3).unwrap(), 1);

		subs.remove_subscription(&id_1);

		assert!(subs.global_blocks.get(&hash_1).is_none());
		assert_eq!(*subs.global_blocks.get(&hash_2).unwrap(), 1);
		assert!(subs.global_blocks.get(&hash_3).is_none());

		subs.remove_subscription(&id_2);

		assert!(subs.global_blocks.get(&hash_2).is_none());
		assert_eq!(subs.global_blocks.len(), 0);
	}

	#[test]
	fn subscription_check_limits() {
		let (backend, mut client) = init_backend();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_1 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_2 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_3 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();

		// Maximum number of pinned blocks is 2.
		let mut subs = SubscriptionsInner::new(2, Duration::from_secs(10), backend);
		let id_1 = "abc".to_string();
		let id_2 = "abcd".to_string();

		// Both subscriptions can pin the maximum limit.
		let _stop = subs.insert_subscription(id_1.clone(), true).unwrap();
		assert_eq!(subs.pin_block(&id_1, hash_1).unwrap(), true);
		assert_eq!(subs.pin_block(&id_1, hash_2).unwrap(), true);

		let _stop = subs.insert_subscription(id_2.clone(), true).unwrap();
		assert_eq!(subs.pin_block(&id_2, hash_1).unwrap(), true);
		assert_eq!(subs.pin_block(&id_2, hash_2).unwrap(), true);

		// Check reference count.
		assert_eq!(*subs.global_blocks.get(&hash_1).unwrap(), 2);
		assert_eq!(*subs.global_blocks.get(&hash_2).unwrap(), 2);

		// Block 3 pinning will exceed the limit and both subscriptions
		// are terminated because no subscription with older blocks than 10
		// seconds are present.
		let err = subs.pin_block(&id_1, hash_3).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::ExceededLimits);

		// Ensure both subscriptions are removed.
		let err = subs.lock_block(&id_1, hash_1).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::SubscriptionAbsent);

		let err = subs.lock_block(&id_2, hash_1).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::SubscriptionAbsent);

		assert!(subs.global_blocks.get(&hash_1).is_none());
		assert!(subs.global_blocks.get(&hash_2).is_none());
		assert!(subs.global_blocks.get(&hash_3).is_none());
		assert_eq!(subs.global_blocks.len(), 0);
	}

	#[test]
	fn subscription_check_limits_with_duration() {
		let (backend, mut client) = init_backend();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_1 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_2 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();
		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;
		let hash_3 = block.header.hash();
		futures::executor::block_on(client.import(BlockOrigin::Own, block.clone())).unwrap();

		// Maximum number of pinned blocks is 2 and maximum pin duration is 5 second.
		let mut subs = SubscriptionsInner::new(2, Duration::from_secs(5), backend);
		let id_1 = "abc".to_string();
		let id_2 = "abcd".to_string();

		let _stop = subs.insert_subscription(id_1.clone(), true).unwrap();
		assert_eq!(subs.pin_block(&id_1, hash_1).unwrap(), true);
		assert_eq!(subs.pin_block(&id_1, hash_2).unwrap(), true);

		// Maximum pin duration is 5 second, sleep 5 seconds to ensure we clean up
		// the first subscription.
		std::thread::sleep(std::time::Duration::from_secs(5));

		let _stop = subs.insert_subscription(id_2.clone(), true).unwrap();
		assert_eq!(subs.pin_block(&id_2, hash_1).unwrap(), true);

		// Check reference count.
		assert_eq!(*subs.global_blocks.get(&hash_1).unwrap(), 2);
		assert_eq!(*subs.global_blocks.get(&hash_2).unwrap(), 1);

		// Second subscription has only 1 block pinned. Only the first subscription is terminated.
		let err = subs.pin_block(&id_1, hash_3).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::ExceededLimits);

		// Ensure both subscriptions are removed.
		let err = subs.lock_block(&id_1, hash_1).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::SubscriptionAbsent);

		let _block_guard = subs.lock_block(&id_2, hash_1).unwrap();

		assert_eq!(*subs.global_blocks.get(&hash_1).unwrap(), 1);
		assert!(subs.global_blocks.get(&hash_2).is_none());
		assert!(subs.global_blocks.get(&hash_3).is_none());
		assert_eq!(subs.global_blocks.len(), 1);

		// Force second subscription to get terminated.
		assert_eq!(subs.pin_block(&id_2, hash_2).unwrap(), true);
		let err = subs.pin_block(&id_2, hash_3).unwrap_err();
		assert_eq!(err, SubscriptionManagementError::ExceededLimits);

		assert!(subs.global_blocks.get(&hash_1).is_none());
		assert!(subs.global_blocks.get(&hash_2).is_none());
		assert!(subs.global_blocks.get(&hash_3).is_none());
		assert_eq!(subs.global_blocks.len(), 0);
	}

	#[test]
	fn subscription_check_stop_event() {
		let builder = TestClientBuilder::new();
		let backend = builder.backend();
		let mut subs = SubscriptionsInner::new(10, Duration::from_secs(10), backend);

		let id = "abc".to_string();

		let mut rx_stop = subs.insert_subscription(id.clone(), true).unwrap();

		// Check the stop signal was not received.
		let res = rx_stop.try_recv().unwrap();
		assert!(res.is_none());

		let sub = subs.subs.get_mut(&id).unwrap();
		sub.stop();

		// Check the signal was received.
		let res = rx_stop.try_recv().unwrap();
		assert!(res.is_some());
	}
}
