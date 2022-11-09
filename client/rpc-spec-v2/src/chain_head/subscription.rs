// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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
use sp_runtime::traits::Block as BlockT;
use std::{
	collections::{hash_map::Entry, HashMap, HashSet},
	sync::Arc,
};

/// Inner subscription data structure.
struct SubscriptionInner<Block: BlockT> {
	/// Signals the "Stop" event.
	tx_stop: Option<oneshot::Sender<()>>,
	/// The blocks pinned.
	blocks: HashSet<Block::Hash>,
}

/// Manage the blocks of a specific subscription ID.
#[derive(Clone)]
pub struct SubscriptionHandle<Block: BlockT> {
	inner: Arc<RwLock<SubscriptionInner<Block>>>,
}

impl<Block: BlockT> SubscriptionHandle<Block> {
	/// Construct a new [`SubscriptionHandle`].
	fn new(tx_stop: oneshot::Sender<()>) -> Self {
		SubscriptionHandle {
			inner: Arc::new(RwLock::new(SubscriptionInner {
				tx_stop: Some(tx_stop),
				blocks: HashSet::new(),
			})),
		}
	}

	/// Trigger the stop event for the current subscription.
	///
	/// This can happen on internal failure (ie, the pruning deleted the block from memory)
	/// or if the user exceeded the amount of available pinned blocks.
	pub fn stop(self) {
		let mut inner = self.inner.write();

		if let Some(tx_stop) = inner.tx_stop.take() {
			let _ = tx_stop.send(());
		}
	}

	/// Pin a new block for the current subscription ID.
	///
	/// Returns whether the value was newly inserted. That is:
	/// - If the set did not previously contain this value, `true` is returned.
	/// - If the set already contained this value, `false` is returned.
	pub fn pin_block(&self, hash: Block::Hash) -> bool {
		let mut inner = self.inner.write();
		inner.blocks.insert(hash)
	}

	/// Unpin a new block for the current subscription ID.
	///
	/// Returns whether the value was present in the set.
	pub fn unpin_block(&self, hash: &Block::Hash) -> bool {
		let mut inner = self.inner.write();
		inner.blocks.remove(hash)
	}

	/// Check if the block hash is present for the provided subscription ID.
	///
	/// Returns `true` if the set contains the block.
	pub fn contains_block(&self, hash: &Block::Hash) -> bool {
		let inner = self.inner.read();
		inner.blocks.contains(hash)
	}
}

/// Manage block pinning / unpinning for subscription IDs.
pub struct SubscriptionManagement<Block: BlockT> {
	/// Manage subscription by mapping the subscription ID
	/// to a set of block hashes.
	inner: RwLock<HashMap<String, SubscriptionHandle<Block>>>,
}

impl<Block: BlockT> SubscriptionManagement<Block> {
	/// Construct a new [`SubscriptionManagement`].
	pub fn new() -> Self {
		SubscriptionManagement { inner: RwLock::new(HashMap::new()) }
	}

	/// Insert a new subscription ID.
	///
	/// If the subscription was not previously inserted, the method returns a tuple of
	/// the receiver that is triggered upon the "Stop" event and the subscription
	/// handle. Otherwise, when the subscription ID was already inserted returns none.
	pub fn insert_subscription(
		&self,
		subscription_id: String,
	) -> Option<(oneshot::Receiver<()>, SubscriptionHandle<Block>)> {
		let mut subs = self.inner.write();

		if let Entry::Vacant(entry) = subs.entry(subscription_id) {
			let (tx_stop, rx_stop) = oneshot::channel();
			let handle = SubscriptionHandle::<Block>::new(tx_stop);
			entry.insert(handle.clone());
			Some((rx_stop, handle))
		} else {
			None
		}
	}

	/// Remove the subscription ID with associated pinned blocks.
	pub fn remove_subscription(&self, subscription_id: &String) {
		let mut subs = self.inner.write();
		subs.remove(subscription_id);
	}

	/// Obtain the specific subscription handle.
	pub fn get_subscription(&self, subscription_id: &String) -> Option<SubscriptionHandle<Block>> {
		let subs = self.inner.write();
		subs.get(subscription_id).map(|handle| Some(handle.clone())).flatten()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use sp_core::H256;
	use substrate_test_runtime_client::runtime::Block;

	#[test]
	fn subscription_check_id() {
		let subs = SubscriptionManagement::<Block>::new();

		let id = "abc".to_string();
		let hash = H256::random();

		let handle = subs.get_subscription(&id);
		assert!(handle.is_none());

		let (_, handle) = subs.insert_subscription(id.clone()).unwrap();
		assert!(!handle.contains_block(&hash));

		subs.remove_subscription(&id);

		let handle = subs.get_subscription(&id);
		assert!(handle.is_none());
	}

	#[test]
	fn subscription_check_block() {
		let subs = SubscriptionManagement::<Block>::new();

		let id = "abc".to_string();
		let hash = H256::random();

		// Check with subscription.
		let (_, handle) = subs.insert_subscription(id.clone()).unwrap();
		assert!(!handle.contains_block(&hash));
		assert!(!handle.unpin_block(&hash));

		handle.pin_block(hash);
		assert!(handle.contains_block(&hash));
		// Unpin an invalid block.
		assert!(!handle.unpin_block(&H256::random()));

		// Unpin the valid block.
		assert!(handle.unpin_block(&hash));
		assert!(!handle.contains_block(&hash));
	}

	#[test]
	fn subscription_check_stop_event() {
		let subs = SubscriptionManagement::<Block>::new();

		let id = "abc".to_string();

		// Check with subscription.
		let (mut rx_stop, sub_handle) = subs.insert_subscription(id.clone()).unwrap();

		// Check the stop signal was not received.
		let res = rx_stop.try_recv().unwrap();
		assert!(res.is_none());

		// Inserting a second time returns None.
		let res = subs.insert_subscription(id.clone());
		assert!(res.is_none());

		sub_handle.stop();

		// Check the signal was received.
		let res = rx_stop.try_recv().unwrap();
		assert!(res.is_some());
	}
}
