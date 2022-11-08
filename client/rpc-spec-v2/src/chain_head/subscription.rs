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
use std::collections::{hash_map::Entry, HashMap, HashSet};

#[derive(Debug)]
/// The subscription management error.
pub enum SubscriptionError {
	/// The subscription ID is invalid.
	InvalidSubId,
	/// The block hash is invalid.
	InvalidBlock,
}

/// Inner subscription data structure.
struct SubscriptionInner<Block: BlockT> {
	/// Signals the "Stop" event.
	pub tx_stop: Option<oneshot::Sender<()>>,
	/// The blocks pinned.
	pub blocks: HashSet<Block::Hash>,
}

impl<Block: BlockT> SubscriptionInner<Block> {
	/// Construct a new [`SubscriptionInner`].
	fn new(tx_stop: oneshot::Sender<()>) -> Self {
		SubscriptionInner { tx_stop: Some(tx_stop), blocks: HashSet::new() }
	}
}

/// Manage block pinning / unpinning for subscription IDs.
pub struct SubscriptionManagement<Block: BlockT> {
	/// Manage subscription by mapping the subscription ID
	/// to a set of block hashes.
	inner: RwLock<HashMap<String, SubscriptionInner<Block>>>,
}

impl<Block: BlockT> SubscriptionManagement<Block> {
	/// Construct a new [`SubscriptionManagement`].
	pub fn new() -> Self {
		SubscriptionManagement { inner: RwLock::new(HashMap::new()) }
	}

	/// Insert a new subscription ID.
	///
	/// Returns the receiver that is triggered when the "Stop" event should be generated.
	/// Returns error if the subscription ID was inserted multiple times.
	pub fn insert_subscription(
		&self,
		subscription_id: String,
	) -> Result<oneshot::Receiver<()>, SubscriptionError> {
		let mut subs = self.inner.write();

		let (tx_stop, rx_stop) = oneshot::channel();

		if let Entry::Vacant(entry) = subs.entry(subscription_id) {
			entry.insert(SubscriptionInner::new(tx_stop));
			Ok(rx_stop)
		} else {
			Err(SubscriptionError::InvalidSubId)
		}
	}

	/// Remove the subscription ID with associated pinned blocks.
	pub fn remove_subscription(&self, subscription_id: &String) {
		let mut subs = self.inner.write();
		subs.remove(subscription_id);
	}

	/// Pin a new block for the given subscription ID.
	///
	/// Fails if the subscription ID is not present.
	///
	/// # Note
	///
	/// It does not fail for pinning the same block multiple times.
	/// This is useful when having a `new_block` event followed
	/// by a `finalized` event.
	pub fn pin_block(
		&self,
		subscription_id: &String,
		hash: Block::Hash,
	) -> Result<(), SubscriptionError> {
		let mut subs = self.inner.write();

		match subs.get_mut(subscription_id) {
			Some(inner) => {
				inner.blocks.insert(hash);
				Ok(())
			},
			None => Err(SubscriptionError::InvalidSubId),
		}
	}

	/// Unpin a new block for the given subscription ID.
	///
	/// Fails if either the subscription ID or the block hash is not present.
	pub fn unpin_block(
		&self,
		subscription_id: &String,
		hash: &Block::Hash,
	) -> Result<(), SubscriptionError> {
		let mut subs = self.inner.write();

		match subs.get_mut(subscription_id) {
			Some(inner) =>
				if !inner.blocks.remove(hash) {
					Err(SubscriptionError::InvalidBlock)
				} else {
					Ok(())
				},
			None => Err(SubscriptionError::InvalidSubId),
		}
	}

	/// Check if the block hash is present for the provided subscription ID.
	///
	/// Fails if either the subscription ID or the block hash is not present.
	pub fn contains(
		&self,
		subscription_id: &String,
		hash: &Block::Hash,
	) -> Result<(), SubscriptionError> {
		let subs = self.inner.read();

		match subs.get(subscription_id) {
			Some(inner) =>
				if inner.blocks.contains(hash) {
					Ok(())
				} else {
					return Err(SubscriptionError::InvalidBlock)
				},
			None => return Err(SubscriptionError::InvalidSubId),
		}
	}

	/// Trigger the stop event for the current subscription.
	///
	/// This can happen on internal failure (ie, the pruning deleted the block from memory)
	/// or if the user exceeded the amount of available pinned blocks.
	pub fn stop(&self, subscription_id: &String) -> Result<(), SubscriptionError> {
		let mut subs = self.inner.write();

		match subs.get_mut(subscription_id) {
			Some(inner) => {
				if let Some(tx_stop) = inner.tx_stop.take() {
					let _ = tx_stop.send(());
				}
				Ok(())
			},
			None => return Err(SubscriptionError::InvalidSubId),
		}
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

		let res = subs.contains(&id, &hash);
		assert!(matches!(res, Err(SubscriptionError::InvalidSubId)));

		let _ = subs.insert_subscription(id.clone());
		let res = subs.contains(&id, &hash);
		assert!(matches!(res, Err(SubscriptionError::InvalidBlock)));

		subs.remove_subscription(&id);

		let res = subs.contains(&id, &hash);
		assert!(matches!(res, Err(SubscriptionError::InvalidSubId)));
	}

	#[test]
	fn subscription_check_block() {
		let subs = SubscriptionManagement::<Block>::new();

		let id = "abc".to_string();
		let hash = H256::random();

		// Check without subscription.
		let res = subs.pin_block(&id, hash);
		assert!(matches!(res, Err(SubscriptionError::InvalidSubId)));

		let res = subs.unpin_block(&id, &hash);
		assert!(matches!(res, Err(SubscriptionError::InvalidSubId)));

		// Check with subscription.
		let _ = subs.insert_subscription(id.clone());
		// No block pinned.
		let res = subs.contains(&id, &hash);
		assert!(matches!(res, Err(SubscriptionError::InvalidBlock)));

		let res = subs.unpin_block(&id, &hash);
		assert!(matches!(res, Err(SubscriptionError::InvalidBlock)));

		// Check with subscription and pinned block.
		let res = subs.pin_block(&id, hash);
		assert!(matches!(res, Ok(())));

		let res = subs.contains(&id, &hash);
		assert!(matches!(res, Ok(())));

		// Unpin an invalid block.
		let res = subs.unpin_block(&id, &H256::random());
		assert!(matches!(res, Err(SubscriptionError::InvalidBlock)));

		let res = subs.unpin_block(&id, &hash);
		assert!(matches!(res, Ok(())));

		// No block pinned.
		let res = subs.contains(&id, &hash);
		assert!(matches!(res, Err(SubscriptionError::InvalidBlock)));
	}

	#[test]
	fn subscription_check_stop_event() {
		let subs = SubscriptionManagement::<Block>::new();

		let id = "abc".to_string();

		// Check with subscription.
		let mut rx_stop = subs.insert_subscription(id.clone()).unwrap();

		// Check the stop signal was not received.
		let res = rx_stop.try_recv().unwrap();
		assert!(res.is_none());

		// Inserting a second time will error.
		let res = subs.insert_subscription(id.clone());
		assert!(matches!(res, Err(SubscriptionError::InvalidSubId)));

		// Stop must be successful.
		subs.stop(&id).unwrap();

		// Check the signal was received.
		let res = rx_stop.try_recv().unwrap();
		assert!(res.is_some());
	}
}
