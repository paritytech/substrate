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

use parking_lot::RwLock;
use sc_client_api::Backend;
use sp_runtime::traits::Block as BlockT;
use std::{sync::Arc, time::Duration};

mod error;
mod inner;

use self::inner::SubscriptionsInner;
pub use error::SubscriptionManagementError;
pub use inner::{BlockGuard, InsertedSubscriptionData};

/// Manage block pinning / unpinning for subscription IDs.
pub struct SubscriptionManagement<Block: BlockT, BE: Backend<Block>> {
	/// Manage subscription by mapping the subscription ID
	/// to a set of block hashes.
	inner: RwLock<SubscriptionsInner<Block, BE>>,
}

impl<Block: BlockT, BE: Backend<Block>> SubscriptionManagement<Block, BE> {
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
	) -> Option<InsertedSubscriptionData<Block>> {
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
