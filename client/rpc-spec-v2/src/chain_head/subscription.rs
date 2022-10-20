use parking_lot::RwLock;
use sp_runtime::traits::Block as BlockT;
use std::collections::{hash_map::Entry, HashMap, HashSet};

/// The subscription management error.
pub enum SubscriptionError {
	/// The subscription ID is invalid.
	InvalidSubId,
	/// The block hash is invalid.
	InvalidBlock,
}

/// Manage block pinning / unpinning for subscription IDs.
pub struct SubscriptionManagement<Block: BlockT> {
	/// Manage subscription by mapping the subscription ID
	/// to a set of block hashes.
	inner: RwLock<HashMap<String, HashSet<Block::Hash>>>,
}

impl<Block: BlockT> SubscriptionManagement<Block> {
	/// Construct a new [`SubscriptionManagement`].
	pub fn new() -> Self {
		SubscriptionManagement { inner: RwLock::new(HashMap::new()) }
	}

	/// Insert a new subscription ID if not already present.
	pub fn insert_subscription(&self, subscription_id: String) {
		let mut subs = self.inner.write();

		if let Entry::Vacant(entry) = subs.entry(subscription_id) {
			entry.insert(Default::default());
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
			Some(set) => {
				set.insert(hash);
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
			Some(set) =>
				if !set.remove(hash) {
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
			Some(set) =>
				if !set.contains(hash) {
					return Err(SubscriptionError::InvalidBlock)
				} else {
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

		subs.insert_subscription(id.clone());
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
		let res = subs.pin_block(&id, hash.clone());
		assert!(matches!(res, Err(SubscriptionError::InvalidSubId)));

		let res = subs.unpin_block(&id, &hash);
		assert!(matches!(res, Err(SubscriptionError::InvalidSubId)));

		// Check with subscription.
		subs.insert_subscription(id.clone());
		// No block pinned.
		let res = subs.contains(&id, &hash);
		assert!(matches!(res, Err(SubscriptionError::InvalidBlock)));

		let res = subs.unpin_block(&id, &hash);
		assert!(matches!(res, Err(SubscriptionError::InvalidBlock)));

		// Check with subscription and pinned block.
		let res = subs.pin_block(&id, hash.clone());
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
}
