// Copyright 2017-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Storage notifications

use std::{
	collections::{HashSet, HashMap},
	sync::Arc,
};

use fnv::{FnvHashSet, FnvHashMap};
use futures::sync::mpsc;
use primitives::storage::{StorageKey, StorageData};
use runtime_primitives::traits::Block as BlockT;

/// Storage change set
#[derive(Debug)]
pub struct StorageChangeSet {
	changes: Arc<Vec<(StorageKey, Option<StorageData>)>>,
	filter: Option<HashSet<StorageKey>>,
}

impl StorageChangeSet {
	/// Convert the change set into iterator over storage items.
	pub fn iter<'a>(&'a self) -> impl Iterator<Item=&'a (StorageKey, Option<StorageData>)> + 'a {
		self.changes
			.iter()
			.filter(move |&(key, _)| match self.filter {
				Some(ref filter) => filter.contains(key),
				None => true,
			})
	}
}

/// Type that implements `futures::Stream` of storage change events.
pub type StorageEventStream<H> = mpsc::UnboundedReceiver<(H, StorageChangeSet)>;

type SubscriberId = u64;

/// Manages storage listeners.
#[derive(Debug)]
pub struct StorageNotifications<Block: BlockT> {
	next_id: SubscriberId,
	wildcard_listeners: FnvHashSet<SubscriberId>,
	listeners: HashMap<StorageKey, FnvHashSet<SubscriberId>>,
	sinks: FnvHashMap<SubscriberId, (
		mpsc::UnboundedSender<(Block::Hash, StorageChangeSet)>,
		Option<HashSet<StorageKey>>,
	)>,
}

impl<Block: BlockT> Default for StorageNotifications<Block> {
	fn default() -> Self {
		StorageNotifications {
			next_id: Default::default(),
			wildcard_listeners: Default::default(),
			listeners: Default::default(),
			sinks: Default::default(),
		}
	}
}

impl<Block: BlockT> StorageNotifications<Block> {
	/// Trigger notification to all listeners.
	///
	/// Note the changes are going to be filtered by listener's filter key.
	/// In fact no event might be sent if clients are not interested in the changes.
	pub fn trigger(&mut self, hash: &Block::Hash, changeset: impl Iterator<Item=(Vec<u8>, Option<Vec<u8>>)>) {
		let has_wildcard = !self.wildcard_listeners.is_empty();

		// early exit if no listeners
		if !has_wildcard && self.listeners.is_empty() {
			return;
		}

		let mut subscribers = self.wildcard_listeners.clone();
		let mut changes = Vec::new();

		// Collect subscribers and changes
		for (k, v) in changeset {
			let k = StorageKey(k);
			let listeners = self.listeners.get(&k);

			if let Some(ref listeners) = listeners {
				subscribers.extend(listeners.iter());
			}

			if has_wildcard || listeners.is_some() {
				changes.push((k, v.map(StorageData)));
			}
		}

		// Don't send empty notifications
		if changes.is_empty() {
			return;
		}

		let changes = Arc::new(changes);
		// Trigger the events
		for subscriber in subscribers {
			let should_remove = {
				let &(ref sink, ref filter) = self.sinks.get(&subscriber)
					.expect("subscribers returned from self.listeners are always in self.sinks; qed");
				sink.unbounded_send((hash.clone(), StorageChangeSet {
					changes: changes.clone(),
					filter: filter.clone(),
				})).is_err()
			};

			if should_remove {
				self.remove_subscriber(subscriber);
			}
		}
	}

	fn remove_subscriber(&mut self, subscriber: SubscriberId) {
		if let Some((_, filters)) = self.sinks.remove(&subscriber) {
			match filters {
				None => {
					self.wildcard_listeners.remove(&subscriber);
				},
				Some(filters) => {
					for key in filters {
						let remove_key = match self.listeners.get_mut(&key) {
							Some(ref mut set) => {
								set.remove(&subscriber);
								set.is_empty()
							},
							None => false,
						};

						if remove_key {
							self.listeners.remove(&key);
						}
					}
				},
			}
		}
	}

	/// Start listening for particular storage keys.
	pub fn listen(&mut self, filter_keys: Option<&[StorageKey]>) -> StorageEventStream<Block::Hash> {
		self.next_id += 1;

		// add subscriber for every key
		let keys = match filter_keys {
			None => {
				self.wildcard_listeners.insert(self.next_id);
				None
			},
			Some(keys) => Some(keys.iter().map(|key| {
				self.listeners
					.entry(key.clone())
					.or_insert_with(Default::default)
					.insert(self.next_id);
				key.clone()
			}).collect())
		};

		// insert sink
		let (tx, rx) = mpsc::unbounded();
		self.sinks.insert(self.next_id, (tx, keys));
		rx
	}
}

#[cfg(test)]
mod tests {
	use runtime_primitives::testing::{H256 as Hash, Block as RawBlock, ExtrinsicWrapper};
	use super::*;
	use futures::Stream;

	#[cfg(test)]
	impl From<Vec<(StorageKey, Option<StorageData>)>> for StorageChangeSet {
		fn from(changes: Vec<(StorageKey, Option<StorageData>)>) -> Self {
			StorageChangeSet {
				changes: Arc::new(changes),
				filter: None,
			}
		}
	}

	#[cfg(test)]
	impl PartialEq for StorageChangeSet {
		fn eq(&self, other: &Self) -> bool {
			self.iter().eq(other.iter())
		}
	}

	type Block = RawBlock<ExtrinsicWrapper<Hash>>;

	#[test]
	fn triggering_change_should_notify_wildcard_listeners() {
		// given
		let mut notifications = StorageNotifications::<Block>::default();
		let mut recv = notifications.listen(None).wait();

		// when
		let changeset = vec![
			(vec![2], Some(vec![3])),
			(vec![3], None),
		];
		notifications.trigger(&Hash::from_low_u64_be(1), changeset.into_iter());

		// then
		assert_eq!(recv.next().unwrap(), Ok((Hash::from_low_u64_be(1), vec![
			(StorageKey(vec![2]), Some(StorageData(vec![3]))),
			(StorageKey(vec![3]), None),
		].into())));
	}

	#[test]
	fn should_only_notify_interested_listeners() {
		// given
		let mut notifications = StorageNotifications::<Block>::default();
		let mut recv1 = notifications.listen(Some(&[StorageKey(vec![1])])).wait();
		let mut recv2 = notifications.listen(Some(&[StorageKey(vec![2])])).wait();

		// when
		let changeset = vec![
			(vec![2], Some(vec![3])),
			(vec![1], None),
		];
		notifications.trigger(&Hash::from_low_u64_be(1), changeset.into_iter());

		// then
		assert_eq!(recv1.next().unwrap(), Ok((Hash::from_low_u64_be(1), vec![
			(StorageKey(vec![1]), None),
		].into())));
		assert_eq!(recv2.next().unwrap(), Ok((Hash::from_low_u64_be(1), vec![
			(StorageKey(vec![2]), Some(StorageData(vec![3]))),
		].into())));
	}

	#[test]
	fn should_cleanup_subscribers_if_dropped() {
		// given
		let mut notifications = StorageNotifications::<Block>::default();
		{
			let _recv1 = notifications.listen(Some(&[StorageKey(vec![1])])).wait();
			let _recv2 = notifications.listen(Some(&[StorageKey(vec![2])])).wait();
			let _recv3 = notifications.listen(None).wait();
			assert_eq!(notifications.listeners.len(), 2);
			assert_eq!(notifications.wildcard_listeners.len(), 1);
		}

		// when
		let changeset = vec![
			(vec![2], Some(vec![3])),
			(vec![1], None),
		];
		notifications.trigger(&Hash::from_low_u64_be(1), changeset.into_iter());

		// then
		assert_eq!(notifications.listeners.len(), 0);
		assert_eq!(notifications.wildcard_listeners.len(), 0);
	}

	#[test]
	fn should_not_send_empty_notifications() {
		// given
		let mut recv = {
			let mut notifications = StorageNotifications::<Block>::default();
			let recv = notifications.listen(None).wait();

			// when
			let changeset = vec![];
			notifications.trigger(&Hash::from_low_u64_be(1), changeset.into_iter());
			recv
		};

		// then
		assert_eq!(recv.next(), None);
	}
}
