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
	child_changes: Arc<Vec<(StorageKey, Vec<(StorageKey, Option<StorageData>)>)>>,
	filter: Option<HashSet<StorageKey>>,
	child_filters: Option<HashMap<StorageKey, Option<HashSet<StorageKey>>>>,
}

impl StorageChangeSet {
	/// Convert the change set into iterator over storage items.
	pub fn iter<'a>(&'a self)
		-> impl Iterator<Item=(Option<&'a StorageKey>, &'a StorageKey, Option<&'a StorageData>)> + 'a {
		let top = self.changes
			.iter()
			.filter(move |&(key, _)| match self.filter {
				Some(ref filter) => filter.contains(key),
				None => true,
			})
			.map(move |(k,v)| (None, k, v.as_ref()));
		let children = self.child_changes
			.iter()
			.filter_map(move |(sk, changes)| {
				if let Some(cf) = self.child_filters.as_ref() {
					if let Some(filter) = cf.get(sk) {
						Some(changes
							.iter()
							.filter(move |&(key, _)| match filter {
								Some(ref filter) => filter.contains(key),
								None => true,
							})
							.map(move |(k,v)| (Some(sk), k, v.as_ref())))
					} else { None }
				} else { None	}
			})
			.flatten();
		top.chain(children)
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
	child_listeners: HashMap<StorageKey, (
		HashMap<StorageKey, FnvHashSet<SubscriberId>>,
		FnvHashSet<SubscriberId>
	)>,
	sinks: FnvHashMap<SubscriberId, (
		mpsc::UnboundedSender<(Block::Hash, StorageChangeSet)>,
		Option<HashSet<StorageKey>>,
		Option<HashMap<StorageKey, Option<HashSet<StorageKey>>>>,
	)>,
}

impl<Block: BlockT> Default for StorageNotifications<Block> {
	fn default() -> Self {
		StorageNotifications {
			next_id: Default::default(),
			wildcard_listeners: Default::default(),
			listeners: Default::default(),
			child_listeners: Default::default(),
			sinks: Default::default(),
		}
	}
}

impl<Block: BlockT> StorageNotifications<Block> {
	/// Trigger notification to all listeners.
	///
	/// Note the changes are going to be filtered by listener's filter key.
	/// In fact no event might be sent if clients are not interested in the changes.
	pub fn trigger(
		&mut self,
		hash: &Block::Hash,
		changeset: impl Iterator<Item=(Vec<u8>, Option<Vec<u8>>)>,
		child_changeset: impl Iterator<
			Item=(Vec<u8>, impl Iterator<Item=(Vec<u8>, Option<Vec<u8>>)>)
		>,
	) {
		let has_wildcard = !self.wildcard_listeners.is_empty();

		// early exit if no listeners
		if !has_wildcard && self.listeners.is_empty() && self.child_listeners.is_empty() {
			return;
		}

		let mut subscribers = self.wildcard_listeners.clone();
		let mut changes = Vec::new();
		let mut child_changes = Vec::new();

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
		for (sk, changeset) in child_changeset {
			let sk = StorageKey(sk);
			if let Some((cl, cw)) = self.child_listeners.get(&sk) {
				let mut changes = Vec::new();
				for (k, v) in changeset {
					let k = StorageKey(k);
					let listeners = cl.get(&k);

					if let Some(ref listeners) = listeners {
						subscribers.extend(listeners.iter());
					}

					subscribers.extend(cw.iter());

					if !cw.is_empty() || listeners.is_some() {
						changes.push((k, v.map(StorageData)));
					}
				}
				if !changes.is_empty() {
					child_changes.push((sk, changes));
				}
			}
		}

		// Don't send empty notifications
		if changes.is_empty() && child_changes.is_empty() {
			return;
		}

		let changes = Arc::new(changes);
		let child_changes = Arc::new(child_changes);
		// Trigger the events
		for subscriber in subscribers {
			let should_remove = {
				let &(ref sink, ref filter, ref child_filters) = self.sinks.get(&subscriber)
					.expect("subscribers returned from self.listeners are always in self.sinks; qed");
				sink.unbounded_send((hash.clone(), StorageChangeSet {
					changes: changes.clone(),
					child_changes: child_changes.clone(),
					filter: filter.clone(),
					child_filters: child_filters.clone(),
				})).is_err()
			};

			if should_remove {
				self.remove_subscriber(subscriber);
			}
		}
	}

	fn remove_subscriber_from(
		subscriber: &SubscriberId,
		filters: &Option<HashSet<StorageKey>>,
		listeners: &mut HashMap<StorageKey, FnvHashSet<SubscriberId>>,
		wildcards: &mut FnvHashSet<SubscriberId>,
	){
		match filters {
			None => {
				wildcards.remove(subscriber);
			},
			Some(filters) => {

				for key in filters.iter() {
					let remove_key = match listeners.get_mut(key) {
						Some(ref mut set) => {
							set.remove(subscriber);
							set.is_empty()
						},
						None => false,
					};

					if remove_key {
						listeners.remove(key);
					}
				}
			}
		}
	}

	fn remove_subscriber(&mut self, subscriber: SubscriberId) {
		if let Some((_, filters, child_filters)) = self.sinks.remove(&subscriber) {
			Self::remove_subscriber_from(
				&subscriber,
				&filters,
				&mut self.listeners,
				&mut self.wildcard_listeners,
			);
			if let Some(child_filters) = child_filters.as_ref() {
				for (c_key, filters) in child_filters {

					if let Some((listeners, wildcards)) = self.child_listeners.get_mut(&c_key) {
						Self::remove_subscriber_from(
							&subscriber,
							&filters,
							&mut *listeners,
							&mut *wildcards,
						);

						if listeners.is_empty() && wildcards.is_empty() {
							self.child_listeners.remove(&c_key);
						}
					}
				}
			}
		}
	}

	fn listen_from(
		current_id: SubscriberId,
		filter_keys: &Option<impl AsRef<[StorageKey]>>,
		listeners: &mut HashMap<StorageKey, FnvHashSet<SubscriberId>>,
		wildcards: &mut FnvHashSet<SubscriberId>,
	) -> Option<HashSet<StorageKey>>
	{
		match filter_keys {
			None => {
				wildcards.insert(current_id);
				None
			},
			Some(keys) => Some(keys.as_ref().iter().map(|key| {
				listeners
					.entry(key.clone())
					.or_insert_with(Default::default)
					.insert(current_id);
				key.clone()
			}).collect())
		}
	}

	/// Start listening for particular storage keys.
	pub fn listen(
		&mut self,
		filter_keys: Option<&[StorageKey]>,
		filter_child_keys: Option<&[(StorageKey, Option<Vec<StorageKey>>)]>,
	) -> StorageEventStream<Block::Hash> {
		self.next_id += 1;
		let current_id = self.next_id;

		// add subscriber for every key
		let keys = Self::listen_from(
			current_id,
			&filter_keys,
			&mut self.listeners,
			&mut self.wildcard_listeners,
		);
		let child_keys = filter_child_keys.map(|filter_child_keys| {
			filter_child_keys.iter().map(|(c_key, o_keys)| {
				let (c_listeners, c_wildcards) = self.child_listeners
					.entry(c_key.clone())
					.or_insert_with(Default::default);

				(c_key.clone(), Self::listen_from(
					current_id,
					o_keys,
					&mut *c_listeners,
					&mut *c_wildcards,
				))
			}).collect()
		});


		// insert sink
		let (tx, rx) = mpsc::unbounded();
		self.sinks.insert(current_id, (tx, keys, child_keys));
		rx
	}
}

#[cfg(test)]
mod tests {
	use runtime_primitives::testing::{H256 as Hash, Block as RawBlock, ExtrinsicWrapper};
	use super::*;
	use futures::Stream;
	use std::iter::{empty, Empty};

	type TestChangeSet = (
		Vec<(StorageKey, Option<StorageData>)>,
		Vec<(StorageKey, Vec<(StorageKey, Option<StorageData>)>)>,
	);

	#[cfg(test)]
	impl From<TestChangeSet> for StorageChangeSet {
		fn from(changes: TestChangeSet) -> Self {
			// warning hardcoded child trie wildcard to test upon
			let child_filters = Some([
				(StorageKey(vec![4]), None),
				(StorageKey(vec![5]), None),
			].into_iter().cloned().collect());
			StorageChangeSet {
				changes: Arc::new(changes.0),
				child_changes: Arc::new(changes.1),
				filter: None,
				child_filters,
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
		let child_filter = [(StorageKey(vec![4]), None)];
		let mut recv = notifications.listen(None, Some(&child_filter[..])).wait();

		// when
		let changeset = vec![
			(vec![2], Some(vec![3])),
			(vec![3], None),
		];
		let c_changeset_1 = vec![
			(vec![5], Some(vec![4])),
			(vec![6], None),
		];
		let c_changeset = vec![(vec![4], c_changeset_1)];
		notifications.trigger(
			&Hash::from_low_u64_be(1),
			changeset.into_iter(),
			c_changeset.into_iter().map(|(a,b)| (a, b.into_iter())),
		);

		// then
		assert_eq!(recv.next().unwrap(), Ok((Hash::from_low_u64_be(1), (vec![
			(StorageKey(vec![2]), Some(StorageData(vec![3]))),
			(StorageKey(vec![3]), None),
		], vec![(StorageKey(vec![4]), vec![
			(StorageKey(vec![5]), Some(StorageData(vec![4]))),
			(StorageKey(vec![6]), None),
		])]).into())));
	}

	#[test]
	fn should_only_notify_interested_listeners() {
		// given
		let mut notifications = StorageNotifications::<Block>::default();
		let child_filter = [(StorageKey(vec![4]), Some(vec![StorageKey(vec![5])]))];
		let mut recv1 = notifications.listen(Some(&[StorageKey(vec![1])]), None).wait();
		let mut recv2 = notifications.listen(Some(&[StorageKey(vec![2])]), None).wait();
		let mut recv3 = notifications.listen(Some(&[]), Some(&child_filter)).wait();

		// when
		let changeset = vec![
			(vec![2], Some(vec![3])),
			(vec![1], None),
		];
		let c_changeset_1 = vec![
			(vec![5], Some(vec![4])),
			(vec![6], None),
		];

		let c_changeset = vec![(vec![4], c_changeset_1)];
		notifications.trigger(
			&Hash::from_low_u64_be(1),
			changeset.into_iter(),
			c_changeset.into_iter().map(|(a,b)| (a, b.into_iter())),
		);

		// then
		assert_eq!(recv1.next().unwrap(), Ok((Hash::from_low_u64_be(1), (vec![
			(StorageKey(vec![1]), None),
		], vec![]).into())));
		assert_eq!(recv2.next().unwrap(), Ok((Hash::from_low_u64_be(1), (vec![
			(StorageKey(vec![2]), Some(StorageData(vec![3]))),
		], vec![]).into())));
		assert_eq!(recv3.next().unwrap(), Ok((Hash::from_low_u64_be(1), (vec![],
		vec![
			(StorageKey(vec![4]), vec![(StorageKey(vec![5]), Some(StorageData(vec![4])))]),
		]).into())));

	}

	#[test]
	fn should_cleanup_subscribers_if_dropped() {
		// given
		let mut notifications = StorageNotifications::<Block>::default();
		{
			let child_filter = [(StorageKey(vec![4]), Some(vec![StorageKey(vec![5])]))];
			let _recv1 = notifications.listen(Some(&[StorageKey(vec![1])]), None).wait();
			let _recv2 = notifications.listen(Some(&[StorageKey(vec![2])]), None).wait();
			let _recv3 = notifications.listen(None, None).wait();
			let _recv4 = notifications.listen(None, Some(&child_filter)).wait();
			assert_eq!(notifications.listeners.len(), 2);
			assert_eq!(notifications.wildcard_listeners.len(), 2);
			assert_eq!(notifications.child_listeners.len(), 1);
		}

		// when
		let changeset = vec![
			(vec![2], Some(vec![3])),
			(vec![1], None),
		];
		let c_changeset = empty::<(_, Empty<_>)>();
		notifications.trigger(&Hash::from_low_u64_be(1), changeset.into_iter(), c_changeset);

		// then
		assert_eq!(notifications.listeners.len(), 0);
		assert_eq!(notifications.wildcard_listeners.len(), 0);
		assert_eq!(notifications.child_listeners.len(), 0);
	}

	#[test]
	fn should_not_send_empty_notifications() {
		// given
		let mut recv = {
			let mut notifications = StorageNotifications::<Block>::default();
			let recv = notifications.listen(None, None).wait();

			// when
			let changeset = vec![];
			let c_changeset = empty::<(_, Empty<_>)>();
			notifications.trigger(&Hash::from_low_u64_be(1), changeset.into_iter(), c_changeset);
			recv
		};

		// then
		assert_eq!(recv.next(), None);
	}
}
