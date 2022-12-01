// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Storage notifications

use fnv::{FnvHashMap, FnvHashSet};
use futures::Stream;
use parking_lot::Mutex;
use prometheus_endpoint::{register, CounterVec, Opts, Registry as PrometheusRegistry, U64};
use sp_core::storage::{StorageData, StorageKey};
use sp_runtime::traits::Block as BlockT;
use sp_storage::StorageChangeSet;
use std::{
	collections::{HashMap, HashSet, VecDeque},
	pin::Pin,
	sync::Arc,
	task::Poll,
};

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
#[repr(transparent)]
struct SubscriberId(u64);

#[derive(Debug)]
enum NotificationKind {
	/// This new block immediately follows the block we've last seen.
	Incremental,
	/// This new block doesn't immediately follow the block we've last seen,
	/// or is the very first block for which we're sending the notifications.
	Reorganized,
}

/// An opaque notification about storage changes.
#[derive(Debug)]
pub struct StorageNotification<Hash> {
	/// The hash of the block.
	block_hash: Hash,

	/// A list of storage changes.
	///
	/// This is unfiltered and contains *all* of the changes in the block.
	all_changes: Arc<HashMap<StorageKey, Option<StorageData>>>,

	/// The type of notification.
	kind: NotificationKind,

	/// A set of keys to which this subscriber is subscribed to.
	subscribed_for: Arc<HashSet<StorageKey>>,
}

impl<Hash> StorageNotification<Hash> {
	/// Extracts the storage change set from this notification and/or the storage.
	pub fn get<Block, Backend, Storage>(self, client: &Storage) -> StorageChangeSet<Hash>
	where
		Storage: crate::StorageProvider<Block, Backend>,
		Backend: crate::backend::Backend<Block>,
		Block: BlockT<Hash = Hash>,
		Hash: Clone,
	{
		self.get_impl(|key| client.storage(self.block_hash.clone(), key).ok().flatten())
	}

	fn get_impl(
		&self,
		mut get_from_storage: impl FnMut(&StorageKey) -> Option<StorageData>,
	) -> StorageChangeSet<Hash>
	where
		Hash: Clone,
	{
		let mut changes = Vec::new();
		if matches!(self.kind, NotificationKind::Incremental) {
			// The new block immediately follows the previous block
			// so we don't have to fetch anything extra from the storage;
			// we only need to grab the changes we're interested in.
			changes = self
				.all_changes
				.iter()
				.filter_map(|(key, value)| {
					self.subscribed_for.contains(&key).then(|| (key.clone(), value.clone()))
				})
				.collect();
		} else {
			// The new block doesn't immediately follow the previous block
			// (or is the very first notification) so we have to fetch
			// the values from the storage.
			for key in &*self.subscribed_for {
				if let Some(value) = self.all_changes.get(key) {
					// One of the keys we care about was changed in this block,
					// so no need to fetch it from the storage.
					changes.push((key.clone(), value.clone()));
				} else {
					// The key we care about wasn't changed here, but it might
					// have been changed in one of the previous blocks,
					// so fetch it from the storage.
					let value = get_from_storage(key);
					changes.push((key.clone(), value));
				}
			}
		}

		StorageChangeSet { block: self.block_hash.clone(), changes }
	}
}

/// Manages storage subscriptions.
#[derive(Debug)]
pub struct StorageChangesForKeysHub<Hash> {
	metrics: Option<CounterVec<U64>>,
	subscriber_ids_for_key: HashMap<StorageKey, FnvHashSet<SubscriberId>>,
	subscriber_by_id: FnvHashMap<SubscriberId, Subscriber<Hash>>,
	dead_subscriber_ids: Arc<Mutex<Vec<SubscriberId>>>,
	last_block_hash: Hash,
	next_sid: u64,
	maximum_pending_messages: usize,
}

#[derive(Debug)]
struct Subscriber<Hash> {
	subscribed_for: Arc<HashSet<StorageKey>>,
	tx: futures::channel::mpsc::Sender<()>,
	message_queue: Arc<Mutex<VecDeque<StorageNotification<Hash>>>>,
}

/// A stream of storage change events.
pub struct StorageChangesForKeysStream<Hash> {
	sid: SubscriberId,
	rx: futures::channel::mpsc::Receiver<()>,
	message_queue: Arc<Mutex<VecDeque<StorageNotification<Hash>>>>,
	dead_subscriber_ids: Arc<Mutex<Vec<SubscriberId>>>,
}

impl<Hash> Drop for StorageChangesForKeysStream<Hash> {
	fn drop(&mut self) {
		self.dead_subscriber_ids.lock().push(self.sid);
	}
}

impl<Hash> Stream for StorageChangesForKeysStream<Hash> {
	type Item = StorageNotification<Hash>;
	fn poll_next(
		mut self: Pin<&mut Self>,
		cx: &mut std::task::Context<'_>,
	) -> Poll<Option<Self::Item>> {
		if let Some(item) = self.message_queue.lock().pop_front() {
			return Poll::Ready(Some(item))
		}

		loop {
			match Stream::poll_next(Pin::new(&mut self.rx), cx) {
				Poll::Pending => return Poll::Pending,
				Poll::Ready(None) => return Poll::Ready(None),
				Poll::Ready(Some(())) => {
					if let Some(item) = self.message_queue.lock().pop_front() {
						return Poll::Ready(Some(item))
					}

					// A spurious wakeup; poll again.
				},
			}
		}
	}
}

impl<Hash> StorageChangesForKeysHub<Hash>
where
	Hash: Clone + PartialEq,
{
	/// Creates a new notification hub for storage changes.
	pub fn new(
		maximum_pending_messages: usize,
		prometheus_registry: Option<PrometheusRegistry>,
		last_block_hash: Hash,
	) -> Self {
		let metrics = prometheus_registry.and_then(|r| {
			CounterVec::new(
				Opts::new(
					"substrate_storage_notification_subscribers",
					"Number of subscribers for storage changes (only specific keys)",
				),
				&["action"], // added | removed
			)
			.and_then(|g| register(g, &r))
			.ok()
		});

		Self {
			metrics,
			subscriber_ids_for_key: Default::default(),
			subscriber_by_id: Default::default(),
			dead_subscriber_ids: Default::default(),
			last_block_hash,
			next_sid: 0,
			maximum_pending_messages,
		}
	}

	/// Trigger notifications to all subscribers interested in given changes.
	pub fn trigger(
		&mut self,
		parent_block_hash: &Hash,
		block_hash: &Hash,
		all_changes: sp_state_machine::StorageCollection,
	) where
		Hash: Clone,
	{
		if self.subscriber_ids_for_key.is_empty() {
			self.last_block_hash = block_hash.clone();
			return
		}

		self.cull_dead_subscribers();

		let all_changes: HashMap<_, _> = all_changes
			.into_iter()
			.map(|(key, value)| (StorageKey(key), value.map(StorageData)))
			.collect();
		let all_changes = Arc::new(all_changes);

		if self.last_block_hash == *parent_block_hash {
			// This new block immediately follows the previous one, so we don't have
			// to trigger everyone; we can only trigger those subscribers whose filter
			// matches the changes that were made.
			let mut subscriber_ids: FnvHashSet<_> = Default::default();
			for (key, _) in &*all_changes {
				if let Some(subscriber_ids_for_this_key) = self.subscriber_ids_for_key.get(key) {
					subscriber_ids.extend(subscriber_ids_for_this_key.iter().copied());
				}
			}
			for sid in subscriber_ids {
				let subscriber = self.subscriber_by_id.get_mut(&sid)
				    .expect("`subscriber_by_id` and `subscriber_ids_for_key` are kept in sync hence this cannot fail; qed");

				let mut message_queue = subscriber.message_queue.lock();
				if message_queue.len() >= self.maximum_pending_messages {
					// This subscriber isn't ingesting the notifications fast enough;
					// let's have it just fetch whatever it needs from the storage
					// once it wakes up.
					message_queue.clear();
					message_queue.push_back(StorageNotification {
						block_hash: block_hash.clone(),
						all_changes: all_changes.clone(),
						kind: NotificationKind::Reorganized,
						subscribed_for: subscriber.subscribed_for.clone(),
					});
				} else {
					message_queue.push_back(StorageNotification {
						block_hash: block_hash.clone(),
						all_changes: all_changes.clone(),
						kind: NotificationKind::Incremental,
						subscribed_for: subscriber.subscribed_for.clone(),
					});
				}

				// This can only return an error if the channel is either full
				// or the receiver was dropped. We don't care either way.
				//
				// If it's full it's fine to ignore this error since
				// since we only use this channel to wake up the receiver,
				// and if it's disconnected then it would have added itself
				// to the dead subscribers list, so it will be culled anyway.
				let _ = subscriber.tx.try_send(());
			}
		} else {
			// This new block *doesn't* immediately follow the previous one,
			// so we need to trigger all of the subscribers.
			//
			// Some of the keys to which the subscribers are subscribed to
			// might have changed in one of the ancestor blocks; any key
			// which wasn't changed in this block will have to be fetched
			// from the storage by the subscribers.
			for (_, subscriber) in &mut self.subscriber_by_id {
				let mut message_queue = subscriber.message_queue.lock();

				// If there are any pending messages there's no point in keeping them
				// as at this point they're stale anyway.
				message_queue.clear();
				message_queue.push_back(StorageNotification {
					block_hash: block_hash.clone(),
					all_changes: all_changes.clone(),
					kind: NotificationKind::Reorganized,
					subscribed_for: subscriber.subscribed_for.clone(),
				});

				let _ = subscriber.tx.try_send(());
			}
		}

		self.last_block_hash = block_hash.clone();
	}

	fn cull_dead_subscribers(&mut self) {
		for sid in self.dead_subscriber_ids.lock().drain(..) {
			let subscriber = self.subscriber_by_id.remove(&sid)
			    .expect("`dead_subscriber_ids` can only have existing subscribers added to it hence this cannot fail; qed");

			for key in &*subscriber.subscribed_for {
				let sids = self.subscriber_ids_for_key.get_mut(key)
				    .expect("`subscriber_by_id` and `subscriber_ids_for_key` are kept in sync hence this cannot fail; qed");

				sids.remove(&sid);
				if sids.is_empty() {
					self.subscriber_ids_for_key.remove(key);
				}
			}

			if let Some(m) = self.metrics.as_ref() {
				m.with_label_values(&["removed"]).inc();
			}
		}
	}

	/// Start listening for particular storage keys.
	pub fn subscribe(&mut self, filter_keys: &[StorageKey]) -> StorageChangesForKeysStream<Hash> {
		let subscribed_for: Arc<HashSet<StorageKey>> =
			Arc::new(filter_keys.iter().cloned().collect());
		let sid = SubscriberId(self.next_sid);
		self.next_sid += 1;

		let mut message_queue = VecDeque::new();
		message_queue.push_back(StorageNotification {
			block_hash: self.last_block_hash.clone(),
			all_changes: Default::default(),
			kind: NotificationKind::Reorganized,
			subscribed_for: subscribed_for.clone(),
		});

		let (mut tx, rx) = futures::channel::mpsc::channel(0);
		let _ = tx.try_send(());

		let message_queue = Arc::new(Mutex::new(message_queue));
		for key in filter_keys {
			self.subscriber_ids_for_key.entry(key.clone()).or_default().insert(sid);
		}

		self.subscriber_by_id
			.insert(sid, Subscriber { subscribed_for, tx, message_queue: message_queue.clone() });

		let stream = StorageChangesForKeysStream {
			sid,
			rx,
			message_queue,
			dead_subscriber_ids: self.dead_subscriber_ids.clone(),
		};

		if let Some(m) = self.metrics.as_ref() {
			m.with_label_values(&["added"]).inc();
		}

		stream
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
	struct Hash(u8);

	// A simple test harness which converts all of the keys and values
	// to strings and mocks the storage to make testing easier.
	struct TestHarness {
		hub: StorageChangesForKeysHub<Hash>,
		storage: Arc<Mutex<HashMap<Hash, HashMap<Vec<u8>, Vec<u8>>>>>,
	}

	struct TestStream {
		storage: Arc<Mutex<HashMap<Hash, HashMap<Vec<u8>, Vec<u8>>>>>,
		stream: StorageChangesForKeysStream<Hash>,
	}

	type TestChangeSet = (Hash, Vec<(String, Option<String>)>);

	impl Default for TestHarness {
		fn default() -> Self {
			Self::new(usize::MAX)
		}
	}

	impl TestHarness {
		fn new(maximum_pending_messages: usize) -> Self {
			Self {
				hub: StorageChangesForKeysHub::new(maximum_pending_messages, None, Hash(0)),
				storage: Default::default(),
			}
		}

		fn insert(&mut self, parent_block: Hash, block: Hash, changes: Vec<(&str, Option<&str>)>) {
			let changes: Vec<_> = changes
				.into_iter()
				.map(|(key, value)| {
					(key.as_bytes().to_owned(), value.map(|value| value.as_bytes().to_owned()))
				})
				.collect();
			self.hub.trigger(&parent_block, &block, changes.clone());

			let mut storage = self.storage.lock();
			let mut storage_for_block = storage.get(&parent_block).cloned().unwrap_or_default();
			for (key, value) in changes {
				if let Some(value) = value {
					storage_for_block.insert(key, value);
				} else {
					storage_for_block.remove(&key);
				}
			}
			storage.insert(block, storage_for_block);
		}

		fn subscribe(&mut self, filter_keys: &[&str]) -> TestStream {
			let filter_keys: Vec<_> =
				filter_keys.iter().map(|key| StorageKey(key.as_bytes().to_owned())).collect();
			let stream = self.hub.subscribe(&filter_keys);

			TestStream { storage: self.storage.clone(), stream }
		}
	}

	impl TestStream {
		fn recv_all(&mut self) -> Vec<TestChangeSet> {
			use futures::{FutureExt, StreamExt};
			let storage = self.storage.lock();
			let mut list = Vec::new();
			while let Some(notif) = self.stream.next().now_or_never() {
				if let Some(notif) = notif {
					let empty = HashMap::new();
					let storage = storage.get(&notif.block_hash).unwrap_or(&empty);
					let mut notif = notif.get_impl(|key| {
						storage.get(&key.0).map(|value| StorageData(value.clone()))
					});

					notif.changes.sort();
					list.push((
						notif.block,
						notif
							.changes
							.into_iter()
							.map(|(key, value)| {
								(
									String::from_utf8(key.0).unwrap(),
									value.map(|value| String::from_utf8(value.0).unwrap()),
								)
							})
							.collect(),
					));
				}
			}
			list
		}
	}

	#[test]
	fn existing_values_are_sent_when_a_subscription_is_created() {
		let mut test = TestHarness::default();
		test.insert(Hash(0), Hash(1), vec![("A", Some("1"))]);
		assert_eq!(
			test.subscribe(&["A", "B"]).recv_all(),
			vec![(Hash(1), vec![("A".to_owned(), Some("1".to_owned())), ("B".to_owned(), None)])]
		);
	}

	#[test]
	fn notification_is_sent_even_if_there_are_no_existing_storage_entries_when_a_subscription_is_created(
	) {
		let mut test = TestHarness::default();
		test.insert(Hash(0), Hash(1), vec![("A", Some("1"))]);
		assert_eq!(
			test.subscribe(&["B"]).recv_all(),
			vec![(Hash(1), vec![("B".to_owned(), None)])]
		);
	}

	#[test]
	fn unrelated_changes_do_not_trigger_the_subscriber() {
		let mut test = TestHarness::default();
		let mut sub = test.subscribe(&["A"]);
		assert_eq!(sub.recv_all(), vec![(Hash(0), vec![("A".to_owned(), None)])]);
		test.insert(Hash(0), Hash(1), vec![("B", Some("1"))]);
		assert_eq!(sub.recv_all(), vec![]);
	}

	#[test]
	fn when_a_new_block_is_a_child_of_the_last_block_generate_messages_with_only_necessary_changes()
	{
		// Block tree:
		//   0 -> 1 -> 2 -> 3

		let mut test = TestHarness::default();
		let mut sub = test.subscribe(&["A", "B"]);
		assert_eq!(
			sub.recv_all(),
			vec![(Hash(0), vec![("A".to_owned(), None), ("B".to_owned(), None)])]
		);

		test.insert(Hash(0), Hash(1), vec![("A", Some("1"))]);
		test.insert(Hash(1), Hash(2), vec![("B", Some("2"))]);
		test.insert(Hash(2), Hash(3), vec![("C", Some("3"))]);
		test.insert(Hash(3), Hash(4), vec![("B", Some("4"))]);
		assert_eq!(
			sub.recv_all(),
			vec![
				(Hash(1), vec![("A".to_owned(), Some("1".to_owned()))]),
				(Hash(2), vec![("B".to_owned(), Some("2".to_owned()))]),
				(Hash(4), vec![("B".to_owned(), Some("4".to_owned()))])
			]
		);
	}

	#[test]
	fn when_a_new_block_is_not_a_child_of_the_last_block_generate_messages_with_all_subscribed_keys(
	) {
		// Block tree:
		//   0 -> 1 -> 3
		//     \> 2

		let mut test = TestHarness::default();
		test.insert(Hash(0), Hash(1), vec![("A", Some("1"))]);
		test.insert(Hash(0), Hash(2), vec![("B", Some("2"))]);

		let mut sub = test.subscribe(&["A", "B"]);
		// Initial notification with values fetched from storage.
		assert_eq!(
			sub.recv_all(),
			vec![(Hash(2), vec![("A".to_owned(), None), ("B".to_owned(), Some("2".to_owned())),])]
		);

		test.insert(Hash(1), Hash(3), vec![("C", Some("2"))]);
		// Fixup notification with values fetched from storage.
		assert_eq!(
			sub.recv_all(),
			vec![(Hash(3), vec![("A".to_owned(), Some("1".to_owned())), ("B".to_owned(), None),])]
		);
	}

	#[test]
	fn when_a_message_with_all_subscribed_keys_is_generated_all_other_pending_messages_are_dropped()
	{
		// Same as previous test; we just don't poll for the initial notification.
		let mut test = TestHarness::default();
		test.insert(Hash(0), Hash(1), vec![("A", Some("1"))]);
		test.insert(Hash(0), Hash(2), vec![("B", Some("2"))]);

		let mut sub = test.subscribe(&["A", "B"]);
		test.insert(Hash(1), Hash(3), vec![("C", Some("2"))]);
		assert_eq!(
			sub.recv_all(),
			vec![(Hash(3), vec![("A".to_owned(), Some("1".to_owned())), ("B".to_owned(), None),])]
		);
	}

	#[test]
	fn when_we_go_over_the_pending_message_limit_all_other_pending_messages_are_dropped_and_a_new_message_is_generated(
	) {
		let mut test = TestHarness::new(2); // Maximum of 2 pending messages.
		test.insert(Hash(0), Hash(1), vec![("A", Some("1"))]);

		let mut sub = test.subscribe(&["A", "B"]);
		sub.recv_all(); // Ignore the initial notification.

		test.insert(Hash(1), Hash(2), vec![("B", Some("2"))]);
		test.insert(Hash(2), Hash(3), vec![("B", Some("3"))]);
		test.insert(Hash(3), Hash(4), vec![("B", Some("4"))]); // This pushes us over limit.
		assert_eq!(
			sub.recv_all(),
			vec![(
				Hash(4),
				vec![
					("A".to_owned(), Some("1".to_owned())),
					("B".to_owned(), Some("4".to_owned())),
				]
			)]
		);
	}

	#[test]
	fn when_a_subscriber_is_dropped_its_removed_from_the_subscribers_maps() {
		let mut test = TestHarness::default();
		assert!(test.hub.subscriber_ids_for_key.is_empty());
		assert!(test.hub.subscriber_by_id.is_empty());
		assert!(test.hub.dead_subscriber_ids.lock().is_empty());
		let sub = test.subscribe(&["A"]);
		assert!(!test.hub.subscriber_ids_for_key.is_empty());
		assert!(!test.hub.subscriber_by_id.is_empty());
		assert!(test.hub.dead_subscriber_ids.lock().is_empty());
		std::mem::drop(sub);

		// This triggers garbage collection of the subscribers.
		test.insert(Hash(0), Hash(1), vec![("A", Some("1"))]);

		assert!(test.hub.subscriber_ids_for_key.is_empty());
		assert!(test.hub.subscriber_by_id.is_empty());
		assert!(test.hub.dead_subscriber_ids.lock().is_empty());
	}
}
