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

use super::*;

use fnv::{FnvHashMap, FnvHashSet};
use futures::channel::mpsc::TrySendError;
use prometheus_endpoint::{register, CounterVec, Opts, U64};

use sc_utils::{
	id_sequence::{IDSequence, SeqID},
	mpsc,
	mpsc::TracingUnboundedSender,
	pubsub_to_remove::{SubsBase, Subscribe, Unsubscribe},
};

use super::keys::{PrintChildKeys, PrintKeys};

type SubscriberId = SeqID;

type SubscribersGauge = CounterVec<U64>;

pub(super) struct SubscribeOp<'a, Hash> {
	pub filter_keys: Option<&'a [StorageKey]>,
	pub filter_child_keys: Option<&'a [(StorageKey, Option<Vec<StorageKey>>)]>,
	pub tx: mpsc::TracingUnboundedSender<Notification<Hash>>,
}

#[derive(Debug)]
pub(super) struct StorageNotificationsImpl<Hash> {
	pub(super) metrics: Option<SubscribersGauge>,
	pub(super) id_sequence: IDSequence,
	pub(super) wildcard_listeners: FnvHashSet<SubscriberId>,
	pub(super) listeners: HashMap<StorageKey, FnvHashSet<SubscriberId>>,
	pub(super) child_listeners: HashMap<
		StorageKey,
		(HashMap<StorageKey, FnvHashSet<SubscriberId>>, FnvHashSet<SubscriberId>),
	>,
	pub(super) sinks: FnvHashMap<SubscriberId, SubscriberSink<Hash>>,
}

#[derive(Debug)]
pub(super) struct SubscriberSink<Hash> {
	subs_id: SubscriberId,
	tx: TracingUnboundedSender<Notification<Hash>>,
	keys: Keys,
	child_keys: ChildKeys,
	was_triggered: bool,
}

impl<Hash> Drop for SubscriberSink<Hash> {
	fn drop(&mut self) {
		if !self.was_triggered {
			log::trace!(
				target: "storage_notifications",
				"Listener was never triggered: id={}, keys={:?}, child_keys={:?}",
				self.subs_id,
				PrintKeys(&self.keys),
				PrintChildKeys(&self.child_keys),
			);
		}
	}
}

impl<Hash> SubscriberSink<Hash> {
	fn new(
		subs_id: SubscriberId,
		tx: TracingUnboundedSender<Notification<Hash>>,
		keys: Keys,
		child_keys: ChildKeys,
	) -> Self {
		Self { subs_id, tx, keys, child_keys, was_triggered: false }
	}

	fn send(
		&mut self,
		hash: Hash,
		changes: Arc<[(StorageKey, Option<StorageData>)]>,
		child_changes: Arc<[(StorageKey, Vec<(StorageKey, Option<StorageData>)>)]>,
	) -> Result<(), TrySendError<Notification<Hash>>> {
		self.was_triggered = true;

		let storage_change_set = StorageChangeSet {
			changes,
			child_changes,
			filter: self.keys.clone(),
			child_filters: self.child_keys.clone(),
		};

		let item = (hash, storage_change_set);

		self.tx.unbounded_send(item)
	}

	fn is_closed(&self) -> bool {
		self.tx.is_closed()
	}
}

impl<Hash> StorageNotificationsImpl<Hash> {
	pub(super) fn new(prometheus_registry: Option<PrometheusRegistry>) -> Self {
		let metrics = prometheus_registry.and_then(|r| {
			CounterVec::new(
				Opts::new(
					"substrate_storage_notification_subscribers",
					"Number of subscribers in storage notification sytem",
				),
				&["action"], // added | removed
			)
			.and_then(|g| register(g, &r))
			.ok()
		});

		StorageNotificationsImpl { metrics, ..Default::default() }
	}
}

impl<Hash> Default for StorageNotificationsImpl<Hash> {
	fn default() -> Self {
		Self {
			metrics: Default::default(),
			id_sequence: Default::default(),
			wildcard_listeners: Default::default(),
			listeners: Default::default(),
			child_listeners: Default::default(),
			sinks: Default::default(),
		}
	}
}

impl<H> SubsBase for StorageNotificationsImpl<H> {
	type SubsID = SubscriberId;
}

impl<H> Unsubscribe for StorageNotificationsImpl<H> {
	fn unsubscribe(&mut self, subs_id: &Self::SubsID) {
		let _ = self.remove_subscriber(*subs_id);
	}
}

impl<'a, Hash> Subscribe<SubscribeOp<'a, Hash>> for StorageNotificationsImpl<Hash> {
	fn subscribe(&mut self, subs_op: SubscribeOp<'a, Hash>) -> Self::SubsID {
		let subs_id = self.id_sequence.next_id();

		let SubscribeOp { filter_keys, filter_child_keys, tx } = subs_op;

		let keys = Self::listen_from(
			subs_id,
			filter_keys.as_ref(),
			&mut self.listeners,
			&mut self.wildcard_listeners,
		);

		let child_keys = filter_child_keys.map(|filter_child_keys| {
			filter_child_keys
				.iter()
				.map(|(c_key, o_keys)| {
					let (c_listeners, c_wildcards) =
						self.child_listeners.entry(c_key.clone()).or_insert_with(Default::default);

					(
						c_key.clone(),
						Self::listen_from(
							subs_id,
							o_keys.as_ref(),
							&mut *c_listeners,
							&mut *c_wildcards,
						),
					)
				})
				.collect()
		});

		if let Some(m) = self.metrics.as_ref() {
			m.with_label_values(&[&"added"]).inc();
		}

		assert!(self.sinks.insert(subs_id, SubscriberSink::new(subs_id, tx, keys,child_keys)).is_none(), "
			Each `subs_id` is taken from `self.id_sequence.next_id()`.
			If we have a duplicate key here, it's either the implementation of `IDSequence` was broken, or we've overflowed `u64`.
			We are not likely to overflow an `u64`.");

		subs_id
	}
}

impl<Hash> StorageNotificationsImpl<Hash> {
	fn listen_from(
		current_id: SubscriberId,
		filter_keys: Option<impl AsRef<[StorageKey]>>,
		listeners: &mut HashMap<StorageKey, FnvHashSet<SubscriberId>>,
		wildcards: &mut FnvHashSet<SubscriberId>,
	) -> Keys {
		match filter_keys {
			None => {
				wildcards.insert(current_id);
				None
			},
			Some(keys) => Some(
				keys.as_ref()
					.iter()
					.map(|key| {
						listeners
							.entry(key.clone())
							.or_insert_with(Default::default)
							.insert(current_id);
						key.clone()
					})
					.collect(),
			),
		}
	}
}

impl<Hash> StorageNotificationsImpl<Hash> {
	pub(super) fn trigger(
		&mut self,
		hash: &Hash,
		changeset: impl Iterator<Item = (Vec<u8>, Option<Vec<u8>>)>,
		child_changeset: impl Iterator<
			Item = (Vec<u8>, impl Iterator<Item = (Vec<u8>, Option<Vec<u8>>)>),
		>,
	) where
		Hash: Clone,
	{
		let has_wildcard = !self.wildcard_listeners.is_empty();

		// early exit if no listeners
		if !has_wildcard && self.listeners.is_empty() && self.child_listeners.is_empty() {
			return
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
			return
		}

		let changes = Arc::<[_]>::from(changes);
		let child_changes = Arc::<[_]>::from(child_changes);
		// Trigger the events

		self.sinks.iter_mut().for_each(|(subs_id, sink)| {
			let _should_remove = {
				if subscribers.contains(subs_id) {
					sink.send(hash.clone(), changes.clone(), child_changes.clone()).is_err()
				} else {
					sink.is_closed()
				}
			};
		});
	}
}

impl<Hash> StorageNotificationsImpl<Hash> {
	fn remove_subscriber_from(
		subscriber: &SubscriberId,
		filters: &Keys,
		listeners: &mut HashMap<StorageKey, FnvHashSet<SubscriberId>>,
		wildcards: &mut FnvHashSet<SubscriberId>,
	) {
		match filters {
			None => {
				wildcards.remove(subscriber);
			},
			Some(filters) =>
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
				},
		}
	}

	fn remove_subscriber(&mut self, subscriber: SubscriberId) -> Option<(Keys, ChildKeys)> {
		let sink = self.sinks.remove(&subscriber)?;

		Self::remove_subscriber_from(
			&subscriber,
			&sink.keys,
			&mut self.listeners,
			&mut self.wildcard_listeners,
		);
		if let Some(child_filters) = &sink.child_keys {
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
		if let Some(m) = self.metrics.as_ref() {
			m.with_label_values(&[&"removed"]).inc();
		}

		Some((sink.keys.clone(), sink.child_keys.clone()))
	}
}
