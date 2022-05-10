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

//! Wildcard storage notifications

use fnv::FnvHashSet;
use futures::Stream;
use prometheus_endpoint::{register, CounterVec, Opts, Registry as PrometheusRegistry, U64};
use sc_utils::{
	id_sequence::SeqID as SubscriberId,
	pubsub::{Dispatch, Hub, Receiver, Subscribe, Unsubscribe},
};
use sp_core::storage::{StorageData, StorageKey};
use sp_storage::StorageChangeSet;
use std::{pin::Pin, task::Poll};

#[derive(Debug)]
struct Registry {
	metrics: Option<CounterVec<U64>>,
	wildcard_listeners: FnvHashSet<SubscriberId>,
}

impl Registry {
	fn new(prometheus_registry: Option<PrometheusRegistry>) -> Self {
		let metrics = prometheus_registry.and_then(|r| {
			CounterVec::new(
				Opts::new(
					"substrate_storage_wildcard_notification_subscribers",
					"Number of subscribers for storage changes (all keys)",
				),
				&["action"], // added | removed
			)
			.and_then(|g| register(g, &r))
			.ok()
		});

		Registry { metrics, wildcard_listeners: Default::default() }
	}
}

impl Unsubscribe for Registry {
	fn unsubscribe(&mut self, subscriber: SubscriberId) {
		self.wildcard_listeners.remove(&subscriber);

		if let Some(m) = self.metrics.as_ref() {
			m.with_label_values(&["removed"]).inc();
		}
	}
}

impl Subscribe<()> for Registry {
	fn subscribe(&mut self, _: (), subs_id: SubscriberId) {
		self.wildcard_listeners.insert(subs_id);

		if let Some(m) = self.metrics.as_ref() {
			m.with_label_values(&["added"]).inc();
		}
	}
}

type Message<'a, Hash> = (&'a Hash, sp_state_machine::StorageCollection);

impl<'a, Hash> Dispatch<Message<'a, Hash>> for Registry
where
	Hash: Clone + PartialEq,
{
	type Item = StorageChangeSet<Hash>;
	type Ret = ();

	fn dispatch<F>(&mut self, (hash, all_changes): Message<'a, Hash>, mut dispatch: F) -> Self::Ret
	where
		F: FnMut(&SubscriberId, Self::Item),
	{
		let changes: Vec<_> = all_changes
			.into_iter()
			.map(|(key, value)| (StorageKey(key), value.map(StorageData)))
			.collect();
		for sid in &self.wildcard_listeners {
			dispatch(sid, StorageChangeSet { block: hash.clone(), changes: changes.clone() });
		}
	}
}

/// Manages wildcard storage subscriptions.
#[derive(Debug)]
pub struct AllStorageChangesHub<Hash>(Hub<StorageChangeSet<Hash>, Registry>);

/// A stream of all storage changes.
pub struct AllStorageChangesStream<H>(Receiver<StorageChangeSet<H>, Registry>);

impl<H> Stream for AllStorageChangesStream<H> {
	type Item = StorageChangeSet<H>;
	fn poll_next(
		self: Pin<&mut Self>,
		cx: &mut std::task::Context<'_>,
	) -> Poll<Option<Self::Item>> {
		Stream::poll_next(Pin::new(&mut self.get_mut().0), cx)
	}
}

impl<Hash> AllStorageChangesHub<Hash>
where
	Hash: Clone + PartialEq,
{
	/// Creates a new notification hub for all storage changes.
	pub fn new(prometheus_registry: Option<PrometheusRegistry>) -> Self {
		let registry = Registry::new(prometheus_registry);
		let hub = Hub::new_with_registry("mpsc_storage_wildcard_notification_items", registry);

		AllStorageChangesHub(hub)
	}

	/// Trigger notification to all listeners.
	pub fn trigger(&self, block_hash: &Hash, changes: sp_state_machine::StorageCollection) {
		self.0.send((block_hash, changes))
	}

	/// Create a new subscription to all storage changes.
	pub fn subscribe(&self) -> AllStorageChangesStream<Hash> {
		AllStorageChangesStream(self.0.subscribe(()))
	}
}
