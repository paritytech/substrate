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

//! Storage notifications

use std::{
	collections::{HashMap, HashSet},
	pin::Pin,
	sync::Arc,
	task::Poll,
};

use futures::Stream;

use prometheus_endpoint::Registry as PrometheusRegistry;

use sc_utils::pubsub::{Hub, Receiver};
use sp_core::storage::{StorageData, StorageKey};
use sp_runtime::traits::Block as BlockT;

mod registry;

use registry::Registry;

#[cfg(test)]
mod tests;

/// A type of a message delivered to the subscribers
#[derive(Debug)]
pub struct StorageNotification<Hash> {
	/// The hash of the block
	pub block: Hash,

	/// The set of changes
	pub changes: StorageChangeSet,
}

/// Storage change set
#[derive(Debug)]
pub struct StorageChangeSet {
	changes: Arc<[(StorageKey, Option<StorageData>)]>,
	child_changes: Arc<[(StorageKey, Vec<(StorageKey, Option<StorageData>)>)]>,
	filter: Keys,
	child_filters: ChildKeys,
}

/// Manages storage listeners.
#[derive(Debug)]
pub struct StorageNotifications<Block: BlockT>(Hub<StorageNotification<Block::Hash>, Registry>);

/// Type that implements `futures::Stream` of storage change events.
pub struct StorageEventStream<H>(Receiver<StorageNotification<H>, Registry>);

type Keys = Option<HashSet<StorageKey>>;
type ChildKeys = Option<HashMap<StorageKey, Option<HashSet<StorageKey>>>>;

impl StorageChangeSet {
	/// Convert the change set into iterator over storage items.
	pub fn iter(
		&self,
	) -> impl Iterator<Item = (Option<&StorageKey>, &StorageKey, Option<&StorageData>)> + '_ {
		let top = self
			.changes
			.iter()
			.filter(move |&(key, _)| match self.filter {
				Some(ref filter) => filter.contains(key),
				None => true,
			})
			.map(move |(k, v)| (None, k, v.as_ref()));
		let children = self
			.child_changes
			.iter()
			.filter_map(move |(sk, changes)| {
				self.child_filters.as_ref().and_then(|cf| {
					cf.get(sk).map(|filter| {
						changes
							.iter()
							.filter(move |&(key, _)| match filter {
								Some(ref filter) => filter.contains(key),
								None => true,
							})
							.map(move |(k, v)| (Some(sk), k, v.as_ref()))
					})
				})
			})
			.flatten();
		top.chain(children)
	}
}

impl<H> Stream for StorageEventStream<H> {
	type Item = StorageNotification<H>;
	fn poll_next(
		self: Pin<&mut Self>,
		cx: &mut std::task::Context<'_>,
	) -> Poll<Option<Self::Item>> {
		Stream::poll_next(Pin::new(&mut self.get_mut().0), cx)
	}
}

impl<Block: BlockT> StorageNotifications<Block> {
	/// Initialize a new StorageNotifications
	/// optionally pass a prometheus registry to send subscriber metrics to
	pub fn new(prometheus_registry: Option<PrometheusRegistry>) -> Self {
		let registry = Registry::new(prometheus_registry);
		let hub = Hub::new_with_registry("mpsc_storage_notification_items", registry);

		StorageNotifications(hub)
	}

	/// Trigger notification to all listeners.
	///
	/// Note the changes are going to be filtered by listener's filter key.
	/// In fact no event might be sent if clients are not interested in the changes.
	pub fn trigger(
		&self,
		hash: &Block::Hash,
		changeset: impl Iterator<Item = (Vec<u8>, Option<Vec<u8>>)>,
		child_changeset: impl Iterator<
			Item = (Vec<u8>, impl Iterator<Item = (Vec<u8>, Option<Vec<u8>>)>),
		>,
	) {
		self.0.send((hash, changeset, child_changeset))
	}

	/// Start listening for particular storage keys.
	pub fn listen(
		&self,
		filter_keys: Option<&[StorageKey]>,
		filter_child_keys: Option<&[(StorageKey, Option<Vec<StorageKey>>)]>,
	) -> StorageEventStream<Block::Hash> {
		let receiver = self
			.0
			.subscribe(registry::SubscribeOp { filter_keys, filter_child_keys }, 100_000);

		StorageEventStream(receiver)
	}
}
