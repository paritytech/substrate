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

use sc_utils::{mpsc, pubsub::SharedRegistry};

use sp_runtime::traits::Block as BlockT;

/// Manages storage listeners.
#[derive(Debug)]
pub struct StorageNotifications<Block: BlockT>(
	pub(super) SharedRegistry<StorageNotificationsImpl<Block::Hash>>,
);

impl<Block: BlockT> Default for StorageNotifications<Block> {
	fn default() -> Self {
		Self(Default::default())
	}
}

impl<Block: BlockT> StorageNotifications<Block> {
	/// Initialize a new StorageNotifications
	/// optionally pass a prometheus registry to send subscriber metrics to
	pub fn new(prometheus_registry: Option<PrometheusRegistry>) -> Self {
		StorageNotifications(SharedRegistry::new(StorageNotificationsImpl::new(
			prometheus_registry,
		)))
	}

	/// Trigger notification to all listeners.
	///
	/// Note the changes are going to be filtered by listener's filter key.
	/// In fact no event might be sent if clients are not interested in the changes.
	pub fn trigger(
		&mut self,
		hash: &Block::Hash,
		changeset: impl Iterator<Item = (Vec<u8>, Option<Vec<u8>>)>,
		child_changeset: impl Iterator<
			Item = (Vec<u8>, impl Iterator<Item = (Vec<u8>, Option<Vec<u8>>)>),
		>,
	) {
		self.0.lock().trigger(hash, changeset, child_changeset);
	}

	/// Start listening for particular storage keys.
	pub fn listen(
		&mut self,
		filter_keys: Option<&[StorageKey]>,
		filter_child_keys: Option<&[(StorageKey, Option<Vec<StorageKey>>)]>,
	) -> StorageEventStream<Block::Hash> {
		use registry::SubscribeOp;

		let (tx, rx) = mpsc::tracing_unbounded("mpsc_storage_notification_items");

		let subs_guard = self.0.subscribe(SubscribeOp { filter_keys, filter_child_keys, tx });

		StorageEventStream { rx, _subs_guard: subs_guard, was_triggered: false }
	}
}
