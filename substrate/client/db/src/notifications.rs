// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Storage notifications

use std::collections::HashMap;

use futures::sync::mpsc;
use primitives::{
	H256,
	storage::{StorageKey, StorageData},
};
use runtime_primitives::traits::Block as BlockT;

type SubscriberId = u64;

/// Manages storage listeners.
#[derive(Debug)]
pub struct StorageNotifications<Block: BlockT> {
	next_id: SubscriberId,
	filters: HashMap<
		Option<StorageKey>,
		Vec<SubscriberId>,
	>,
	sinks: HashMap<
		SubscriberId,
		mpsc::UnboundedSender<(
			Block::Hash,
			Vec<(StorageKey, Option<StorageData>)>,
		)>,
	>,
}

impl<Block: BlockT> Default for StorageNotifications<Block> {
	fn default() -> Self {
		StorageNotifications {
			next_id: Default::default(),
			filters: Default::default(),
			sinks: Default::default(),
		}
	}
}

impl<Block: BlockT> StorageNotifications<Block> {
	/// Trigger notification to all listeners.
	///
	/// Note the changes are going to be filtered by listener's filter key.
	/// In fact no event might be sent if clients are not interested in the changes.
	pub fn trigger(&mut self, hash: &Block::Hash, changeset: &::state_db::ChangeSet<H256>) {

	}

	/// Start listening for particular storage keys.
	pub fn listen(&mut self, filter_keys: Option<&[StorageKey]>) -> ::client::StorageEventStream<Block::Hash> {
		self.next_id += 1;

		// add subscriber for every key
		{
			let mut add = |key| {
				self.filters
					.entry(key)
					.or_insert_with(Default::default)
					.push(self.next_id);
			};

			match filter_keys {
				None => add(None),
				Some(keys) => keys.iter().for_each(|key| add(Some(StorageKey(key.0.clone())))),
			}
		}

		// insert sink
		let (tx, rx) = mpsc::unbounded();
		self.sinks.insert(self.next_id, tx);
		rx
	}
}

#[cfg(test)]
mod tests {

}
