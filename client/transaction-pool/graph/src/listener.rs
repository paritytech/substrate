
// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

use std::{
	collections::HashMap, hash,
};
use linked_hash_map::LinkedHashMap;
use serde::Serialize;
use crate::{watcher, ChainApi, BlockHash};
use log::{debug, trace, warn};
use sp_runtime::traits;

/// Extrinsic pool default listener.
pub struct Listener<H: hash::Hash + Eq, C: ChainApi> {
	watchers: HashMap<H, watcher::Sender<H, BlockHash<C>>>,
	finality_watchers: LinkedHashMap<BlockHash<C>, Vec<H>>,
}

/// Maximum number of blocks awaiting finality at any time.
const MAX_FINALITY_WATCHERS: usize = 512;

impl<H: hash::Hash + Eq, C: ChainApi> Default for Listener<H, C> {
	fn default() -> Self {
		Listener {
			watchers: Default::default(),
			finality_watchers: Default::default(),
		}
	}
}

impl<H: hash::Hash + traits::Member + Serialize, C: ChainApi> Listener<H, C> {
	fn fire<F>(&mut self, hash: &H, fun: F) where F: FnOnce(&mut watcher::Sender<H, BlockHash<C>>) {
		let clean = if let Some(h) = self.watchers.get_mut(hash) {
			fun(h);
			h.is_done()
		} else {
			false
		};

		if clean {
			self.watchers.remove(hash);
		}
	}

	/// Creates a new watcher for given verified extrinsic.
	///
	/// The watcher can be used to subscribe to life-cycle events of that extrinsic.
	pub fn create_watcher(&mut self, hash: H) -> watcher::Watcher<H, BlockHash<C>> {
		let sender = self.watchers.entry(hash.clone()).or_insert_with(watcher::Sender::default);
		sender.new_watcher(hash)
	}

	/// Notify the listeners about extrinsic broadcast.
	pub fn broadcasted(&mut self, hash: &H, peers: Vec<String>) {
		trace!(target: "txpool", "[{:?}] Broadcasted", hash);
		self.fire(hash, |watcher| watcher.broadcast(peers));
	}

	/// New transaction was added to the ready pool or promoted from the future pool.
	pub fn ready(&mut self, tx: &H, old: Option<&H>) {
		trace!(target: "txpool", "[{:?}] Ready (replaced: {:?})", tx, old);
		self.fire(tx, |watcher| watcher.ready());
		if let Some(old) = old {
			self.fire(old, |watcher| watcher.usurped(tx.clone()));
		}
	}

	/// New transaction was added to the future pool.
	pub fn future(&mut self, tx: &H) {
		trace!(target: "txpool", "[{:?}] Future", tx);
		self.fire(tx, |watcher| watcher.future());
	}

	/// Transaction was dropped from the pool because of the limit.
	pub fn dropped(&mut self, tx: &H, by: Option<&H>) {
		trace!(target: "txpool", "[{:?}] Dropped (replaced by {:?})", tx, by);
		self.fire(tx, |watcher| match by {
			Some(t) => watcher.usurped(t.clone()),
			None => watcher.dropped(),
		})
	}

	/// Transaction was removed as invalid.
	pub fn invalid(&mut self, tx: &H, warn: bool) {
		if warn {
			warn!(target: "txpool", "Extrinsic invalid: {:?}", tx);
		} else {
			debug!(target: "txpool", "Extrinsic invalid: {:?}", tx);
		}
		self.fire(tx, |watcher| watcher.invalid());
	}

	/// Transaction was pruned from the pool.
	pub fn pruned(&mut self, block_hash: BlockHash<C>, tx: &H) {
		debug!(target: "txpool", "[{:?}] Pruned at {:?}", tx, block_hash);
		self.fire(tx, |s| s.in_block(block_hash));
		self.finality_watchers.entry(block_hash).or_insert(vec![]).push(tx.clone());

		while self.finality_watchers.len() > MAX_FINALITY_WATCHERS {
			if let Some((hash, txs)) = self.finality_watchers.pop_front() {
				for tx in txs {
					self.fire(&tx, |s| s.finality_timeout(hash.clone()));
				}
			}
		}
	}

	/// The block this transaction was included in has been retracted.
	pub fn retracted(&mut self, block_hash: BlockHash<C>) {
		if let Some(hashes) = self.finality_watchers.remove(&block_hash) {
			for hash in hashes {
				self.fire(&hash, |s| s.retracted(block_hash))
			}
		}
	}

	/// Notify all watchers that transactions have been finalized
	pub fn finalized(&mut self, block_hash: BlockHash<C>) {
		if let Some(hashes) = self.finality_watchers.remove(&block_hash) {
			for hash in hashes {
				self.fire(&hash, |s| s.finalized(block_hash))
			}
		}
	}
}
