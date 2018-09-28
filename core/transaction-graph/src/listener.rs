
// Copyright 2018 Parity Technologies (UK) Ltd.
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
	collections::HashMap,
	fmt,
	hash,
	sync::Arc,
};

use watcher;
use sr_primitives::traits;

/// Extrinsic pool default listener.
pub struct Listener<H: hash::Hash + Eq> {
	watchers: HashMap<H, watcher::Sender<H>>
}

impl<H: hash::Hash + Eq> Default for Listener<H> {
	fn default() -> Self {
		Listener {
			watchers: Default::default(),
		}
	}
}

impl<H: hash::Hash + traits::Member> Listener<H> {
	fn fire<F>(&mut self, hash: &H, fun: F) where F: FnOnce(&mut watcher::Sender<H>) {
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
	/// The watcher can be used to subscribe to lifecycle events of that extrinsic.
	pub fn create_watcher(&mut self, hash: H) -> watcher::Watcher<H> {
		let sender = self.watchers.entry(hash).or_insert_with(watcher::Sender::default);
		sender.new_watcher()
	}

	/// Notify the listeners about extrinsic broadcast.
	pub fn broadcasted(&mut self, hash: &H, peers: Vec<String>) {
		self.fire(hash, |watcher| watcher.broadcast(peers));
	}

	/// New transaction was added to the pool.
	pub fn added(&mut self, tx: &Arc<H>, old: Option<&Arc<H>>) {
		if let Some(old) = old {
			self.fire(old, |watcher| watcher.usurped((**tx).clone()));
		}
	}

	/// Transaction was dropped from the pool because of the limit.
	pub fn dropped(&mut self, tx: &Arc<H>, by: Option<&H>) {
		self.fire(tx, |watcher| match by {
			Some(t) => watcher.usurped(t.clone()),
			None => watcher.dropped(),
		})
	}

	/// Transaction was rejected from the pool.
	pub fn rejected(&mut self, tx: &Arc<H>, is_invalid: bool) {
		warn!(target: "transaction-pool", "Extrinsic rejected ({}): {:?}", is_invalid, tx);
	}

	/// Transaction was removed as invalid.
	pub fn invalid(&mut self, tx: &Arc<H>) {
		warn!(target: "transaction-pool", "Extrinsic invalid: {:?}", tx);
	}

	/// Transaction was pruned from the pool.
	pub fn pruned(&mut self, header_hash: H, tx: &Arc<H>) {
		self.fire(&**tx, |watcher| watcher.finalised(header_hash))
	}
}
