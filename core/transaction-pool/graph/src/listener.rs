
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
	hash,
};
use watcher;
use sr_primitives::traits;

/// Extrinsic pool default listener.
pub struct Listener<H: hash::Hash + Eq, H2> {
	watchers: HashMap<H, watcher::Sender<H, H2>>
}

impl<H: hash::Hash + Eq, H2> Default for Listener<H, H2> {
	fn default() -> Self {
		Listener {
			watchers: Default::default(),
		}
	}
}

impl<H: hash::Hash + traits::Member, H2: Clone> Listener<H, H2> {
	fn fire<F>(&mut self, hash: &H, fun: F) where F: FnOnce(&mut watcher::Sender<H, H2>) {
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
	pub fn create_watcher(&mut self, hash: H) -> watcher::Watcher<H, H2> {
		let sender = self.watchers.entry(hash).or_insert_with(watcher::Sender::default);
		sender.new_watcher()
	}

	/// Notify the listeners about extrinsic broadcast.
	pub fn broadcasted(&mut self, hash: &H, peers: Vec<String>) {
		self.fire(hash, |watcher| watcher.broadcast(peers));
	}

	/// New transaction was added to the ready pool or promoted from the future pool.
	pub fn ready(&mut self, tx: &H, old: Option<&H>) {
		if let Some(old) = old {
			self.fire(old, |watcher| watcher.usurped(tx.clone()));
		}
	}

	/// New transaction was added to the future pool.
	pub fn future(&mut self, _tx: &H) {
	}

	/// Transaction was dropped from the pool because of the limit.
	pub fn dropped(&mut self, tx: &H, by: Option<&H>) {
		self.fire(tx, |watcher| match by {
			Some(t) => watcher.usurped(t.clone()),
			None => watcher.dropped(),
		})
	}

	/// Transaction was rejected from the pool.
	pub fn rejected(&mut self, tx: &H, is_invalid: bool) {
		warn!(target: "transaction-pool", "Extrinsic rejected ({}): {:?}", is_invalid, tx);
	}

	/// Transaction was removed as invalid.
	pub fn invalid(&mut self, tx: &H) {
		warn!(target: "transaction-pool", "Extrinsic invalid: {:?}", tx);
	}

	/// Transaction was pruned from the pool.
	pub fn pruned(&mut self, header_hash: H2, tx: &H) {
		self.fire(tx, |watcher| watcher.finalised(header_hash))
	}
}
