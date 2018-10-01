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
	sync::Arc,
	fmt,
	collections::HashMap,
};
use txpool;
use watcher;

/// Returns the hash of the latest block.
pub trait LatestHash {
	type Hash: Clone;

	/// Hash of the latest block.
	fn latest_hash(&self) -> Self::Hash;
}

/// Extrinsic pool default listener.
pub struct Listener<H: ::std::hash::Hash + Eq, C: LatestHash> {
	watchers: HashMap<H, watcher::Sender<H, C::Hash>>,
	chain: C,
}

impl<H, C> Listener<H, C> where
	H: ::std::hash::Hash + Eq + Copy + fmt::Debug + fmt::LowerHex + Default,
	C: LatestHash,
{
	/// Creates a new listener with given latest hash provider.
	pub fn new(chain: C) -> Self {
		Listener {
			watchers: Default::default(),
			chain,
		}
	}

	/// Creates a new watcher for given verified extrinsic.
	///
	/// The watcher can be used to subscribe to lifecycle events of that extrinsic.
	pub fn create_watcher<T: txpool::VerifiedTransaction<Hash=H>>(&mut self, xt: Arc<T>) -> watcher::Watcher<H, C::Hash> {
		let sender = self.watchers.entry(*xt.hash()).or_insert_with(watcher::Sender::default);
		sender.new_watcher()
	}

	/// Notify the listeners about extrinsic broadcast.
	pub fn broadcasted(&mut self, hash: &H, peers: Vec<String>) {
		self.fire(hash, |watcher| watcher.broadcast(peers));
	}

	fn fire<F>(&mut self, hash: &H, fun: F) where F: FnOnce(&mut watcher::Sender<H, C::Hash>) {
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
}

impl<H, T, C> txpool::Listener<T> for Listener<H, C> where
	H: ::std::hash::Hash + Eq + Copy + fmt::Debug + fmt::LowerHex + Default,
	T: txpool::VerifiedTransaction<Hash=H>,
	C: LatestHash,
{
	fn added(&mut self, tx: &Arc<T>, old: Option<&Arc<T>>) {
		if let Some(old) = old {
			let hash = tx.hash();
			self.fire(old.hash(), |watcher| watcher.usurped(*hash));
		}
	}

	fn dropped(&mut self, tx: &Arc<T>, by: Option<&T>) {
		self.fire(tx.hash(), |watcher| match by {
			Some(t) => watcher.usurped(*t.hash()),
			None => watcher.dropped(),
		})
	}

	fn rejected(&mut self, tx: &Arc<T>, reason: &txpool::ErrorKind) {
		warn!(target: "transaction-pool", "Extrinsic rejected ({}): {:?}", reason, tx);
	}

	fn invalid(&mut self, tx: &Arc<T>) {
		warn!(target: "transaction-pool", "Extrinsic invalid: {:?}", tx);
	}

	fn canceled(&mut self, tx: &Arc<T>) {
		debug!(target: "transaction-pool", "Extrinsic canceled: {:?}", tx);
	}

	fn culled(&mut self, tx: &Arc<T>) {
		let header_hash = self.chain.latest_hash();
		self.fire(tx.hash(), |watcher| watcher.finalised(header_hash))
	}
}
