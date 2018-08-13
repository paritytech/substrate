// Copyright 2018 Parity Technologies (UK) Ltd.
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

use std::{
	sync::Arc,
	fmt,
	collections::HashMap,
};
use txpool;

use watcher;

/// Extrinsic pool default listener.
#[derive(Default)]
pub struct Listener<H: ::std::hash::Hash + Eq> {
	watchers: HashMap<H, watcher::Sender<H>>
}

impl<H: ::std::hash::Hash + Eq + Copy + fmt::Debug + fmt::LowerHex + Default> Listener<H> {
	/// Creates a new watcher for given verified extrinsic.
	///
	/// The watcher can be used to subscribe to lifecycle events of that extrinsic.
	pub fn create_watcher<T: txpool::VerifiedTransaction<Hash=H>>(&mut self, xt: Arc<T>) -> watcher::Watcher<H> {
		let sender = self.watchers.entry(*xt.hash()).or_insert_with(watcher::Sender::default);
		sender.new_watcher()
	}

	/// Notify the listeners about extrinsic broadcast.
	pub fn broadcasted(&mut self, hash: &H, peers: Vec<String>) {
		self.fire(hash, |watcher| watcher.broadcast(peers));
	}

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
}

impl<H, T> txpool::Listener<T> for Listener<H> where
	H: ::std::hash::Hash + Eq + Copy + fmt::Debug + fmt::LowerHex + Default,
	T: txpool::VerifiedTransaction<Hash=H>,
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
		warn!("Extrinsic rejected ({}): {:?}", reason, tx);
	}

	fn invalid(&mut self, tx: &Arc<T>) {
		warn!("Extrinsic invalid: {:?}", tx);
	}

	fn canceled(&mut self, tx: &Arc<T>) {
		warn!("Extrinsic canceled: {:?}", tx);
	}

	fn mined(&mut self, tx: &Arc<T>) {
		// TODO [ToDr] latest block number?
		let header_hash = Default::default();
		self.fire(tx.hash(), |watcher| watcher.finalised(header_hash))
	}
}
