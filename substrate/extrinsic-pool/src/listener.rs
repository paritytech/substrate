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
	collections::HashMap,
};
use primitives::Hash;
use txpool;

use watcher;

#[derive(Default)]
pub struct Listener {
	watchers: HashMap<Hash, watcher::Sender>
}

impl Listener {
	pub fn create_watcher<T: txpool::VerifiedTransaction<Hash=Hash>>(&mut self, xt: Arc<T>) -> watcher::Watcher {
		let sender = self.watchers.entry(*xt.hash()).or_insert_with(watcher::Sender::default);
		sender.new_watcher()
	}

	pub fn broadcasted(&mut self, hash: &Hash, peers: Vec<String>) {
		self.fire(hash, |watcher| watcher.broadcast(peers));
	}

	fn fire<F: FnOnce(&mut watcher::Sender)>(&mut self, hash: &Hash, fun: F) {
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

impl<T: txpool::VerifiedTransaction<Hash=Hash>> txpool::Listener<T> for Listener {
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
		let header_hash = 1.into();
		self.fire(tx.hash(), |watcher| watcher.finalised(header_hash))
	}
}


