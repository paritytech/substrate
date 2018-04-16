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

//! Implements a future which resolves when all of the candidates referenced are includable.

use std::collections::HashMap;

use futures::prelude::*;
use futures::sync::oneshot;

use polkadot_primitives::Hash;

/// Track includability of a set of candidates,
pub(super) fn track<I: IntoIterator<Item=(Hash, bool)>>(candidates: I) -> (IncludabilitySender, Includable) {
	let (tx, rx) = oneshot::channel();
	let tracking: HashMap<_, _> = candidates.into_iter().collect();
	let includable_count = tracking.values().filter(|x| **x).count();

	let mut sender = IncludabilitySender {
		tracking,
		includable_count,
		sender: Some(tx),
	};

	sender.try_complete();

	(
		sender,
		Includable(rx),
	)
}

/// The sending end of the includability sender.
pub(super) struct IncludabilitySender {
	tracking: HashMap<Hash, bool>,
	includable_count: usize,
	sender: Option<oneshot::Sender<()>>,
}

impl IncludabilitySender {
	/// update the inner candidate. wakes up the task as necessary.
	/// returns `Err(Canceled)` if the other end has hung up.
	///
	/// returns `true` when this is completed and should be destroyed.
	pub fn update_candidate(&mut self, candidate: Hash, includable: bool) -> bool {
		use std::collections::hash_map::Entry;

		match self.tracking.entry(candidate) {
			Entry::Vacant(_) => {}
			Entry::Occupied(mut entry) => {
				let old = entry.insert(includable);
				if !old && includable {
					self.includable_count += 1;
				} else if old && !includable {
					self.includable_count -= 1;
				}
			}
		}

		self.try_complete()
	}

	/// whether the sender is completed.
	pub fn is_complete(&self) -> bool {
		self.sender.is_none()
	}

	fn try_complete(&mut self) -> bool {
		if self.includable_count == self.tracking.len() {
			if let Some(sender) = self.sender.take() {
				let _ = sender.send(());
			}

			true
		} else {
			false
		}
	}
}

/// Future that resolves when all the candidates within are includable.
pub struct Includable(oneshot::Receiver<()>);

impl Future for Includable {
	type Item = ();
	type Error = oneshot::Canceled;

	fn poll(&mut self) -> Poll<(), oneshot::Canceled> {
		self.0.poll()
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn it_works() {
		let hash1 = [1; 32].into();
		let hash2 = [2; 32].into();
		let hash3 = [3; 32].into();

		let (mut sender, recv) = track([
			(hash1, true),
			(hash2, true),
			(hash2, false), // overwrite should favor latter.
			(hash3, true),
		].iter().cloned());

		assert!(!sender.is_complete());

		// true -> false transition is possible and should be handled.
		sender.update_candidate(hash1, false);
		assert!(!sender.is_complete());

		sender.update_candidate(hash2, true);
		assert!(!sender.is_complete());

		sender.update_candidate(hash1, true);
		assert!(sender.is_complete());

		recv.wait().unwrap();
	}
}
