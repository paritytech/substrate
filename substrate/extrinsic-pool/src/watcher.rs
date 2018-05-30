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

use futures::sync::mpsc;
use primitives::{
	block::{HeaderHash, ExtrinsicHash}
};

/// Possible extrinsic status events
#[derive(Debug, Clone)]
pub enum Status {
	/// Extrinsic has been finalised in block with given hash.
	Finalised(HeaderHash),
	/// Some state change (perhaps another extrinsic was included) rendered this extrinsic invalid.
	Usurped(ExtrinsicHash),
	/// The extrinsic has been broadcast to the given peers.
	Broadcast(Vec<String>),
	/// Extrinsic has been dropped from the pool because of the limit.
	Dropped,
}

/// Extrinsic watcher.
///
/// Represents a stream of status updates for particular extrinsic.
#[derive(Debug)]
pub struct Watcher {
	receiver: mpsc::UnboundedReceiver<Status>,
}

#[derive(Debug, Default)]
pub(crate) struct Sender {
	receivers: Vec<mpsc::UnboundedSender<Status>>,
	finalised: bool,
}

impl Sender {
	/// Add a new watcher to this sender object.
	pub fn new_watcher(&mut self) -> Watcher {
		let (tx, receiver) = mpsc::unbounded();
		self.receivers.push(tx);
		Watcher {
			receiver,
		}
	}

	/// Some state change (perhaps another extrinsic was included) rendered this extrinsic invalid.
	pub fn usurped(&mut self, hash: ExtrinsicHash) {
		self.send(Status::Usurped(hash))
	}

	/// Extrinsic has been finalised in block with given hash.
	pub fn finalised(&mut self, hash: HeaderHash) {
		self.send(Status::Finalised(hash));
		self.finalised = true;
	}

	/// Transaction has been dropped from the pool because of the limit.
	pub fn dropped(&mut self) {
		self.send(Status::Dropped);
	}

	/// The extrinsic has been broadcast to the given peers.
	pub fn broadcast(&mut self, peers: Vec<String>) {
		self.send(Status::Broadcast(peers))
	}

	/// Returns true if the are no more listeners for this extrinsic or it was finalised.
	pub fn is_done(&self) -> bool {
		self.finalised || self.receivers.is_empty()
	}

	fn send(&mut self, status: Status) {
		self.receivers.retain(|sender| sender.unbounded_send(status.clone()).is_ok())
	}
}
