// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Extrinsics status updates.

use futures::{
	Stream,
	sync::mpsc,
};
use serde::{Serialize, Deserialize};

/// Possible extrinsic status events
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Status<H, H2> {
	/// Extrinsic is part of the future queue.
	Future,
	/// Extrinsic is part of the ready queue.
	Ready,
	/// Extrinsic has been finalized in block with given hash.
	Finalized(H2),
	/// Some state change (perhaps another extrinsic was included) rendered this extrinsic invalid.
	Usurped(H),
	/// The extrinsic has been broadcast to the given peers.
	Broadcast(Vec<String>),
	/// Extrinsic has been dropped from the pool because of the limit.
	Dropped,
	/// Extrinsic was detected as invalid.
	Invalid,
}

/// Extrinsic watcher.
///
/// Represents a stream of status updates for particular extrinsic.
#[derive(Debug)]
pub struct Watcher<H, H2> {
	receiver: mpsc::UnboundedReceiver<Status<H, H2>>,
	hash: H,
}

impl<H, H2> Watcher<H, H2> {
	/// Returns the transaction hash.
	pub fn hash(&self) -> &H {
		&self.hash
	}

	/// Pipe the notifications to given sink.
	///
	/// Make sure to drive the future to completion.
	pub fn into_stream(self) -> impl Stream<Item=Status<H, H2>, Error=()> {
		// we can safely ignore the error here, `UnboundedReceiver` never fails.
		self.receiver.map_err(|_| ())
	}
}

/// Sender part of the watcher. Exposed only for testing purposes.
#[derive(Debug)]
pub struct Sender<H, H2> {
	receivers: Vec<mpsc::UnboundedSender<Status<H, H2>>>,
	finalized: bool,
}

impl<H, H2> Default for Sender<H, H2> {
	fn default() -> Self {
		Sender {
			receivers: Default::default(),
			finalized: false,
		}
	}
}

impl<H: Clone, H2: Clone> Sender<H, H2> {
	/// Add a new watcher to this sender object.
	pub fn new_watcher(&mut self, hash: H) -> Watcher<H, H2> {
		let (tx, receiver) = mpsc::unbounded();
		self.receivers.push(tx);
		Watcher {
			receiver,
			hash,
		}
	}

	/// Transaction became ready.
	pub fn ready(&mut self) {
		self.send(Status::Ready)
	}

	/// Transaction was moved to future.
	pub fn future(&mut self) {
		self.send(Status::Future)
	}

	/// Some state change (perhaps another extrinsic was included) rendered this extrinsic invalid.
	pub fn usurped(&mut self, hash: H) {
		self.send(Status::Usurped(hash))
	}

	/// Extrinsic has been finalized in block with given hash.
	pub fn finalized(&mut self, hash: H2) {
		self.send(Status::Finalized(hash));
		self.finalized = true;
	}

	/// Extrinsic has been marked as invalid by the block builder.
	pub fn invalid(&mut self) {
		self.send(Status::Invalid);
		// we mark as finalized as there are no more notifications
		self.finalized = true;
	}

	/// Transaction has been dropped from the pool because of the limit.
	pub fn dropped(&mut self) {
		self.send(Status::Dropped);
	}

	/// The extrinsic has been broadcast to the given peers.
	pub fn broadcast(&mut self, peers: Vec<String>) {
		self.send(Status::Broadcast(peers))
	}


	/// Returns true if the are no more listeners for this extrinsic or it was finalized.
	pub fn is_done(&self) -> bool {
		self.finalized || self.receivers.is_empty()
	}

	fn send(&mut self, status: Status<H, H2>) {
		self.receivers.retain(|sender| sender.unbounded_send(status.clone()).is_ok())
	}
}
