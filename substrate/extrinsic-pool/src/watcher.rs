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

//! Extrinsics status updates.

use futures::{
	Stream,
	sync::mpsc,
};

/// Possible extrinsic status events
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub enum Status<H> {
	/// Extrinsic has been finalised in block with given hash.
	Finalised(H),
	/// Some state change (perhaps another extrinsic was included) rendered this extrinsic invalid.
	Usurped(H),
	/// The extrinsic has been broadcast to the given peers.
	Broadcast(Vec<String>),
	/// Extrinsic has been dropped from the pool because of the limit.
	Dropped,
}

/// Extrinsic watcher.
///
/// Represents a stream of status updates for particular extrinsic.
#[derive(Debug)]
pub struct Watcher<H> {
	receiver: mpsc::UnboundedReceiver<Status<H>>,
}

impl<H> Watcher<H> {
	/// Pipe the notifications to given sink.
	///
	/// Make sure to drive the future to completion.
	pub fn into_stream(self) -> impl Stream<Item=Status<H>, Error=()> {
		// we can safely ignore the error here, `UnboundedReceiver` never fails.
		self.receiver.map_err(|_| ())
	}
}

/// Sender part of the watcher. Exposed only for testing purposes.
#[derive(Debug, Default)]
pub struct Sender<H> {
	receivers: Vec<mpsc::UnboundedSender<Status<H>>>,
	finalised: bool,
}

impl<H: Clone> Sender<H> {
	/// Add a new watcher to this sender object.
	pub fn new_watcher(&mut self) -> Watcher<H> {
		let (tx, receiver) = mpsc::unbounded();
		self.receivers.push(tx);
		Watcher {
			receiver,
		}
	}

	/// Some state change (perhaps another extrinsic was included) rendered this extrinsic invalid.
	pub fn usurped(&mut self, hash: H) {
		self.send(Status::Usurped(hash))
	}

	/// Extrinsic has been finalised in block with given hash.
	pub fn finalised(&mut self, hash: H) {
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

	fn send(&mut self, status: Status<H>) {
		self.receivers.retain(|sender| sender.unbounded_send(status.clone()).is_ok())
	}
}
