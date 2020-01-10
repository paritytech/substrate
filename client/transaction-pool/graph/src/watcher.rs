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

//! Extrinsics status updates.

use futures::{
	Stream,
	channel::mpsc,
};
use sp_transaction_pool::TransactionStatus;

/// Extrinsic watcher.
///
/// Represents a stream of status updates for particular extrinsic.
#[derive(Debug)]
pub struct Watcher<H, H2> {
	receiver: mpsc::UnboundedReceiver<TransactionStatus<H, H2>>,
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
	pub fn into_stream(self) -> impl Stream<Item=TransactionStatus<H, H2>> {
		self.receiver
	}
}

/// Sender part of the watcher. Exposed only for testing purposes.
#[derive(Debug)]
pub struct Sender<H, H2> {
	receivers: Vec<mpsc::UnboundedSender<TransactionStatus<H, H2>>>,
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
		self.send(TransactionStatus::Ready)
	}

	/// Transaction was moved to future.
	pub fn future(&mut self) {
		self.send(TransactionStatus::Future)
	}

	/// Some state change (perhaps another extrinsic was included) rendered this extrinsic invalid.
	pub fn usurped(&mut self, hash: H) {
		self.send(TransactionStatus::Usurped(hash));
		self.finalized = true;
	}

	/// Extrinsic has been included in block with given hash.
	pub fn in_block(&mut self, hash: H2) {
		self.send(TransactionStatus::InBlock(hash));
		self.finalized = true;
	}

	/// Extrinsic has been marked as invalid by the block builder.
	pub fn invalid(&mut self) {
		self.send(TransactionStatus::Invalid);
		// we mark as finalized as there are no more notifications
		self.finalized = true;
	}

	/// Transaction has been dropped from the pool because of the limit.
	pub fn dropped(&mut self) {
		self.send(TransactionStatus::Dropped);
		self.finalized = true;
	}

	/// The extrinsic has been broadcast to the given peers.
	pub fn broadcast(&mut self, peers: Vec<String>) {
		self.send(TransactionStatus::Broadcast(peers))
	}

	/// Returns true if the are no more listeners for this extrinsic or it was finalized.
	pub fn is_done(&self) -> bool {
		self.finalized || self.receivers.is_empty()
	}

	fn send(&mut self, status: TransactionStatus<H, H2>) {
		self.receivers.retain(|sender| sender.unbounded_send(status.clone()).is_ok())
	}
}
