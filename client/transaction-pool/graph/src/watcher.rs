// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Extrinsics status updates.

use futures::Stream;
use sp_transaction_pool::TransactionStatus;
use sp_utils::mpsc::{tracing_unbounded, TracingUnboundedSender, TracingUnboundedReceiver};

/// Extrinsic watcher.
///
/// Represents a stream of status updates for particular extrinsic.
#[derive(Debug)]
pub struct Watcher<H, BH> {
	receiver: TracingUnboundedReceiver<TransactionStatus<H, BH>>,
	hash: H,
}

impl<H, BH> Watcher<H, BH> {
	/// Returns the transaction hash.
	pub fn hash(&self) -> &H {
		&self.hash
	}

	/// Pipe the notifications to given sink.
	///
	/// Make sure to drive the future to completion.
	pub fn into_stream(self) -> impl Stream<Item=TransactionStatus<H, BH>> {
		self.receiver
	}
}

/// Sender part of the watcher. Exposed only for testing purposes.
#[derive(Debug)]
pub struct Sender<H, BH> {
	receivers: Vec<TracingUnboundedSender<TransactionStatus<H, BH>>>,
	is_finalized: bool,
}

impl<H, BH> Default for Sender<H, BH> {
	fn default() -> Self {
		Sender {
			receivers: Default::default(),
			is_finalized: false,
		}
	}
}

impl<H: Clone, BH: Clone> Sender<H, BH> {
	/// Add a new watcher to this sender object.
	pub fn new_watcher(&mut self, hash: H) -> Watcher<H, BH> {
		let (tx, receiver) = tracing_unbounded("mpsc_txpool_watcher");
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
		self.is_finalized = true;
	}

	/// Extrinsic has been included in block with given hash.
	pub fn in_block(&mut self, hash: BH) {
		self.send(TransactionStatus::InBlock(hash));
	}

	/// Extrinsic has been finalized by a finality gadget.
	pub fn finalized(&mut self, hash: BH) {
		self.send(TransactionStatus::Finalized(hash));
		self.is_finalized = true;
	}

	/// The block this extrinsic was included in has been retracted
	pub fn finality_timeout(&mut self, hash: BH) {
		self.send(TransactionStatus::FinalityTimeout(hash));
		self.is_finalized = true;
	}

	/// The block this extrinsic was included in has been retracted
	pub fn retracted(&mut self, hash: BH) {
		self.send(TransactionStatus::Retracted(hash));
	}

	/// Extrinsic has been marked as invalid by the block builder.
	pub fn invalid(&mut self) {
		self.send(TransactionStatus::Invalid);
		// we mark as finalized as there are no more notifications
		self.is_finalized = true;
	}

	/// Transaction has been dropped from the pool because of the limit.
	pub fn dropped(&mut self) {
		self.send(TransactionStatus::Dropped);
		self.is_finalized = true;
	}

	/// The extrinsic has been broadcast to the given peers.
	pub fn broadcast(&mut self, peers: Vec<String>) {
		self.send(TransactionStatus::Broadcast(peers))
	}

	/// Returns true if the are no more listeners for this extrinsic or it was finalized.
	pub fn is_done(&self) -> bool {
		self.is_finalized || self.receivers.is_empty()
	}

	fn send(&mut self, status: TransactionStatus<H, BH>) {
		self.receivers.retain(|sender| sender.unbounded_send(status.clone()).is_ok())
	}
}
