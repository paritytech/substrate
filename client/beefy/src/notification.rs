// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use std::sync::Arc;

use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use sp_runtime::traits::{Block, NumberFor};

use parking_lot::Mutex;

/// Stream of signed commitments returned when subscribing.
pub type SignedCommitment<Block> =
	beefy_primitives::SignedCommitment<NumberFor<Block>, beefy_primitives::crypto::Signature>;

/// Stream of signed commitments returned when subscribing.
type SignedCommitmentStream<Block> = TracingUnboundedReceiver<SignedCommitment<Block>>;

/// Sending endpoint for notifying about signed commitments.
type SignedCommitmentSender<Block> = TracingUnboundedSender<SignedCommitment<Block>>;

/// Collection of channel sending endpoints shared with the receiver side so they can register
/// themselves.
type SharedSignedCommitmentSenders<Block> = Arc<Mutex<Vec<SignedCommitmentSender<Block>>>>;

/// The sending half of the signed commitment channel(s).
///
/// Used to send notifications about signed commitments generated at the end of a BEEFY round.
#[derive(Clone)]
pub struct BeefySignedCommitmentSender<B>
where
	B: Block,
{
	subscribers: SharedSignedCommitmentSenders<B>,
}

impl<B> BeefySignedCommitmentSender<B>
where
	B: Block,
{
	/// The `subscribers` should be shared with a corresponding `SignedCommitmentSender`.
	fn new(subscribers: SharedSignedCommitmentSenders<B>) -> Self {
		Self { subscribers }
	}

	/// Send out a notification to all subscribers that a new signed commitment is available for a
	/// block.
	pub fn notify(&self, signed_commitment: SignedCommitment<B>) {
		let mut subscribers = self.subscribers.lock();

		// do an initial prune on closed subscriptions
		subscribers.retain(|n| !n.is_closed());

		if !subscribers.is_empty() {
			subscribers.retain(|n| n.unbounded_send(signed_commitment.clone()).is_ok());
		}
	}
}

/// The receiving half of the signed commitments channel.
///
/// Used to receive notifications about signed commitments generated at the end of a BEEFY round.
/// The `BeefySignedCommitmentStream` entity stores the `SharedSignedCommitmentSenders` so it can be
/// used to add more subscriptions.
#[derive(Clone)]
pub struct BeefySignedCommitmentStream<B>
where
	B: Block,
{
	subscribers: SharedSignedCommitmentSenders<B>,
}

impl<B> BeefySignedCommitmentStream<B>
where
	B: Block,
{
	/// Creates a new pair of receiver and sender of signed commitment notifications.
	pub fn channel() -> (BeefySignedCommitmentSender<B>, Self) {
		let subscribers = Arc::new(Mutex::new(vec![]));
		let receiver = BeefySignedCommitmentStream::new(subscribers.clone());
		let sender = BeefySignedCommitmentSender::new(subscribers);
		(sender, receiver)
	}

	/// Create a new receiver of signed commitment notifications.
	///
	/// The `subscribers` should be shared with a corresponding `BeefySignedCommitmentSender`.
	fn new(subscribers: SharedSignedCommitmentSenders<B>) -> Self {
		Self { subscribers }
	}

	/// Subscribe to a channel through which signed commitments are sent at the end of each BEEFY
	/// voting round.
	pub fn subscribe(&self) -> SignedCommitmentStream<B> {
		let (sender, receiver) = tracing_unbounded("mpsc_signed_commitments_notification_stream");
		self.subscribers.lock().push(sender);
		receiver
	}
}
