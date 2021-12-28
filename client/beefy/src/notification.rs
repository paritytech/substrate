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
use sp_runtime::traits::NumberFor;

use parking_lot::Mutex;

/// A commitment with matching GRANDPA validators' signatures.
pub type BSignedCommitment<Block> =
	beefy_primitives::SignedCommitment<NumberFor<Block>, beefy_primitives::crypto::Signature>;

/// Collection of channel sending endpoints shared with the receiver side so they can register
/// themselves.
type SharedSenders<Payload> = Arc<Mutex<Vec<TracingUnboundedSender<Payload>>>>;

/// The sending half of the notifications channel(s).
///
/// Used to send notifications from the BEEFY gadget side.
#[derive(Clone)]
pub struct BeefyNotificationSender<Payload: Clone> {
	subscribers: SharedSenders<Payload>,
}

impl<Payload: Clone> BeefyNotificationSender<Payload> {
	/// The `subscribers` should be shared with a corresponding `BeefyNotificationStream`.
	fn new(subscribers: SharedSenders<Payload>) -> Self {
		Self { subscribers }
	}

	/// Send out a notification to all subscribers that a new payload is available for a
	/// block.
	pub fn notify(&self, signed_commitment: Payload) {
		let mut subscribers = self.subscribers.lock();

		// do an initial prune on closed subscriptions
		subscribers.retain(|n| !n.is_closed());

		if !subscribers.is_empty() {
			subscribers.retain(|n| n.unbounded_send(signed_commitment.clone()).is_ok());
		}
	}
}

/// The receiving half of the notifications channel.
///
/// Used to receive notifications generated at the BEEFY gadget side.
/// The `BeefyNotificationStream` entity stores the `SharedSenders` so it can be
/// used to add more subscriptions.
#[derive(Clone)]
pub struct BeefyNotificationStream<Payload: Clone> {
	subscribers: SharedSenders<Payload>,
}

impl<Payload: Clone> BeefyNotificationStream<Payload> {
	/// Creates a new pair of receiver and sender of `Payload` notifications.
	pub fn channel() -> (BeefyNotificationSender<Payload>, Self) {
		let subscribers = Arc::new(Mutex::new(vec![]));
		let receiver = BeefyNotificationStream::new(subscribers.clone());
		let sender = BeefyNotificationSender::new(subscribers);
		(sender, receiver)
	}

	/// Create a new receiver of `Payload` notifications.
	///
	/// The `subscribers` should be shared with a corresponding `BeefyNotificationSender`.
	fn new(subscribers: SharedSenders<Payload>) -> Self {
		Self { subscribers }
	}

	/// Subscribe to a channel through which signed commitments are sent at the end of each BEEFY
	/// voting round.
	pub fn subscribe(&self) -> TracingUnboundedReceiver<Payload> {
		let (sender, receiver) = tracing_unbounded("mpsc_signed_commitments_notification_stream");
		self.subscribers.lock().push(sender);
		receiver
	}
}
