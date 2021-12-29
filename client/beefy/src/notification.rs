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

use std::{marker::PhantomData, sync::Arc};

use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use sp_runtime::traits::NumberFor;

use parking_lot::Mutex;

/// A commitment with matching BEEFY authorities' signatures.
pub type BSignedCommitment<Block> =
	beefy_primitives::SignedCommitment<NumberFor<Block>, beefy_primitives::crypto::Signature>;

/// The sending half of the notifications channel(s) used to send
/// notifications about best BEEFY block from the gadget side.
pub type BeefyBestBlockSender<Block> = NotificationSender<NumberFor<Block>>;

/// The receiving half of a notifications channel used to receive
/// notifications about best BEEFY blocks determined on the gadget side.
pub type BeefyBestBlockStream<Block> =
	NotificationStream<NumberFor<Block>, BeefyBestBlockTracingKey>;

/// The sending half of the notifications channel(s) used to send notifications
/// about signed commitments generated at the end of a BEEFY round.
pub type BeefySignedCommitmentSender<Block> = NotificationSender<BSignedCommitment<Block>>;

/// The receiving half of a notifications channel used to receive notifications
/// about signed commitments generated at the end of a BEEFY round.
pub type BeefySignedCommitmentStream<Block> =
	NotificationStream<BSignedCommitment<Block>, BeefySignedCommitmentTracingKey>;

/// Collection of channel sending endpoints shared with the receiver side so they can register
/// themselves.
type SharedSenders<Payload> = Arc<Mutex<Vec<TracingUnboundedSender<Payload>>>>;

pub trait TracingKeyStr {
	const TRACING_KEY: &'static str;
}

/// Provides tracing key for BEEFY best block stream.
#[derive(Clone)]
pub struct BeefyBestBlockTracingKey;
impl TracingKeyStr for BeefyBestBlockTracingKey {
	const TRACING_KEY: &'static str = "mpsc_beefy_best_block_notification_stream";
}

/// Provides tracing key for BEEFY signed commitments stream.
#[derive(Clone)]
pub struct BeefySignedCommitmentTracingKey;
impl TracingKeyStr for BeefySignedCommitmentTracingKey {
	const TRACING_KEY: &'static str = "mpsc_beefy_signed_commitments_notification_stream";
}

/// The sending half of the notifications channel(s).
///
/// Used to send notifications from the BEEFY gadget side.
#[derive(Clone)]
pub struct NotificationSender<Payload: Clone> {
	subscribers: SharedSenders<Payload>,
}

impl<Payload: Clone> NotificationSender<Payload> {
	/// The `subscribers` should be shared with a corresponding `NotificationStream`.
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
/// The `NotificationStream` entity stores the `SharedSenders` so it can be
/// used to add more subscriptions.
#[derive(Clone)]
pub struct NotificationStream<Payload: Clone, TK: TracingKeyStr> {
	subscribers: SharedSenders<Payload>,
	_trace_key: PhantomData<TK>,
}

impl<Payload: Clone, TK: TracingKeyStr> NotificationStream<Payload, TK> {
	/// Creates a new pair of receiver and sender of `Payload` notifications.
	pub fn channel() -> (NotificationSender<Payload>, Self) {
		let subscribers = Arc::new(Mutex::new(vec![]));
		let receiver = NotificationStream::new(subscribers.clone());
		let sender = NotificationSender::new(subscribers);
		(sender, receiver)
	}

	/// Create a new receiver of `Payload` notifications.
	///
	/// The `subscribers` should be shared with a corresponding `NotificationSender`.
	fn new(subscribers: SharedSenders<Payload>) -> Self {
		Self { subscribers, _trace_key: PhantomData }
	}

	/// Subscribe to a channel through which signed commitments are sent at the end of each BEEFY
	/// voting round.
	pub fn subscribe(&self) -> TracingUnboundedReceiver<Payload> {
		let (sender, receiver) = tracing_unbounded(TK::TRACING_KEY);
		self.subscribers.lock().push(sender);
		receiver
	}
}
