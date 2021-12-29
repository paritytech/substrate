// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! Provides mpsc notification channel that can be instantiated
//! _after_ it's been shared to the consumer and producers entities.
//!
//! Useful when building RPC extensions where, at service definition time, we
//! don't know whether the specific interface where the RPC extension will be
//! exposed is safe or not and we want to lazily build the RPC extension
//! whenever we bind the service to an interface.
//!
//! See [`sc-service::builder::RpcExtensionBuilder`] for more details.

use std::{marker::PhantomData, sync::Arc};

use crate::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};

use parking_lot::Mutex;

/// Collection of channel sending endpoints shared with the receiver side
/// so they can register themselves.
type SharedSenders<Payload> = Arc<Mutex<Vec<TracingUnboundedSender<Payload>>>>;

/// Trait used to define the "tracing key" string used to tag
/// and identify the mpsc channels;
pub trait TracingKeyStr {
	const TRACING_KEY: &'static str;
}

/// The sending half of the notifications channel(s).
///
/// Used to send notifications from the BEEFY gadget side.
#[derive(Clone)]
pub struct NotificationSender<Payload: Clone, Error> {
	subscribers: SharedSenders<Payload>,
	_err: PhantomData<Error>,
}

impl<Payload: Clone, Error> NotificationSender<Payload, Error> {
	/// The `subscribers` should be shared with a corresponding `NotificationStream`.
	fn new(subscribers: SharedSenders<Payload>) -> Self {
		Self { subscribers, _err: PhantomData }
	}

	/// Send out a notification to all subscribers that a new payload is available for a
	/// block.
	pub fn notify(&self, payload: impl FnOnce() -> Result<Payload, Error>) -> Result<(), Error> {
		let mut subscribers = self.subscribers.lock();

		// do an initial prune on closed subscriptions
		subscribers.retain(|n| !n.is_closed());

		if !subscribers.is_empty() {
			let payload = payload()?;
			subscribers.retain(|n| n.unbounded_send(payload.clone()).is_ok());
		}

		Ok(())
	}
}

/// The receiving half of the notifications channel.
///
/// Used to receive notifications generated at the BEEFY gadget side.
/// The `NotificationStream` entity stores the `SharedSenders` so it can be
/// used to add more subscriptions.
#[derive(Clone)]
pub struct NotificationStream<Payload: Clone, TK: TracingKeyStr, Error> {
	subscribers: SharedSenders<Payload>,
	_trace_key: PhantomData<TK>,
	_err: PhantomData<Error>,
}

impl<Payload: Clone, TK: TracingKeyStr, Error> NotificationStream<Payload, TK, Error> {
	/// Creates a new pair of receiver and sender of `Payload` notifications.
	pub fn channel() -> (NotificationSender<Payload, Error>, Self) {
		let subscribers = Arc::new(Mutex::new(vec![]));
		let receiver = NotificationStream::new(subscribers.clone());
		let sender = NotificationSender::new(subscribers);
		(sender, receiver)
	}

	/// Create a new receiver of `Payload` notifications.
	///
	/// The `subscribers` should be shared with a corresponding `NotificationSender`.
	fn new(subscribers: SharedSenders<Payload>) -> Self {
		Self { subscribers, _trace_key: PhantomData, _err: PhantomData }
	}

	/// Subscribe to a channel through which signed commitments are sent at the end of each BEEFY
	/// voting round.
	pub fn subscribe(&self) -> TracingUnboundedReceiver<Payload> {
		let (sender, receiver) = tracing_unbounded(TK::TRACING_KEY);
		self.subscribers.lock().push(sender);
		receiver
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use futures::{future, task::Poll, StreamExt};

	#[derive(Clone)]
	pub struct DummyTracingKey;
	impl TracingKeyStr for DummyTracingKey {
		const TRACING_KEY: &'static str = "test_notification_stream";
	}

	type StringStream = NotificationStream<String, DummyTracingKey, ()>;

	#[test]
	fn notification_channel_simple() {
		let (sender, stream) = StringStream::channel();

		let test_payload = String::from("test payload");
		let closure_payload = test_payload.clone();
		let mut times = 0;
		let allow_once = future::poll_fn(|_cx| {
			times += 1;
			if times <= 1 {
				Poll::Pending
			} else {
				Poll::Ready(())
			}
		});

		// Create a future to receive a single notification
		// from the stream and verify its payload.
		let future = stream.subscribe().take_until(allow_once).for_each(move |payload| {
			let test_payload = closure_payload.clone();
			async move {
				assert_eq!(payload, test_payload);
			}
		});

		// Send notification.
		sender.notify(|| Ok(test_payload)).unwrap();

		// Run receiver future.
		tokio_test::block_on(future);
	}
}
