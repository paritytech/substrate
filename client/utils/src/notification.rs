// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use futures::stream::{FusedStream, Stream};
use std::{
	pin::Pin,
	task::{Context, Poll},
};

use crate::pubsub::{Hub, Receiver};

mod registry;
use registry::Registry;

#[cfg(test)]
mod tests;

/// Trait used to define the "tracing key" string used to tag
/// and identify the mpsc channels.
pub trait TracingKeyStr {
	/// Const `str` representing the "tracing key" used to tag and identify
	/// the mpsc channels owned by the object implemeting this trait.
	const TRACING_KEY: &'static str;
}

/// The receiving half of the notifications channel.
///
/// The [`NotificationStream`] entity stores the [`Hub`] so it can be
/// used to add more subscriptions.
#[derive(Clone)]
pub struct NotificationStream<Payload, TK: TracingKeyStr> {
	hub: Hub<Payload, Registry>,
	_pd: std::marker::PhantomData<TK>,
}

/// The receiving half of the notifications channel(s).
#[derive(Debug)]
pub struct NotificationReceiver<Payload> {
	receiver: Receiver<Payload, Registry>,
}

/// The sending half of the notifications channel(s).
pub struct NotificationSender<Payload> {
	hub: Hub<Payload, Registry>,
}

impl<Payload, TK: TracingKeyStr> NotificationStream<Payload, TK> {
	/// Creates a new pair of receiver and sender of `Payload` notifications.
	pub fn channel() -> (NotificationSender<Payload>, Self) {
		let hub = Hub::new(TK::TRACING_KEY);
		let sender = NotificationSender { hub: hub.clone() };
		let receiver = NotificationStream { hub, _pd: Default::default() };
		(sender, receiver)
	}

	/// Subscribe to a channel through which the generic payload can be received.
	pub fn subscribe(&self, queue_size_warning: usize) -> NotificationReceiver<Payload> {
		let receiver = self.hub.subscribe((), queue_size_warning);
		NotificationReceiver { receiver }
	}
}

impl<Payload> NotificationSender<Payload> {
	/// Send out a notification to all subscribers that a new payload is available for a
	/// block.
	pub fn notify<Error>(
		&self,
		payload: impl FnOnce() -> Result<Payload, Error>,
	) -> Result<(), Error>
	where
		Payload: Clone,
	{
		self.hub.send(payload)
	}
}

impl<Payload> Clone for NotificationSender<Payload> {
	fn clone(&self) -> Self {
		Self { hub: self.hub.clone() }
	}
}

impl<Payload> Unpin for NotificationReceiver<Payload> {}

impl<Payload> Stream for NotificationReceiver<Payload> {
	type Item = Payload;

	fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Payload>> {
		Pin::new(&mut self.get_mut().receiver).poll_next(cx)
	}
}

impl<Payload> FusedStream for NotificationReceiver<Payload> {
	fn is_terminated(&self) -> bool {
		self.receiver.is_terminated()
	}
}
