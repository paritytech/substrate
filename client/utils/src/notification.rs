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

use std::collections::HashMap;

use crate::{
	id_sequence::{IDSequence, SeqID},
	mpsc::{TracingUnboundedReceiver, TracingUnboundedSender},
	pubsub::{SharedRegistry, SubscriptionGuard},
};

mod impl_traits;

mod registry;
use registry::Registry;

/// Trait used to define the "tracing key" string used to tag
/// and identify the mpsc channels.
pub trait TracingKeyStr {
	/// Const `str` representing the "tracing key" used to tag and identify
	/// the mpsc channels owned by the object implemeting this trait.
	const TRACING_KEY: &'static str;
}

/// The receiving half of the notifications channel.
///
/// The `NotificationStream` entity stores the `SharedSenders` so it can be
/// used to add more subscriptions.
#[derive(Clone)]
pub struct NotificationStream<Payload, TK: TracingKeyStr> {
	registry: SharedRegistry<Registry<Payload>>,
	_pd: std::marker::PhantomData<TK>,
}

/// The receiving half of the notifications channel(s).
#[derive(Debug)]
pub struct NotificationReceiver<Payload> {
	subs_guard: SubscriptionGuard<Registry<Payload>, TracingUnboundedReceiver<Payload>>,
}

/// The sending half of the notifications channel(s).
///
/// Used to send notifications from the BEEFY gadget side.
pub struct NotificationSender<Payload> {
	registry: SharedRegistry<Registry<Payload>>,
}

impl<Payload, TK: TracingKeyStr> NotificationStream<Payload, TK> {
	/// Creates a new pair of receiver and sender of `Payload` notifications.
	pub fn channel() -> (NotificationSender<Payload>, Self) {
		let registry = SharedRegistry::<Registry<Payload>>::default();
		let sender = NotificationSender::new(registry.clone());
		let receiver = NotificationStream::new(registry);
		(sender, receiver)
	}

	/// Create a new receiver of `Payload` notifications.
	///
	/// The `subscribers` should be shared with a corresponding `NotificationSender`.
	fn new(registry: SharedRegistry<Registry<Payload>>) -> Self {
		Self { registry, _pd: Default::default() }
	}

	/// Subscribe to a channel through which the generic payload can be received.
	pub fn subscribe(&self) -> NotificationReceiver<Payload> {
		let (underlying_tx, underlying_rx) = crate::mpsc::tracing_unbounded(TK::TRACING_KEY);
		let subs_guard = self.registry.subscribe(underlying_tx).with_rx(underlying_rx);
		let receiver = NotificationReceiver { subs_guard };
		receiver
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
		// The subscribers collection used to be cleaned upon send previously.
		// The set used to be cleaned up twice:
		// - once before sending: filter on `!tx.is_closed()`;
		// - once while sending: filter on `!tx.unbounded_send().is_err()`.
		//
		// Since there is no `close` or `disconnect` operation defined on the
		// `NotificationReceiver<Payload>`, the only way to close the `rx` is to drop it.
		// Upon being dropped the `NotificationReceiver<Payload>` unregisters its `rx`
		// from the registry using its `_subs_guard`.
		//
		// So there's no need to clean up the subscribers set upon sending another message.

		let registry = self.registry.lock();
		let subscribers = &registry.subscribers;

		if !subscribers.is_empty() {
			let payload = payload()?;
			for (_subs_id, tx) in subscribers {
				let _ = tx.unbounded_send(payload.clone());
			}
		}

		Ok(())
	}

	/// The `subscribers` should be shared with a corresponding `NotificationStream`.
	fn new(registry: SharedRegistry<Registry<Payload>>) -> Self {
		Self { registry }
	}
}

#[cfg(test)]
mod tests;
