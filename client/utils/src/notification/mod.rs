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

mod impl_notification_receiver;
mod impl_notification_sender;
mod impl_notification_stream;
mod impl_registry;

/// Trait used to define the "tracing key" string used to tag
/// and identify the mpsc channels.
pub trait TracingKeyStr {
	/// Const `str` representing the "tracing key" used to tag and identify
	/// the mpsc channels owned by the object implemeting this trait.
	const TRACING_KEY: &'static str;
}

#[derive(Debug)]
pub struct NotificationReceiver<Payload> {
	underlying_rx: TracingUnboundedReceiver<Payload>,
	_subs_guard: SubscriptionGuard<Registry<Payload>>,
}

/// The sending half of the notifications channel(s).
///
/// Used to send notifications from the BEEFY gadget side.
pub struct NotificationSender<Payload> {
	registry: SharedRegistry<Registry<Payload>>,
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

/// The shared structure to keep track on subscribers.
#[derive(Debug)]
struct Registry<Payload> {
	id_sequence: IDSequence,
	subscribers: HashMap<SeqID, TracingUnboundedSender<Payload>>,
}

#[cfg(test)]
mod tests;
