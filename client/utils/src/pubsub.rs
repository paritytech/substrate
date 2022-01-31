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

//! Provides means to implement a typical Pub/Sub mechanism.
//!
//! This module provides a type `Hub` which can be used both to subscribe,
//! and to send the broadcast messages.
//!
//! The `Hub` type is parametrized by two other types:
//! - `Message` — the type of a message that shall be delivered to the subscribers;
//! - `Registry` — implementation of the subscription/dispatch logic.
//!
//! A Registry is implemented by defining the following traits:
//! - `Subscribe<K>`;
//! - `Dispatch<M>`;
//! - `Unsubscribe`.
//!
//! As a result of subscription `Hub::subscribe` method returns an instance of `Receiver<Message,
//! Registry>`. That can be used as a `futures::Stream` to receive the messages.
//! Upon drop the `Receiver<Message, Registry>` shall unregister itself from the `Hub`.

use std::{
	collections::HashMap,
	ops::DerefMut,
	pin::Pin,
	sync::{Arc, Weak},
	task::{Context, Poll},
};

use ::futures::stream::{FusedStream, Stream};
use ::parking_lot::Mutex;

use crate::mpsc::{TracingUnboundedReceiver, TracingUnboundedSender};

/// The type to identify subscribers.
pub type SubsID = crate::id_sequence::SeqID;

/// Unsubscribe: unregisters a previously created subscription.
pub trait Unsubscribe {
	/// Remove all registrations of the subscriber with ID `subs_id`.
	fn unsubscribe(&mut self, subs_id: SubsID);
}

/// Subscribe using a key of type `K`
pub trait Subscribe<K> {
	/// Register subscriber with the ID `subs_id` as having interest to the key `K`.
	fn subscribe(&mut self, subs_key: K, subs_id: SubsID);
}

/// Dispatch a message of type `M`.
pub trait Dispatch<M> {
	/// The type of the that shall be sent through the channel as a result of such dispatch.
	type Item;
	/// The type returned by the `dispatch`-method.
	type Ret;

	/// Dispatch the message of type `M`.
	///
	/// The implementation is given an instance of `M` and is supposed to invoke `dispatch` for
	/// each matching subscriber, with an argument of type `Self::Item` matching that subscriber.
	///
	/// Note that this does not have to be of the same type with the item that will be sent through
	/// to the subscribers. The subscribers will receive a message of type `Self::Item`.
	fn dispatch<F>(&mut self, message: M, dispatch: F) -> Self::Ret
	where
		F: FnMut(&SubsID, Self::Item);
}

/// A subscription hub.
///
/// Does the subscription and dispatch.
/// The exact subscription and routing behaviour is to be implemented by the Registry (of type `R`).
/// The Hub under the hood uses the channel defined in `crate::mpsc` module.
#[derive(Debug)]
pub struct Hub<M, R> {
	tracing_key: &'static str,
	shared: Arc<Mutex<Shared<R, TracingUnboundedSender<M>>>>,
}

/// The receiving side of the subscription.
///
/// The messages are delivered as items of a `futures::Stream`.
/// Upon drop this receiver unsubscribes itself from the `Hub`.
#[derive(Debug)]
pub struct Receiver<M, R>
where
	R: Unsubscribe,
{
	// NB: this field should be defined before `rx`.
	// (The fields of a struct are dropped in declaration order.)[https://doc.rust-lang.org/reference/destructors.html]
	_unsubs_guard: UnsubscribeGuard<R, TracingUnboundedSender<M>>,

	// NB: this field should be defined after `_unsubs_guard`.
	rx: TracingUnboundedReceiver<M>,
}

#[derive(Debug)]
struct UnsubscribeGuard<R, Tx>
where
	R: Unsubscribe,
{
	shared: Weak<Mutex<Shared<R, Tx>>>,
	subs_id: SubsID,
}

#[derive(Debug)]
struct Shared<R, Tx> {
	id_sequence: crate::id_sequence::IDSequence,
	registry: R,
	sinks: HashMap<SubsID, Tx>,
}

impl<R, Tx> AsMut<R> for Shared<R, Tx> {
	fn as_mut(&mut self) -> &mut R {
		&mut self.registry
	}
}

impl<M, R> Hub<M, R>
where
	R: Unsubscribe,
{
	/// Provide mutable access to the registry (for test purposes).
	pub fn lock_registry<'a>(&'a self) -> impl DerefMut<Target = impl AsMut<R>> + 'a {
		self.shared.lock()
	}
}

impl<R, Tx> Drop for UnsubscribeGuard<R, Tx>
where
	R: Unsubscribe,
{
	fn drop(&mut self) {
		if let Some(shared) = self.shared.upgrade() {
			shared.lock().unsubscribe(self.subs_id);
		}
	}
}

impl<M, R> Hub<M, R> {
	/// Create a new instance of Hub (with default value for the Registry).
	pub fn new(tracing_key: &'static str) -> Self
	where
		R: Default,
	{
		Self::new_with_registry(tracing_key, Default::default())
	}

	/// Create a new instance of Hub over the initialized Registry.
	pub fn new_with_registry(tracing_key: &'static str, registry: R) -> Self {
		let shared =
			Shared { registry, sinks: Default::default(), id_sequence: Default::default() };
		let shared = Arc::new(Mutex::new(shared));
		Self { tracing_key, shared }
	}

	/// Subscribe to this Hub using the `subs_key: K`.
	///
	/// A subscription with a key `K` is possible if the Registry implements `Subscribe<K>`.
	pub fn subscribe<K>(&self, subs_key: K) -> Receiver<M, R>
	where
		R: Subscribe<K> + Unsubscribe,
	{
		let mut shared = self.shared.lock();

		let subs_id = shared.id_sequence.next_id();
		let (tx, rx) = crate::mpsc::tracing_unbounded(self.tracing_key);
		assert!(shared.sinks.insert(subs_id, tx).is_none(), "Used IDSequence to create another ID. Should be unique until u64 is overflowed. Should be unique.");
		shared.registry.subscribe(subs_key, subs_id);

		let unsubs_guard = UnsubscribeGuard { shared: Arc::downgrade(&self.shared), subs_id };
		Receiver { _unsubs_guard: unsubs_guard, rx }
	}

	/// Dispatch the message produced with `Trigger`.
	///
	/// This is possible if the registry implements `Dispatch<Trigger, Item = M>`.
	pub fn dispatch<Trigger>(&self, trigger: Trigger)
	where
		R: Dispatch<Trigger, Item = M>,
	{
		let mut shared = self.shared.lock();
		let (registry, sinks) = shared.get_mut();

		registry.dispatch(trigger, |subs_id, item| {
			if let Some(tx) = sinks.get_mut(&subs_id) {
				if let Err(send_err) = tx.unbounded_send(item) {
					log::warn!("Sink with SubsID = {} failed to perform unbounded_send: {} ({} as Dispatch<{}, Item = {}>::dispatch(...))", subs_id, send_err, std::any::type_name::<R>(),
					std::any::type_name::<Trigger>(),
					std::any::type_name::<M>());
				}
			} else {
				log::warn!(
					"No Sink for SubsID = {} ({} as Dispatch<{}, Item = {}>::dispatch(...))",
					subs_id,
					std::any::type_name::<R>(),
					std::any::type_name::<Trigger>(),
					std::any::type_name::<M>(),
				);
			}
		});
	}
}

impl<R, Tx> Shared<R, Tx> {
	fn get_mut(&mut self) -> (&mut R, &mut HashMap<SubsID, Tx>) {
		(&mut self.registry, &mut self.sinks)
	}

	fn unsubscribe(&mut self, subs_id: SubsID)
	where
		R: Unsubscribe,
	{
		self.registry.unsubscribe(subs_id);
		self.sinks.remove(&subs_id);
	}
}

impl<M, R> Clone for Hub<M, R> {
	fn clone(&self) -> Self {
		Self { tracing_key: self.tracing_key, shared: self.shared.clone() }
	}
}

impl<M, R> Unpin for Receiver<M, R> where R: Unsubscribe {}

impl<M, R> Stream for Receiver<M, R>
where
	R: Unsubscribe,
{
	type Item = <TracingUnboundedReceiver<M> as Stream>::Item;

	fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
		Pin::new(&mut self.get_mut().rx).poll_next(cx)
	}
}

impl<Ch, R> FusedStream for Receiver<Ch, R>
where
	R: Unsubscribe,
{
	fn is_terminated(&self) -> bool {
		self.rx.is_terminated()
	}
}
