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

use std::{
	collections::HashMap,
	ops::DerefMut,
	pin::Pin,
	sync::{Arc, Weak},
	task::{Context, Poll},
};

use ::futures::stream::{FusedStream, Stream};
use ::parking_lot::Mutex;

pub mod channels;

pub type SubsID = crate::id_sequence::SeqID;

/// Unsubscribe: unregisters a previously created subscription.
pub trait Unsubscribe {
	fn unsubscribe(&mut self, subs_id: &SubsID);
}

/// Subscribe using a key of type `K`
pub trait Subscribe<K> {
	fn subscribe(&mut self, subs_key: K, subs_id: SubsID);
}

/// Dispatch a message of type `M`.
pub trait Dispatch<M> {
	type Item;
	fn dispatch<F>(&mut self, message: M, dispatch: F)
	where
		F: FnMut(&SubsID, Self::Item);
}

/// Channel routines.
///
/// Allows to create a pair of tx and rx, and to send a message over the tx.
pub trait Channel {
	type Tx;
	type Rx;
	type Item;

	fn create(&self) -> (Self::Tx, Self::Rx);
	fn send(&self, tx: &mut Self::Tx, item: Self::Item);
}

/// A subscription hub.
///
/// Does the subscription and dispatch.
/// The exact subscription and routing behaviour is to be implemented by the Registry (of type `R`).
/// The Hub manages the underlying channels using the `Ch: Channel`.
#[derive(Debug)]
pub struct Hub<Ch, R>
where
	Ch: Channel,
{
	channel: Ch,
	shared: Arc<Mutex<Shared<R, Ch::Tx>>>,
}

/// The receiving side of the subscription.
///
/// The messages are delivered as items of a `futures::Stream`.
/// Upon drop this receiver unsubscribes itself from the `Hub`.
#[derive(Debug)]
pub struct Receiver<Ch, R>
where
	Ch: Channel,
	R: Unsubscribe,
{
	// NB: this field should be defined before `rx`.
	// (The fields of a struct are dropped in declaration order.)[https://doc.rust-lang.org/reference/destructors.html]
	_unsubs_guard: UnsubscribeGuard<R, Ch::Tx>,

	// NB: this field should be defined after `_unsubs_guard`.
	rx: Ch::Rx,
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

impl<Ch, R> Hub<Ch, R>
where
	Ch: Channel,
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
			shared.lock().unsubscribe(&self.subs_id);
		}
	}
}

impl<Ch, Tx, R> Hub<Ch, R>
where
	Ch: Channel<Tx = Tx>,
{
	/// Create a new instance of Hub (with default value for the Registry).
	pub fn new(channel: Ch) -> Self
	where
		R: Default,
	{
		Self::new_with_registry(channel, Default::default())
	}

	/// Create a new instance of Hub over the initialized Registry.
	pub fn new_with_registry(channel: Ch, registry: R) -> Self {
		let shared =
			Shared { registry, sinks: Default::default(), id_sequence: Default::default() };
		let shared = Arc::new(Mutex::new(shared));
		Self { channel, shared }
	}

	/// Subscribe to this Hub using the `subs_key: K`.
	///
	/// A subscription with a key `K` is possible if the Registry implements `Subscribe<K>`.
	pub fn subscribe<K>(&self, subs_key: K) -> Receiver<Ch, R>
	where
		R: Subscribe<K> + Unsubscribe,
	{
		let mut shared = self.shared.lock();

		let subs_id = shared.id_sequence.next_id();
		let (tx, rx) = self.channel.create();
		assert!(shared.sinks.insert(subs_id, tx).is_none(), "Used IDSequence to create another ID. Should be unique until u64 is overflowed. Should be unique.");
		shared.registry.subscribe(subs_key, subs_id);

		let unsubs_guard = UnsubscribeGuard { shared: Arc::downgrade(&self.shared), subs_id };
		Receiver { _unsubs_guard: unsubs_guard, rx }
	}

	/// Dispatch the message of type `M`.
	///
	/// This is possible if the registry implements `Dispatch<M>`.
	pub fn dispatch<M>(&self, message: M)
	where
		R: Dispatch<M, Item = Ch::Item>,
	{
		let mut shared = self.shared.lock();
		let (registry, sinks) = shared.get_mut();

		registry.dispatch(message, |subs_id, item| {
			if let Some(tx) = sinks.get_mut(&subs_id) {
				self.channel.send(tx, item)
			}
			// This create does not have `log` as a dependency.
			// Not sure such dependency should be added.
			// But if there was a possibility to log something,
			// the following warn-message would be appropriate:
			/* else {
				log::warn!(
					"{} as Dispatch<{}>::dispatch(...). No Sink for SubsID = {}",
					std::any::type_name::<R>(),
					std::any::type_name::<K>(),
					subs_id
				);
			}*/
		});
	}
}

impl<R, Tx> Shared<R, Tx> {
	fn get_mut(&mut self) -> (&mut R, &mut HashMap<SubsID, Tx>) {
		(&mut self.registry, &mut self.sinks)
	}

	fn unsubscribe(&mut self, subs_id: &SubsID)
	where
		R: Unsubscribe,
	{
		self.registry.unsubscribe(subs_id);
		self.sinks.remove(subs_id);
	}
}

impl<Ch, R> Clone for Hub<Ch, R>
where
	Ch: Channel + Clone,
{
	fn clone(&self) -> Self {
		Self { channel: self.channel.clone(), shared: self.shared.clone() }
	}
}

impl<Ch, R> Unpin for Receiver<Ch, R>
where
	Ch: Channel,
	R: Unsubscribe,
{
}

impl<Ch, R> Stream for Receiver<Ch, R>
where
	Ch: Channel,
	R: Unsubscribe,
	Ch::Rx: Stream + Unpin,
{
	type Item = <Ch::Rx as Stream>::Item;

	fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
		Pin::new(&mut self.get_mut().rx).poll_next(cx)
	}
}

impl<Ch, R> FusedStream for Receiver<Ch, R>
where
	Ch: Channel,
	R: Unsubscribe,
	Ch::Rx: FusedStream + Unpin,
{
	fn is_terminated(&self) -> bool {
		self.rx.is_terminated()
	}
}
