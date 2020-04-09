// Copyright 2017-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Registering events streams.
//!
//! This code holds the logic that is used for the network service to inform other parts of
//! Substrate about what is happening.
//!
//! # Usage
//!
//! - Create an instance of [`OutChannels`].
//! - Create channels using the [`channel`] function. The receiving side implements the `Stream`
//! trait.
//! - You cannot directly send an event on a sender. Instead, you have to call
//! [`OutChannels::push`] to associate the sender with the [`OutChannels`].
//! - Send events by calling [`OutChannels::send`]. Events are cloned for each sender in the
//! collection.
//! - Collect stats by calling [`OutChannels::lock_stats`].
//!

use crate::Event;

use futures::{prelude::*, channel::mpsc, ready};
use parking_lot::Mutex;
use sp_runtime::ConsensusEngineId;
use std::{
	collections::HashMap,
	convert::TryFrom as _,
	fmt, ops::Deref, pin::Pin, sync::Arc,
	task::{Context, Poll}
};

/// Creates a new channel that can be associated to a [`OutChannels`].
pub fn channel() -> (Sender, Receiver) {
	let (tx, rx) = mpsc::unbounded();
	let stats = Arc::new(Mutex::new(None));
	let tx = Sender { inner: tx, stats: stats.clone() };
	let rx = Receiver { inner: rx, stats };
	(tx, rx)
}

/// Sending side of a channel.
///
/// Must be associated with an [`OutChannels`] before anything can be sent on it
///
/// > **Note**: Contrary to regular channels, this `Sender` is purposefully designed to not
/// > implement the `Clone` trait. If someone adds a `#[derive(Clone)]` below, it is **wrong**.
pub struct Sender {
	inner: mpsc::UnboundedSender<Event>,
	/// Clone of [`Receiver::stats`].
	stats: Arc<Mutex<Option<Arc<Mutex<StatsCollect>>>>>,
}

impl fmt::Debug for Sender {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_tuple("Sender").finish()
	}
}

/// Receiving side of a channel.
pub struct Receiver {
	inner: mpsc::UnboundedReceiver<Event>,
	/// Initially contains `None`, and will be set to a value once the corresponding [`Sender`]
	/// is assigned to an instance of [`OutChannels`].
	stats: Arc<Mutex<Option<Arc<Mutex<StatsCollect>>>>>,
}

impl Stream for Receiver {
	type Item = Event;

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Event>> {
		if let Some(ev) = ready!(Pin::new(&mut self.inner).poll_next(cx)) {
			let stats = self.stats.lock();
			if let Some(stats) = stats.as_ref() {
				decrease_stats(&mut *stats.lock(), &ev);
			} else {
				log::warn!("Inconsistency in out_events: event happened before sender associated");
			}
			Poll::Ready(Some(ev))
		} else {
			Poll::Ready(None)
		}
	}
}

impl fmt::Debug for Receiver {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_tuple("Receiver").finish()
	}
}

impl Drop for Receiver {
	fn drop(&mut self) {
		// Empty the list to properly decrease the stats.
		while let Some(Some(_)) = self.next().now_or_never() {}
	}
}

/// Statistics about the content of the channel.
#[non_exhaustive]
pub struct StatsCollect {
	/// For each protocol, total number of substream open notifications in the channel.
	pub notifications_open_messages_count: HashMap<ConsensusEngineId, u64>,

	/// For each protocol, total number of substream closed notifications in the channel.
	pub notifications_closed_messages_count: HashMap<ConsensusEngineId, u64>,

	/// For each protocol, the total size of all notifications stuck in the channel.
	pub notifications_sizes_total: HashMap<ConsensusEngineId, u64>,

	/// Number of DHT events in the channel.
	///
	/// > **Note**: DHT events are extremely rare at the moment, but this could be broken down
	/// >			further if there's a need to.
	pub dht_events: u64,
}

/// Collection of senders.
pub struct OutChannels {
	event_streams: Vec<Sender>,
	/// The stats we collect. A clone of this is sent to each [`Receiver`] associated with this
	/// object.
	stats: Arc<Mutex<StatsCollect>>,
}

impl OutChannels {
	/// Creates a new empty collection of senders.
	pub fn new() -> Self {
		OutChannels {
			event_streams: Vec::new(),
			stats: Arc::new(Mutex::new(StatsCollect {
				notifications_open_messages_count: HashMap::new(),
				notifications_closed_messages_count: HashMap::new(),
				notifications_sizes_total: HashMap::new(),
				dht_events: 0,
			}))
		}
	}

	/// Adds a new [`Sender`] to the collection.
	pub fn push(&mut self, sender: Sender) {
		let mut stats = sender.stats.lock();
		debug_assert!(stats.is_none());
		*stats = Some(self.stats.clone());
		drop(stats);
		self.event_streams.push(sender);
	}

	/// Returns the number of senders in the collection.
	pub fn len(&self) -> usize {
		self.event_streams.len()
	}

	/// Sends an event.
	pub fn send(&mut self, event: Event) {
		self.event_streams.retain(|sender| {
			sender.inner.unbounded_send(event.clone()).is_ok()
		});

		// The number of elements remaining in `event_streams` corresponds to the number of times
		// we have sent an element on the channel.
		let mut stats = self.stats.lock();
		for _ in 0..self.event_streams.len() {
			increase_stats(&mut stats, &event);
		}
	}

	/// Returns statistics about the content of the channel.
	///
	/// > **Important**: This function returns a mutex lock. As long as it is not disposed of,
	/// >				 receivers will block receiving any message.
	pub fn lock_stats<'a>(&'a self) -> impl Deref<Target = StatsCollect> + 'a {
		self.stats.lock()
	}
}

impl fmt::Debug for OutChannels {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_struct("OutChannels")
			.field("num_channels", &self.event_streams.len())
			.finish()
	}
}

fn increase_stats(stats: &mut StatsCollect, event: &Event) {
	match event {
		Event::Dht(_) => stats.dht_events = stats.dht_events.wrapping_add(1),
		Event::NotificationStreamOpened { engine_id, .. } => {
			let val = stats.notifications_open_messages_count.entry(*engine_id).or_insert(0);
			*val = val.wrapping_add(1);
		},
		Event::NotificationStreamClosed { engine_id, .. } => {
			let val = stats.notifications_closed_messages_count.entry(*engine_id).or_insert(0);
			*val = val.wrapping_add(1);
		},
		Event::NotificationsReceived { messages, .. } => {
			for (engine_id, message) in messages {
				let val = stats.notifications_sizes_total.entry(*engine_id).or_insert(0);
				*val = val.wrapping_add(u64::try_from(message.len()).unwrap_or(u64::max_value()));
			}
		},
	}
}

fn decrease_stats(stats: &mut StatsCollect, event: &Event) {
	match event {
		Event::Dht(_) => stats.dht_events = stats.dht_events.wrapping_sub(1),
		Event::NotificationStreamOpened { engine_id, .. } => {
			let val = stats.notifications_open_messages_count.entry(*engine_id).or_insert(0);
			*val = val.wrapping_sub(1);
		},
		Event::NotificationStreamClosed { engine_id, .. } => {
			let val = stats.notifications_closed_messages_count.entry(*engine_id).or_insert(0);
			*val = val.wrapping_sub(1);
		},
		Event::NotificationsReceived { messages, .. } => {
			for (engine_id, message) in messages {
				let val = stats.notifications_sizes_total.entry(*engine_id).or_insert(0);
				*val = val.wrapping_sub(u64::try_from(message.len()).unwrap_or(u64::max_value()));
			}
		},
	}
}
