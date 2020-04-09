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
//! [`OutChannels::push`] to put the sender within a [`OutChannels`].
//! - Send events by calling [`OutChannels::send`]. Events are cloned for each sender in the
//! collection.
//!

use crate::Event;
use super::engine_id_to_string;

use futures::{prelude::*, channel::mpsc, ready};
use parking_lot::Mutex;
use prometheus_endpoint::{Gauge, GaugeVec, U64};
use std::{
	convert::TryFrom as _,
	fmt, pin::Pin, sync::Arc,
	task::{Context, Poll}
};

/// Creates a new channel that can be associated to a [`OutChannels`].
pub fn channel() -> (Sender, Receiver) {
	let (tx, rx) = mpsc::unbounded();
	let metrics = Arc::new(Mutex::new(None));
	let tx = Sender { inner: tx, metrics: metrics.clone() };
	let rx = Receiver { inner: rx, metrics };
	(tx, rx)
}

pub struct Metrics {
	// This list is ordered alphabetically
	pub out_events_dht_count: Gauge<U64>,
	pub out_events_num_channels: Gauge<U64>,
	pub out_events_notifications_closed_count: GaugeVec<U64>,
	pub out_events_notifications_opened_count: GaugeVec<U64>,
	pub out_events_notifications_sizes: GaugeVec<U64>,
}

/// Sending side of a channel.
///
/// Must be associated with an [`OutChannels`] before anything can be sent on it
///
/// > **Note**: Contrary to regular channels, this `Sender` is purposefully designed to not
/// > implement the `Clone` trait. If someone adds a `#[derive(Clone)]` below, it is **wrong**.
pub struct Sender {
	inner: mpsc::UnboundedSender<Event>,
	/// Clone of [`Receiver::metrics`].
	metrics: Arc<Mutex<Option<Arc<Option<Metrics>>>>>,
}

impl fmt::Debug for Sender {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_tuple("Sender").finish()
	}
}

impl Drop for Sender {
	fn drop(&mut self) {
		let metrics = self.metrics.lock();
		if let Some(Some(metrics)) = metrics.as_ref().map(|m| &**m) {
			metrics.out_events_num_channels.dec();
		}
	}
}

/// Receiving side of a channel.
pub struct Receiver {
	inner: mpsc::UnboundedReceiver<Event>,
	/// Initially contains `None`, and will be set to a value once the corresponding [`Sender`]
	/// is assigned to an instance of [`OutChannels`].
	metrics: Arc<Mutex<Option<Arc<Option<Metrics>>>>>,
}

impl Stream for Receiver {
	type Item = Event;

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Event>> {
		if let Some(ev) = ready!(Pin::new(&mut self.inner).poll_next(cx)) {
			let metrics = self.metrics.lock();
			if let Some(Some(metrics)) = metrics.as_ref().map(|m| &**m) {
				decrease_metrics(metrics, &ev);
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
		// Empty the list to properly decrease the metrics.
		while let Some(Some(_)) = self.next().now_or_never() {}
	}
}

/// Collection of senders.
pub struct OutChannels {
	event_streams: Vec<Sender>,
	/// The metrics we collect. A clone of this is sent to each [`Receiver`] associated with this
	/// object.
	metrics: Arc<Option<Metrics>>,
}

impl OutChannels {
	/// Creates a new empty collection of senders.
	pub fn new(metrics: Option<Metrics>) -> Self {
		OutChannels {
			event_streams: Vec::new(),
			metrics: Arc::new(metrics),
		}
	}

	/// Adds a new [`Sender`] to the collection.
	pub fn push(&mut self, sender: Sender) {
		let mut metrics = sender.metrics.lock();
		debug_assert!(metrics.is_none());
		*metrics = Some(self.metrics.clone());
		drop(metrics);
		self.event_streams.push(sender);

		if let Some(metrics) = &*self.metrics {
			metrics.out_events_num_channels.inc();
		}
	}

	/// Sends an event.
	pub fn send(&mut self, event: Event) {
		self.event_streams.retain(|sender| {
			sender.inner.unbounded_send(event.clone()).is_ok()
		});

		// The number of elements remaining in `event_streams` corresponds to the number of times
		// we have sent an element on the channel.
		if let Some(metrics) = &*self.metrics {
			increase_metrics(metrics, &event, self.event_streams.len() as u64);
		}
	}
}

impl fmt::Debug for OutChannels {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_struct("OutChannels")
			.field("num_channels", &self.event_streams.len())
			.finish()
	}
}

fn increase_metrics(metrics: &Metrics, event: &Event, num: u64) {
	match event {
		Event::Dht(_) => metrics.out_events_dht_count.inc(),
		Event::NotificationStreamOpened { engine_id, .. } => {
			metrics.out_events_notifications_opened_count
				.with_label_values(&[&engine_id_to_string(engine_id)])
				.add(num);
		},
		Event::NotificationStreamClosed { engine_id, .. } => {
			metrics.out_events_notifications_closed_count
				.with_label_values(&[&engine_id_to_string(engine_id)])
				.add(num);
		},
		Event::NotificationsReceived { messages, .. } => {
			for (engine_id, message) in messages {
				metrics.out_events_notifications_sizes
					.with_label_values(&[&engine_id_to_string(engine_id)])
					.add(num.saturating_mul(u64::try_from(message.len()).unwrap_or(u64::max_value())));
			}
		},
	}
}

fn decrease_metrics(metrics: &Metrics, event: &Event) {
	match event {
		Event::Dht(_) => metrics.out_events_dht_count.inc(),
		Event::NotificationStreamOpened { engine_id, .. } => {
			metrics.out_events_notifications_opened_count
				.with_label_values(&[&engine_id_to_string(engine_id)])
				.dec();
		},
		Event::NotificationStreamClosed { engine_id, .. } => {
			metrics.out_events_notifications_closed_count
				.with_label_values(&[&engine_id_to_string(engine_id)])
				.dec();
		},
		Event::NotificationsReceived { messages, .. } => {
			for (engine_id, message) in messages {
				metrics.out_events_notifications_sizes
					.with_label_values(&[&engine_id_to_string(engine_id)])
					.sub(u64::try_from(message.len()).unwrap_or(u64::max_value()));
			}
		},
	}
}
