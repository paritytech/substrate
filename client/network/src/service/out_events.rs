// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use futures::{channel::mpsc, prelude::*, ready, stream::FusedStream};
use parking_lot::Mutex;
use prometheus_endpoint::{register, CounterVec, GaugeVec, Opts, PrometheusError, Registry, U64};
use sc_network_common::protocol::event::Event;
use std::{
	cell::RefCell,
	fmt,
	pin::Pin,
	sync::Arc,
	task::{Context, Poll},
};

/// Creates a new channel that can be associated to a [`OutChannels`].
///
/// The name is used in Prometheus reports.
pub fn channel(name: &'static str) -> (Sender, Receiver) {
	let (tx, rx) = mpsc::unbounded();
	let metrics = Arc::new(Mutex::new(None));
	let tx = Sender { inner: tx, name, metrics: metrics.clone() };
	let rx = Receiver { inner: rx, name, metrics };
	(tx, rx)
}

/// Sending side of a channel.
///
/// Must be associated with an [`OutChannels`] before anything can be sent on it
///
/// > **Note**: Contrary to regular channels, this `Sender` is purposefully designed to not
/// implement the `Clone` trait e.g. in Order to not complicate the logic keeping the metrics in
/// sync on drop. If someone adds a `#[derive(Clone)]` below, it is **wrong**.
pub struct Sender {
	inner: mpsc::UnboundedSender<Event>,
	name: &'static str,
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
			metrics.num_channels.with_label_values(&[self.name]).dec();
		}
	}
}

/// Receiving side of a channel.
pub struct Receiver {
	inner: mpsc::UnboundedReceiver<Event>,
	name: &'static str,
	/// Initially contains `None`, and will be set to a value once the corresponding [`Sender`]
	/// is assigned to an instance of [`OutChannels`].
	metrics: Arc<Mutex<Option<Arc<Option<Metrics>>>>>,
}

impl Stream for Receiver {
	type Item = Event;

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Event>> {
		if let Some(ev) = ready!(Pin::new(&mut self.inner).poll_next(cx)) {
			let metrics = self.metrics.lock().clone();
			match metrics.as_ref().map(|m| m.as_ref()) {
				Some(Some(metrics)) => metrics.event_out(&ev, self.name),
				Some(None) => (), // no registry
				None => log::warn!(
					"Inconsistency in out_events: event happened before sender associated"
				),
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
		if !self.inner.is_terminated() {
			// Empty the list to properly decrease the metrics.
			while let Some(Some(_)) = self.next().now_or_never() {}
		}
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
	pub fn new(registry: Option<&Registry>) -> Result<Self, PrometheusError> {
		let metrics =
			if let Some(registry) = registry { Some(Metrics::register(registry)?) } else { None };

		Ok(Self { event_streams: Vec::new(), metrics: Arc::new(metrics) })
	}

	/// Adds a new [`Sender`] to the collection.
	pub fn push(&mut self, sender: Sender) {
		let mut metrics = sender.metrics.lock();
		debug_assert!(metrics.is_none());
		*metrics = Some(self.metrics.clone());
		drop(metrics);

		if let Some(metrics) = &*self.metrics {
			metrics.num_channels.with_label_values(&[sender.name]).inc();
		}

		self.event_streams.push(sender);
	}

	/// Sends an event.
	pub fn send(&mut self, event: Event) {
		self.event_streams
			.retain(|sender| sender.inner.unbounded_send(event.clone()).is_ok());

		if let Some(metrics) = &*self.metrics {
			for ev in &self.event_streams {
				metrics.event_in(&event, 1, ev.name);
			}
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

struct Metrics {
	// This list is ordered alphabetically
	events_total: CounterVec<U64>,
	notifications_sizes: CounterVec<U64>,
	num_channels: GaugeVec<U64>,
}

thread_local! {
	static LABEL_BUFFER: RefCell<String> = RefCell::new(String::new());
}

fn format_label(prefix: &str, protocol: &str, callback: impl FnOnce(&str)) {
	LABEL_BUFFER.with(|label_buffer| {
		let mut label_buffer = label_buffer.borrow_mut();
		label_buffer.clear();
		label_buffer.reserve(prefix.len() + protocol.len() + 2);
		label_buffer.push_str(prefix);
		label_buffer.push('"');
		label_buffer.push_str(protocol);
		label_buffer.push('"');
		callback(&label_buffer);
	});
}

impl Metrics {
	fn register(registry: &Registry) -> Result<Self, PrometheusError> {
		Ok(Self {
			events_total: register(CounterVec::new(
				Opts::new(
					"substrate_sub_libp2p_out_events_events_total",
					"Number of broadcast network events that have been sent or received across all \
					 channels"
				),
				&["event_name", "action", "name"]
			)?, registry)?,
			notifications_sizes: register(CounterVec::new(
				Opts::new(
					"substrate_sub_libp2p_out_events_notifications_sizes",
					"Size of notification events that have been sent or received across all \
					 channels"
				),
				&["protocol", "action", "name"]
			)?, registry)?,
			num_channels: register(GaugeVec::new(
				Opts::new(
					"substrate_sub_libp2p_out_events_num_channels",
					"Number of internal active channels that broadcast network events",
				),
				&["name"]
			)?, registry)?,
		})
	}

	fn event_in(&self, event: &Event, num: u64, name: &str) {
		match event {
			Event::Dht(_) => {
				self.events_total.with_label_values(&["dht", "sent", name]).inc_by(num);
			},
			Event::SyncConnected { .. } => {
				self.events_total
					.with_label_values(&["sync-connected", "sent", name])
					.inc_by(num);
			},
			Event::SyncDisconnected { .. } => {
				self.events_total
					.with_label_values(&["sync-disconnected", "sent", name])
					.inc_by(num);
			},
			Event::NotificationStreamOpened { protocol, .. } => {
				format_label("notif-open-", protocol, |protocol_label| {
					self.events_total
						.with_label_values(&[protocol_label, "sent", name])
						.inc_by(num);
				});
			},
			Event::NotificationStreamClosed { protocol, .. } => {
				format_label("notif-closed-", protocol, |protocol_label| {
					self.events_total
						.with_label_values(&[protocol_label, "sent", name])
						.inc_by(num);
				});
			},
			Event::NotificationsReceived { messages, .. } =>
				for (protocol, message) in messages {
					format_label("notif-", protocol, |protocol_label| {
						self.events_total
							.with_label_values(&[protocol_label, "sent", name])
							.inc_by(num);
					});
					self.notifications_sizes.with_label_values(&[protocol, "sent", name]).inc_by(
						num.saturating_mul(u64::try_from(message.len()).unwrap_or(u64::MAX)),
					);
				},
		}
	}

	fn event_out(&self, event: &Event, name: &str) {
		match event {
			Event::Dht(_) => {
				self.events_total.with_label_values(&["dht", "received", name]).inc();
			},
			Event::SyncConnected { .. } => {
				self.events_total.with_label_values(&["sync-connected", "received", name]).inc();
			},
			Event::SyncDisconnected { .. } => {
				self.events_total
					.with_label_values(&["sync-disconnected", "received", name])
					.inc();
			},
			Event::NotificationStreamOpened { protocol, .. } => {
				format_label("notif-open-", protocol, |protocol_label| {
					self.events_total.with_label_values(&[protocol_label, "received", name]).inc();
				});
			},
			Event::NotificationStreamClosed { protocol, .. } => {
				format_label("notif-closed-", protocol, |protocol_label| {
					self.events_total.with_label_values(&[protocol_label, "received", name]).inc();
				});
			},
			Event::NotificationsReceived { messages, .. } =>
				for (protocol, message) in messages {
					format_label("notif-", protocol, |protocol_label| {
						self.events_total
							.with_label_values(&[protocol_label, "received", name])
							.inc();
					});
					self.notifications_sizes
						.with_label_values(&[protocol, "received", name])
						.inc_by(u64::try_from(message.len()).unwrap_or(u64::MAX));
				},
		}
	}
}
