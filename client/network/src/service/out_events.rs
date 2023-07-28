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

use crate::event::Event;

use futures::{prelude::*, ready, stream::FusedStream};
use log::{debug, error};
use prometheus_endpoint::{register, CounterVec, GaugeVec, Opts, PrometheusError, Registry, U64};
use std::{
	backtrace::Backtrace,
	cell::RefCell,
	fmt,
	pin::Pin,
	task::{Context, Poll},
};

/// Log target for this file.
pub const LOG_TARGET: &str = "sub-libp2p::out_events";

/// Creates a new channel that can be associated to a [`OutChannels`].
///
/// The name is used in Prometheus reports, the queue size threshold is used
/// to warn if there are too many unprocessed events in the channel.
pub fn channel(name: &'static str, queue_size_warning: usize) -> (Sender, Receiver) {
	let (tx, rx) = async_channel::unbounded();
	let tx = Sender {
		inner: tx,
		name,
		queue_size_warning,
		warning_fired: SenderWarningState::NotFired,
		creation_backtrace: Backtrace::force_capture(),
		metrics: None,
	};
	let rx = Receiver { inner: rx, name, metrics: None };
	(tx, rx)
}

/// A state of a sender warning that is used to avoid spamming the logs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SenderWarningState {
	/// The warning has not been fired yet.
	NotFired,
	/// The warning has been fired, and the channel is full
	FiredFull,
	/// The warning has been fired and the channel is not full anymore.
	FiredFree,
}

/// Sending side of a channel.
///
/// Must be associated with an [`OutChannels`] before anything can be sent on it
///
/// > **Note**: Contrary to regular channels, this `Sender` is purposefully designed to not
/// implement the `Clone` trait e.g. in Order to not complicate the logic keeping the metrics in
/// sync on drop. If someone adds a `#[derive(Clone)]` below, it is **wrong**.
pub struct Sender {
	inner: async_channel::Sender<Event>,
	/// Name to identify the channel (e.g., in Prometheus and logs).
	name: &'static str,
	/// Threshold queue size to generate an error message in the logs.
	queue_size_warning: usize,
	/// We generate the error message only once to not spam the logs after the first error.
	/// Subsequently we indicate channel fullness on debug level.
	warning_fired: SenderWarningState,
	/// Backtrace of a place where the channel was created.
	creation_backtrace: Backtrace,
	/// Clone of [`Receiver::metrics`]. Will be initialized when [`Sender`] is added to
	/// [`OutChannels`] with `OutChannels::push()`.
	metrics: Option<Metrics>,
}

impl fmt::Debug for Sender {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_tuple("Sender").finish()
	}
}

impl Drop for Sender {
	fn drop(&mut self) {
		if let Some(metrics) = self.metrics.as_ref() {
			metrics.num_channels.with_label_values(&[self.name]).dec();
		}
	}
}

/// Receiving side of a channel.
pub struct Receiver {
	inner: async_channel::Receiver<Event>,
	name: &'static str,
	/// Initially contains `None`, and will be set to a value once the corresponding [`Sender`]
	/// is assigned to an instance of [`OutChannels`].
	metrics: Option<Metrics>,
}

impl Stream for Receiver {
	type Item = Event;

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Event>> {
		if let Some(ev) = ready!(Pin::new(&mut self.inner).poll_next(cx)) {
			if let Some(metrics) = &self.metrics {
				metrics.event_out(&ev, self.name);
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
	metrics: Option<Metrics>,
}

impl OutChannels {
	/// Creates a new empty collection of senders.
	pub fn new(registry: Option<&Registry>) -> Result<Self, PrometheusError> {
		let metrics =
			if let Some(registry) = registry { Some(Metrics::register(registry)?) } else { None };

		Ok(Self { event_streams: Vec::new(), metrics })
	}

	/// Adds a new [`Sender`] to the collection.
	pub fn push(&mut self, mut sender: Sender) {
		debug_assert!(sender.metrics.is_none());
		sender.metrics = self.metrics.clone();

		if let Some(metrics) = &self.metrics {
			metrics.num_channels.with_label_values(&[sender.name]).inc();
		}

		self.event_streams.push(sender);
	}

	/// Sends an event.
	pub fn send(&mut self, event: Event) {
		self.event_streams.retain_mut(|sender| {
			let current_pending = sender.inner.len();
			if current_pending >= sender.queue_size_warning {
				if sender.warning_fired == SenderWarningState::NotFired {
					error!(
						"The number of unprocessed events in channel `{}` exceeded {}.\n\
						 The channel was created at:\n{:}\n
						 The last event was sent from:\n{:}",
						sender.name,
						sender.queue_size_warning,
						sender.creation_backtrace,
						Backtrace::force_capture(),
					);
				} else if sender.warning_fired == SenderWarningState::FiredFree {
					// We don't want to spam the logs, so we only log on debug level
					debug!(
						target: LOG_TARGET,
						"Channel `{}` is overflowed again. Number of events: {}",
						sender.name, current_pending
					);
				}
				sender.warning_fired = SenderWarningState::FiredFull;
			} else if sender.warning_fired == SenderWarningState::FiredFull &&
				current_pending < sender.queue_size_warning.wrapping_div(2)
			{
				sender.warning_fired = SenderWarningState::FiredFree;
				debug!(
					target: LOG_TARGET,
					"Channel `{}` is no longer overflowed. Number of events: {}",
					sender.name, current_pending
				);
			}

			sender.inner.try_send(event.clone()).is_ok()
		});

		if let Some(metrics) = &self.metrics {
			for ev in &self.event_streams {
				metrics.event_in(&event, ev.name);
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

#[derive(Clone)]
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

	fn event_in(&self, event: &Event, name: &str) {
		match event {
			Event::Dht(_) => {
				self.events_total.with_label_values(&["dht", "sent", name]).inc();
			},
			Event::NotificationStreamOpened { protocol, .. } => {
				format_label("notif-open-", protocol, |protocol_label| {
					self.events_total.with_label_values(&[protocol_label, "sent", name]).inc();
				});
			},
			Event::NotificationStreamClosed { protocol, .. } => {
				format_label("notif-closed-", protocol, |protocol_label| {
					self.events_total.with_label_values(&[protocol_label, "sent", name]).inc();
				});
			},
			Event::NotificationsReceived { messages, .. } =>
				for (protocol, message) in messages {
					format_label("notif-", protocol, |protocol_label| {
						self.events_total.with_label_values(&[protocol_label, "sent", name]).inc();
					});
					self.notifications_sizes
						.with_label_values(&[protocol, "sent", name])
						.inc_by(u64::try_from(message.len()).unwrap_or(u64::MAX));
				},
		}
	}

	fn event_out(&self, event: &Event, name: &str) {
		match event {
			Event::Dht(_) => {
				self.events_total.with_label_values(&["dht", "received", name]).inc();
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
