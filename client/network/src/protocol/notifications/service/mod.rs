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

//! Notification service implementation.

use crate::{
	error,
	protocol::notifications::handler::NotificationsSink,
	service::traits::{
		Direction, MessageSink, NotificationEvent, NotificationService, ValidationResult,
	},
	types::ProtocolName,
};

use futures::{
	stream::{FuturesUnordered, Stream},
	StreamExt,
};
use libp2p::PeerId;
use parking_lot::Mutex;
use tokio::sync::{mpsc, oneshot};
use tokio_stream::wrappers::ReceiverStream;

use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};

use std::{collections::HashMap, fmt::Debug, sync::Arc};

pub(crate) mod metrics;
#[cfg(test)]
mod tests;

/// Logging target for the file.
const LOG_TARGET: &str = "notification-service";

/// Default command queue size.
const COMMAND_QUEUE_SIZE: usize = 64;

/// Type representing subscribers of a notification protocol.
type Subscribers = Arc<Mutex<Vec<TracingUnboundedSender<InnerNotificationEvent>>>>;

/// Type represending a distributable message sink.
///
/// See documentation for [`PeerContext`] for more details.
type NotificationSink = Arc<Mutex<NotificationsSink>>;

#[async_trait::async_trait]
impl MessageSink for NotificationSink {
	/// Send synchronous `notification` to the peer associated with this [`MessageSink`].
	fn send_sync_notification(&self, notification: Vec<u8>) {
		self.lock().send_sync_notification(notification);
	}

	/// Send an asynchronous `notification` to to the peer associated with this [`MessageSink`],
	/// allowing sender to exercise backpressure.
	///
	/// Returns an error if the peer does not exist.
	async fn send_async_notification(&self, notification: Vec<u8>) -> Result<(), error::Error> {
		// notification sink must be cloned because the lock cannot be held across `.await`
		// this makes the implementation less efficient but not prohibitively so as the same
		// method is also used by `NetworkService` when sending notifications.
		let sink = self.lock().clone();
		let sink = sink.reserve_notification().await.map_err(|_| error::Error::ConnectionClosed)?;
		sink.send(notification).map_err(|_| error::Error::ChannelClosed)
	}
}

/// Inner notification event to deal with `NotificationsSinks` without exposing that
/// implementation detail to [`NotificationService`] consumers.
#[derive(Debug)]
enum InnerNotificationEvent {
	/// Validate inbound substream.
	ValidateInboundSubstream {
		/// Peer ID.
		peer: PeerId,

		/// Received handshake.
		handshake: Vec<u8>,

		/// `oneshot::Sender` for sending validation result back to `Notifications`
		result_tx: oneshot::Sender<ValidationResult>,
	},

	/// Notification substream open to `peer`.
	NotificationStreamOpened {
		/// Peer ID.
		peer: PeerId,

		/// Direction of the substream.
		direction: Direction,

		/// Received handshake.
		handshake: Vec<u8>,

		/// Negotiated fallback.
		negotiated_fallback: Option<ProtocolName>,

		/// Notification sink.
		sink: NotificationsSink,
	},

	/// Substream was closed.
	NotificationStreamClosed {
		/// Peer ID.
		peer: PeerId,
	},

	/// Notification was received from the substream.
	NotificationReceived {
		/// Peer ID.
		peer: PeerId,

		/// Received notification.
		notification: Vec<u8>,
	},

	/// Notification sink has been replaced.
	NotificationSinkReplaced {
		/// Peer ID.
		peer: PeerId,

		/// Notification sink.
		sink: NotificationsSink,
	},
}

/// Notification commands.
///
/// Sent by the installed protocols to `Notifications` to open/close/modify substreams.
#[derive(Debug)]
pub enum NotificationCommand {
	/// Instruct `Notifications` to open a substream to peer.
	OpenSubstream(PeerId),

	/// Instruct `Notifications` to close the substream to peer.
	CloseSubstream(PeerId),

	/// Set handshake for the notifications protocol.
	SetHandshake(Vec<u8>),
}

/// Context assigned to each peer.
///
/// Contains `NotificationsSink` used by [`NotificationService`] to send notifications
/// and an additional, distributable `NotificationsSink` which the protocol may acquire
/// if it wishes to send notifications through `NotificationsSink` directly.
///
/// The distributable `NoticationsSink` is wrapped in an `Arc<Mutex<>>` to allow
/// `NotificationsService` to swap the underlying sink in case it's replaced.
#[derive(Debug, Clone)]
struct PeerContext {
	/// Sink for sending notificaitons.
	sink: NotificationsSink,

	/// Distributable notification sink.
	shared_sink: NotificationSink,
}

/// Handle that is passed on to the notifications protocol.
#[derive(Debug)]
pub struct NotificationHandle {
	/// Protocol name.
	protocol: ProtocolName,

	/// TX channel for sending commands to `Notifications`.
	tx: mpsc::Sender<NotificationCommand>,

	/// RX channel for receiving events from `Notifications`.
	rx: TracingUnboundedReceiver<InnerNotificationEvent>,

	/// All subscribers of `NotificationEvent`s.
	subscribers: Subscribers,

	/// Connected peers.
	peers: HashMap<PeerId, PeerContext>,
}

impl NotificationHandle {
	/// Create new [`NotificationHandle`].
	fn new(
		protocol: ProtocolName,
		tx: mpsc::Sender<NotificationCommand>,
		rx: TracingUnboundedReceiver<InnerNotificationEvent>,
		subscribers: Arc<Mutex<Vec<TracingUnboundedSender<InnerNotificationEvent>>>>,
	) -> Self {
		Self { protocol, tx, rx, subscribers, peers: HashMap::new() }
	}
}

#[async_trait::async_trait]
impl NotificationService for NotificationHandle {
	/// Instruct `Notifications` to open a new substream for `peer`.
	async fn open_substream(&mut self, _peer: PeerId) -> Result<(), ()> {
		todo!("support for opening substreams not implemented yet");
	}

	/// Instruct `Notifications` to close substream for `peer`.
	async fn close_substream(&mut self, _peer: PeerId) -> Result<(), ()> {
		todo!("support for closing substreams not implemented yet, call `NetworkService::disconnect_peer()` instead");
	}

	/// Send synchronous `notification` to `peer`.
	fn send_sync_notification(&self, peer: &PeerId, notification: Vec<u8>) {
		log::trace!(target: LOG_TARGET, "{}: send sync notification to {peer:?}", self.protocol);

		if let Some(info) = self.peers.get(&peer) {
			let _ = info.sink.send_sync_notification(notification);
		}
	}

	/// Send asynchronous `notification` to `peer`, allowing sender to exercise backpressure.
	async fn send_async_notification(
		&self,
		peer: &PeerId,
		notification: Vec<u8>,
	) -> Result<(), error::Error> {
		log::trace!(target: LOG_TARGET, "{}: send async notification to {peer:?}", self.protocol);

		self.peers
			.get(&peer)
			.ok_or_else(|| error::Error::PeerDoesntExist(*peer))?
			.sink
			.reserve_notification()
			.await
			.map_err(|_| error::Error::ConnectionClosed)?
			.send(notification)
			.map_err(|_| error::Error::ChannelClosed)
	}

	/// Set handshake for the notification protocol replacing the old handshake.
	async fn set_handshake(&mut self, handshake: Vec<u8>) -> Result<(), ()> {
		log::trace!(target: LOG_TARGET, "{}: set handshake to {handshake:?}", self.protocol);

		self.tx.send(NotificationCommand::SetHandshake(handshake)).await.map_err(|_| ())
	}

	/// Get next event from the `Notifications` event stream.
	async fn next_event(&mut self) -> Option<NotificationEvent> {
		loop {
			match self.rx.next().await? {
				InnerNotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx } =>
					return Some(NotificationEvent::ValidateInboundSubstream {
						peer,
						handshake,
						result_tx,
					}),
				InnerNotificationEvent::NotificationStreamOpened {
					peer,
					handshake,
					negotiated_fallback,
					direction,
					sink,
				} => {
					self.peers.insert(
						peer,
						PeerContext { sink: sink.clone(), shared_sink: Arc::new(Mutex::new(sink)) },
					);
					return Some(NotificationEvent::NotificationStreamOpened {
						peer,
						handshake,
						direction,
						negotiated_fallback,
					})
				},
				InnerNotificationEvent::NotificationStreamClosed { peer } => {
					self.peers.remove(&peer);
					return Some(NotificationEvent::NotificationStreamClosed { peer })
				},
				InnerNotificationEvent::NotificationReceived { peer, notification } =>
					return Some(NotificationEvent::NotificationReceived { peer, notification }),
				InnerNotificationEvent::NotificationSinkReplaced { peer, sink } => {
					match self.peers.get_mut(&peer) {
						None => log::error!(
							"{}: notification sink replaced for {peer} but peer does not exist",
							self.protocol
						),
						Some(context) => {
							context.sink = sink.clone();
							*context.shared_sink.lock() = sink.clone();
						},
					}
				},
			}
		}
	}

	// Clone [`NotificationService`]
	fn clone(&mut self) -> Result<Box<dyn NotificationService>, ()> {
		let mut subscribers = self.subscribers.lock();
		let (event_tx, event_rx) = tracing_unbounded("mpsc-notification-to-protocol", 100_000);
		subscribers.push(event_tx);

		Ok(Box::new(NotificationHandle {
			protocol: self.protocol.clone(),
			tx: self.tx.clone(),
			rx: event_rx,
			peers: self.peers.clone(),
			subscribers: self.subscribers.clone(),
		}))
	}

	/// Get protocol name.
	fn protocol(&self) -> &ProtocolName {
		&self.protocol
	}

	/// Get message sink of the peer.
	fn message_sink(&self, peer: &PeerId) -> Option<Box<dyn MessageSink>> {
		match self.peers.get(peer) {
			Some(context) => Some(Box::new(context.shared_sink.clone())),
			None => None,
		}
	}
}

/// Channel pair which allows `Notifications` to interact with a protocol.
#[derive(Debug)]
pub struct ProtocolHandlePair {
	/// Protocol name.
	protocol: ProtocolName,

	/// Subscribers of the notification protocol events.
	subscribers: Subscribers,

	// Receiver for notification commands received from the protocol implementation.
	rx: mpsc::Receiver<NotificationCommand>,
}

impl ProtocolHandlePair {
	/// Create new [`ProtocolHandlePair`].
	fn new(
		protocol: ProtocolName,
		subscribers: Subscribers,
		rx: mpsc::Receiver<NotificationCommand>,
	) -> Self {
		Self { protocol, subscribers, rx }
	}

	/// Consume `self` and split [`ProtocolHandlePair`] into a handle which allows it to send events
	/// to the protocol and a stream of commands received from the protocol.
	pub fn split(
		self,
	) -> (ProtocolHandle, Box<dyn Stream<Item = NotificationCommand> + Send + Unpin>) {
		(
			ProtocolHandle::new(self.protocol, self.subscribers),
			Box::new(ReceiverStream::new(self.rx)),
		)
	}
}

/// Handle that is passed on to `Notifications` and allows it to directly communicate
/// with the protocol.
#[derive(Debug)]
pub struct ProtocolHandle {
	/// Protocol name.
	protocol: ProtocolName,

	/// Subscribers of the notification protocol.
	subscribers: Subscribers,

	/// Number of connected peers.
	num_peers: usize,

	/// Prometheus metrics.
	metrics: Option<metrics::Metrics>,
}

impl ProtocolHandle {
	/// Create new [`ProtocolHandle`].
	fn new(protocol: ProtocolName, subscribers: Subscribers) -> Self {
		Self { protocol, subscribers, num_peers: 0usize, metrics: None }
	}

	/// Set metrics.
	pub fn set_metrics(&mut self, metrics: Option<metrics::Metrics>) {
		self.metrics = metrics;
	}

	/// Report to the protocol that a substream has been opened and it must be validated by the
	/// protocol.
	///
	/// Return `oneshot::Receiver` which allows `Notifications` to poll for the validation result
	/// from protocol.
	pub fn report_incoming_substream(
		&self,
		peer: PeerId,
		handshake: Vec<u8>,
	) -> Result<oneshot::Receiver<ValidationResult>, ()> {
		let subscribers = self.subscribers.lock();

		log::trace!(
			target: LOG_TARGET,
			"{}: report incoming substream for {peer}, handshake {handshake:?}",
			self.protocol
		);

		// if there is only one subscriber, `Notifications` can wait directly on the
		// `oneshot::channel()`'s RX half without indirection
		if subscribers.len() == 1 {
			let (result_tx, rx) = oneshot::channel();
			return subscribers[0]
				.unbounded_send(InnerNotificationEvent::ValidateInboundSubstream {
					peer,
					handshake,
					result_tx,
				})
				.map(|_| rx)
				.map_err(|_| ())
		}

		// if there are multiple subscribers, create a task which waits for all of the
		// validations to finish and returns the combined result to `Notifications`
		let mut results: FuturesUnordered<_> = subscribers
			.iter()
			.filter_map(|subscriber| {
				let (result_tx, rx) = oneshot::channel();

				subscriber
					.unbounded_send(InnerNotificationEvent::ValidateInboundSubstream {
						peer,
						handshake: handshake.clone(),
						result_tx,
					})
					.is_ok()
					.then_some(rx)
			})
			.collect();

		let (tx, rx) = oneshot::channel();
		tokio::spawn(async move {
			while let Some(event) = results.next().await {
				match event {
					Err(_) | Ok(ValidationResult::Reject) =>
						return tx.send(ValidationResult::Reject),
					Ok(ValidationResult::Accept) => {},
				}
			}

			return tx.send(ValidationResult::Accept)
		});

		Ok(rx)
	}

	/// Report to the protocol that a substream has been opened and that it can now use the handle
	/// to send notifications to the remote peer.
	pub fn report_substream_opened(
		&mut self,
		peer: PeerId,
		direction: Direction,
		handshake: Vec<u8>,
		negotiated_fallback: Option<ProtocolName>,
		sink: NotificationsSink,
	) -> Result<(), ()> {
		metrics::register_substream_opened(&self.metrics, &self.protocol);

		let mut subscribers = self.subscribers.lock();
		log::trace!(target: LOG_TARGET, "{}: substream opened for {peer:?}", self.protocol);

		subscribers.retain(|subscriber| {
			subscriber
				.unbounded_send(InnerNotificationEvent::NotificationStreamOpened {
					peer,
					direction,
					handshake: handshake.clone(),
					negotiated_fallback: negotiated_fallback.clone(),
					sink: sink.clone(),
				})
				.is_ok()
		});
		self.num_peers += 1;

		Ok(())
	}

	/// Substream was closed.
	pub fn report_substream_closed(&mut self, peer: PeerId) -> Result<(), ()> {
		metrics::register_substream_closed(&self.metrics, &self.protocol);

		let mut subscribers = self.subscribers.lock();
		log::trace!(target: LOG_TARGET, "{}: substream closed for {peer:?}", self.protocol);

		subscribers.retain(|subscriber| {
			subscriber
				.unbounded_send(InnerNotificationEvent::NotificationStreamClosed { peer })
				.is_ok()
		});
		self.num_peers -= 1;

		Ok(())
	}

	/// Notification was received from the substream.
	pub fn report_notification_received(
		&mut self,
		peer: PeerId,
		notification: Vec<u8>,
	) -> Result<(), ()> {
		metrics::register_notification_received(&self.metrics, &self.protocol, notification.len());

		let mut subscribers = self.subscribers.lock();
		log::trace!(target: LOG_TARGET, "{}: notification received from {peer:?}", self.protocol);

		subscribers.retain(|subscriber| {
			subscriber
				.unbounded_send(InnerNotificationEvent::NotificationReceived {
					peer,
					notification: notification.clone(),
				})
				.is_ok()
		});

		Ok(())
	}

	/// Notification sink was replaced.
	pub fn report_notification_sink_replaced(
		&mut self,
		peer: PeerId,
		sink: NotificationsSink,
	) -> Result<(), ()> {
		let mut subscribers = self.subscribers.lock();

		log::trace!(
			target: LOG_TARGET,
			"{}: notification sink replaced for {peer:?}",
			self.protocol
		);

		subscribers.retain(|subscriber| {
			subscriber
				.unbounded_send(InnerNotificationEvent::NotificationSinkReplaced {
					peer,
					sink: sink.clone(),
				})
				.is_ok()
		});

		Ok(())
	}

	/// Get the number of connected peers.
	pub fn num_peers(&self) -> usize {
		self.num_peers
	}
}

/// Create new (protocol, notification) handle pair.
///
/// Handle pair allows `Notifications` and the protocol to communicate with each other directly.
pub fn notification_service(
	protocol: ProtocolName,
) -> (ProtocolHandlePair, Box<dyn NotificationService>) {
	let (cmd_tx, cmd_rx) = mpsc::channel(COMMAND_QUEUE_SIZE);
	let (event_tx, event_rx) = tracing_unbounded("mpsc-notification-to-protocol", 100_000);
	let subscribers = Arc::new(Mutex::new(vec![event_tx]));

	(
		ProtocolHandlePair::new(protocol.clone(), subscribers.clone(), cmd_rx),
		Box::new(NotificationHandle::new(protocol.clone(), cmd_tx, event_rx, subscribers)),
	)
}
