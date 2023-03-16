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

#![allow(unused)]

use crate::{
	error,
	protocol::notifications::handler::{
		NotificationsSink, NotificationsSinkMessage, ASYNC_NOTIFICATIONS_BUFFER_SIZE,
	},
	service::traits::{NotificationEvent, NotificationService, ValidationResult},
	types::ProtocolName,
};

use futures::{stream::Stream, SinkExt, StreamExt};
use libp2p::PeerId;
use tokio::sync::{mpsc, oneshot};

use sc_network_common::role::ObservedRole;

use std::{collections::HashMap, fmt::Debug};

/// Inner notification event to deal with `NotificationsSinks` without exposing that
/// implementation detail to [`NotificationService`] consumers.
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

	/// Remote identified by `PeerId` opened a substream and sent `Handshake`.
	/// Validate `Handshake` and report status (accept/reject) to `Notifications`.
	NotificationStreamOpened {
		/// Peer ID.
		peer: PeerId,

		/// Role of the peer.
		role: ObservedRole,

		/// Negotiated fallback.
		negotiated_fallback: Option<ProtocolName>,

		/// Notification sink.
		sink: NotificationsSink,
	},

	/// Substream was closed.
	NotificationStreamClosed {
		/// Peer Id.
		peer: PeerId,
	},

	/// Notification was received from the substream.
	NotificationReceived {
		/// Peer ID.
		peer: PeerId,

		/// Received notification.
		notification: Vec<u8>,
	},
}

/// Notification commands.
///
/// Commands sent by the notifications protocol to `Notifications`
/// in order to modify connectivity state and communicate with the remote peer.
pub enum NotificationCommand {
	/// Instruct `Notifications` to open a substream to peer.
	OpenSubstream(PeerId),

	/// Instruct `Notifications` to close the substream to peer.
	CloseSubstream(PeerId),

	/// Send notification to peer.
	SendNotification(PeerId, Vec<u8>),

	/// Set handshake for the notifications protocol.
	SetHandshake(Vec<u8>),
}

/// Handle that is passed on to the notifications protocol.
#[derive(Debug)]
pub struct NotificationHandle {
	/// TX channel for sending commands to `Notifications`.
	tx: mpsc::Sender<NotificationCommand>,

	/// RX channel for receiving events from `Notifications`.
	rx: mpsc::Receiver<InnerNotificationEvent>,

	/// Connected peers.
	peers: HashMap<PeerId, NotificationsSink>,
}

impl NotificationHandle {
	/// Create new [`NotificationHandle`].
	fn new(
		tx: mpsc::Sender<NotificationCommand>,
		rx: mpsc::Receiver<InnerNotificationEvent>,
	) -> Self {
		Self { tx, rx, peers: HashMap::new() }
	}
}

#[async_trait::async_trait]
impl NotificationService for NotificationHandle {
	/// Instruct `Notifications` to open a new substream for `peer`.
	async fn open_substream(&mut self, peer: PeerId) -> Result<(), ()> {
		todo!("support for opening substreams not implemented yet");
	}

	/// Instruct `Notifications` to close substream for `peer`.
	async fn close_substream(&mut self, peer: PeerId) -> Result<(), ()> {
		todo!("support for closing substreams not implemented yet");
	}

	/// Send synchronous `notification` to `peer`.
	fn send_sync_notification(
		&self,
		peer: &PeerId,
		notification: Vec<u8>,
	) -> Result<(), error::Error> {
		self.peers
			.get(&peer)
			.ok_or_else(|| error::Error::PeerDoesntExist(*peer))?
			.send_sync_notification(notification);
		Ok(())
	}

	/// Send asynchronous `notification` to `peer`, allowing sender to exercise backpressure.
	async fn send_async_notification(
		&self,
		peer: &PeerId,
		notification: Vec<u8>,
	) -> Result<(), error::Error> {
		self.peers
			.get(&peer)
			.ok_or_else(|| error::Error::PeerDoesntExist(*peer))?
			.reserve_notification()
			.await
			.map_err(|_| error::Error::ConnectionClosed)?
			.send(notification)
			.map_err(|_| error::Error::ChannelClosed)
	}

	/// Set handshake for the notification protocol replacing the old handshake.
	async fn set_hanshake(&mut self, handshake: Vec<u8>) -> Result<(), ()> {
		self.tx.send(NotificationCommand::SetHandshake(handshake)).await.map_err(|_| ())
	}

	/// Get next event from the `Notifications` event stream.
	async fn next_event(&mut self) -> Option<NotificationEvent> {
		match self.rx.recv().await? {
			InnerNotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx } =>
				Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }),
			InnerNotificationEvent::NotificationStreamOpened {
				peer,
				role,
				negotiated_fallback,
				sink,
			} => {
				self.peers.insert(peer, sink);
				Some(NotificationEvent::NotificationStreamOpened {
					peer,
					role,
					negotiated_fallback,
				})
			},
			InnerNotificationEvent::NotificationStreamClosed { peer } => {
				self.peers.remove(&peer);
				Some(NotificationEvent::NotificationStreamClosed { peer })
			},
			InnerNotificationEvent::NotificationReceived { peer, notification } =>
				Some(NotificationEvent::NotificationReceived { peer, notification }),
		}
	}
}

/// Channel pair which allows `Notifications` to interact with a protocol.
#[derive(Debug)]
pub struct ProtocolHandlePair(
	mpsc::Sender<InnerNotificationEvent>,
	mpsc::Receiver<NotificationCommand>,
);

impl ProtocolHandlePair {
	/// Create new [`ProtocolHandlePair`].
	fn new(
		tx: mpsc::Sender<InnerNotificationEvent>,
		rx: mpsc::Receiver<NotificationCommand>,
	) -> Self {
		Self(tx, rx)
	}

	/// Split [`ProtocolHandlePair`] into a handle which allows it to send events to the protocol
	/// into a stream of commands received from the protocol.
	pub fn split(self) -> (ProtocolHandle, Box<dyn Stream<Item = NotificationCommand> + Send>) {
		(ProtocolHandle::new(self.0), Box::new(tokio_stream::wrappers::ReceiverStream::new(self.1)))
	}
}

/// Handle that is passed on to `Notifications` and allows it to directly communicate
/// with the protocol.
#[derive(Debug)]
pub struct ProtocolHandle {
	/// TX channel for sending events to protocol.
	tx: mpsc::Sender<InnerNotificationEvent>,
}

impl ProtocolHandle {
	fn new(tx: mpsc::Sender<InnerNotificationEvent>) -> Self {
		Self { tx }
	}

	/// Report to the protocol that a substream has been opened and it must be validated by the
	/// protocol.
	///
	/// Return `oneshot::Receiver` which allows `Notifications` to poll for the validation result
	/// from protocol.
	async fn report_incoming_substream(
		&self,
		peer: PeerId,
		handshake: Vec<u8>,
	) -> Result<oneshot::Receiver<ValidationResult>, ()> {
		let (result_tx, rx) = oneshot::channel();

		self.tx
			.send(InnerNotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx })
			.await
			.map(|_| rx)
			.map_err(|_| ())
	}

	/// Report to the protocol that a substream has been opened and that it can now use the handle
	/// to send notifications to the remote peer.
	async fn report_substream_opened(
		&self,
		peer: PeerId,
		role: ObservedRole,
		negotiated_fallback: Option<ProtocolName>,
		sink: NotificationsSink,
	) -> Result<(), ()> {
		self.tx
			.send(InnerNotificationEvent::NotificationStreamOpened {
				peer,
				role,
				negotiated_fallback,
				sink,
			})
			.await
			.map_err(|_| ())
	}

	/// Substream was closed.
	async fn report_substream_closed(&mut self, peer: PeerId) -> Result<(), ()> {
		self.tx
			.send(InnerNotificationEvent::NotificationStreamClosed { peer })
			.await
			.map_err(|_| ())
	}

	/// Notification was received from the substream.
	async fn report_notification_received(
		&mut self,
		peer: PeerId,
		notification: Vec<u8>,
	) -> Result<(), ()> {
		self.tx
			.send(InnerNotificationEvent::NotificationReceived { peer, notification })
			.await
			.map_err(|_| ())
	}
}

/// Create new (protocol, notification) handle pair.
///
/// Handle pair allows `Notifications` and the protocol to communicate with each other directly.
pub fn notification_service() -> (ProtocolHandlePair, Box<dyn NotificationService>) {
	let (cmd_tx, cmd_rx) = mpsc::channel(64); // TODO: zzz
	let (event_tx, event_rx) = mpsc::channel(64); // TODO: zzz

	(ProtocolHandlePair::new(event_tx, cmd_rx), Box::new(NotificationHandle::new(cmd_tx, event_rx)))
}

#[cfg(test)]
mod tests {
	use super::*;
	use futures::prelude::*;

	#[tokio::test]
	async fn validate_and_accept_substream() {
		let (proto, mut notif) = notification_service();
		let (mut handle, stream) = proto.split();

		let peer_id = PeerId::random();
		let rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).await.unwrap();

		if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
			notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(handshake, vec![1, 3, 3, 7]);
			result_tx.send(ValidationResult::Accept);
		} else {
			panic!("invalid event received");
		}

		assert_eq!(rx.await.unwrap(), ValidationResult::Accept);
	}

	#[tokio::test]
	async fn substream_opened() {
		let (proto, mut notif) = notification_service();
		let (sink, _, _) = NotificationsSink::new(PeerId::random());
		let (mut handle, stream) = proto.split();

		let peer_id = PeerId::random();
		handle
			.report_substream_opened(peer_id, ObservedRole::Full, None, sink)
			.await
			.unwrap();

		if let Some(NotificationEvent::NotificationStreamOpened {
			peer,
			role,
			negotiated_fallback,
		}) = notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(negotiated_fallback, None);
			assert_eq!(role, ObservedRole::Full);
		} else {
			panic!("invalid event received");
		}
	}

	#[tokio::test]
	async fn send_sync_notification() {
		let (proto, mut notif) = notification_service();
		let (sink, _, mut sync_rx) = NotificationsSink::new(PeerId::random());
		let (mut handle, stream) = proto.split();
		let peer_id = PeerId::random();

		// validate inbound substream
		let result_rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).await.unwrap();

		if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
			notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(handshake, vec![1, 3, 3, 7]);
			result_tx.send(ValidationResult::Accept);
		} else {
			panic!("invalid event received");
		}
		assert_eq!(result_rx.await.unwrap(), ValidationResult::Accept);

		// report that a substream has been opened
		handle
			.report_substream_opened(peer_id, ObservedRole::Full, None, sink)
			.await
			.unwrap();

		if let Some(NotificationEvent::NotificationStreamOpened {
			peer,
			role,
			negotiated_fallback,
		}) = notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(negotiated_fallback, None);
			assert_eq!(role, ObservedRole::Full);
		} else {
			panic!("invalid event received");
		}

		notif.send_sync_notification(&peer_id, vec![1, 3, 3, 8]);
		assert_eq!(
			sync_rx.next().await,
			Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 8] })
		);
	}

	#[tokio::test]
	async fn send_async_notification() {
		let (proto, mut notif) = notification_service();
		let (sink, mut async_rx, _) = NotificationsSink::new(PeerId::random());
		let (mut handle, stream) = proto.split();
		let peer_id = PeerId::random();

		// validate inbound substream
		let result_rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).await.unwrap();

		if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
			notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(handshake, vec![1, 3, 3, 7]);
			result_tx.send(ValidationResult::Accept);
		} else {
			panic!("invalid event received");
		}
		assert_eq!(result_rx.await.unwrap(), ValidationResult::Accept);

		// report that a substream has been opened
		handle
			.report_substream_opened(peer_id, ObservedRole::Full, None, sink)
			.await
			.unwrap();

		if let Some(NotificationEvent::NotificationStreamOpened {
			peer,
			role,
			negotiated_fallback,
		}) = notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(negotiated_fallback, None);
			assert_eq!(role, ObservedRole::Full);
		} else {
			panic!("invalid event received");
		}

		notif.send_async_notification(&peer_id, vec![1, 3, 3, 9]).await.unwrap();
		assert_eq!(
			async_rx.next().await,
			Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 9] })
		);
	}

	#[tokio::test]
	async fn send_sync_notification_to_non_existent_peer() {
		let (proto, mut notif) = notification_service();
		let (sink, _, mut sync_rx) = NotificationsSink::new(PeerId::random());
		let (mut handle, stream) = proto.split();
		let peer = PeerId::random();

		if let Err(error::Error::PeerDoesntExist(peer_id)) =
			notif.send_sync_notification(&peer, vec![1, 3, 3, 7])
		{
			assert_eq!(peer, peer_id);
		} else {
			panic!("invalid error received from `send_sync_notification()`");
		}
	}

	#[tokio::test]
	async fn send_async_notification_to_non_existent_peer() {
		let (proto, mut notif) = notification_service();
		let (sink, _, mut sync_rx) = NotificationsSink::new(PeerId::random());
		let (mut handle, stream) = proto.split();
		let peer = PeerId::random();

		if let Err(error::Error::PeerDoesntExist(peer_id)) =
			notif.send_async_notification(&peer, vec![1, 3, 3, 7]).await
		{
			assert_eq!(peer, peer_id);
		} else {
			panic!("invalid error received from `send_sync_notification()`");
		}
	}

	#[tokio::test]
	async fn receive_notification() {
		let (proto, mut notif) = notification_service();
		let (sink, _, mut sync_rx) = NotificationsSink::new(PeerId::random());
		let (mut handle, stream) = proto.split();
		let peer_id = PeerId::random();

		// validate inbound substream
		let result_rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).await.unwrap();

		if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
			notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(handshake, vec![1, 3, 3, 7]);
			result_tx.send(ValidationResult::Accept);
		} else {
			panic!("invalid event received");
		}
		assert_eq!(result_rx.await.unwrap(), ValidationResult::Accept);

		// report that a substream has been opened
		handle
			.report_substream_opened(peer_id, ObservedRole::Full, None, sink)
			.await
			.unwrap();

		if let Some(NotificationEvent::NotificationStreamOpened {
			peer,
			role,
			negotiated_fallback,
		}) = notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(negotiated_fallback, None);
			assert_eq!(role, ObservedRole::Full);
		} else {
			panic!("invalid event received");
		}

		// notification is received
		handle.report_notification_received(peer_id, vec![1, 3, 3, 8]).await.unwrap();

		if let Some(NotificationEvent::NotificationReceived { peer, notification }) =
			notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(notification, vec![1, 3, 3, 8]);
		} else {
			panic!("invalid event received");
		}
	}

	#[tokio::test]
	async fn backpressure_works() {
		let (proto, mut notif) = notification_service();
		let (sink, mut async_rx, _) = NotificationsSink::new(PeerId::random());
		let (mut handle, stream) = proto.split();
		let peer_id = PeerId::random();

		// validate inbound substream
		let result_rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).await.unwrap();

		if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
			notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(handshake, vec![1, 3, 3, 7]);
			result_tx.send(ValidationResult::Accept);
		} else {
			panic!("invalid event received");
		}
		assert_eq!(result_rx.await.unwrap(), ValidationResult::Accept);

		// report that a substream has been opened
		handle
			.report_substream_opened(peer_id, ObservedRole::Full, None, sink)
			.await
			.unwrap();

		if let Some(NotificationEvent::NotificationStreamOpened {
			peer,
			role,
			negotiated_fallback,
		}) = notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(negotiated_fallback, None);
			assert_eq!(role, ObservedRole::Full);
		} else {
			panic!("invalid event received");
		}

		// fill the message buffer with messages
		for i in 0..=ASYNC_NOTIFICATIONS_BUFFER_SIZE {
			assert!(
				futures::poll!(notif.send_async_notification(&peer_id, vec![1, 3, 3, i as u8]))
					.is_ready()
			);
		}

		// try to send one more message and verify that the call blocks
		assert!(
			futures::poll!(notif.send_async_notification(&peer_id, vec![1, 3, 3, 9])).is_pending()
		);

		// release one slot from the buffer for new message
		assert_eq!(
			async_rx.next().await,
			Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 0] })
		);

		// verify that a message can be sent
		assert!(
			futures::poll!(notif.send_async_notification(&peer_id, vec![1, 3, 3, 9])).is_ready()
		);
	}

	#[tokio::test]
	async fn peer_disconnects_then_sync_notification_is_sent() {
		let (proto, mut notif) = notification_service();
		let (sink, _, mut sync_rx) = NotificationsSink::new(PeerId::random());
		let (mut handle, stream) = proto.split();
		let peer_id = PeerId::random();

		// validate inbound substream
		let result_rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).await.unwrap();

		if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
			notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(handshake, vec![1, 3, 3, 7]);
			result_tx.send(ValidationResult::Accept);
		} else {
			panic!("invalid event received");
		}
		assert_eq!(result_rx.await.unwrap(), ValidationResult::Accept);

		// report that a substream has been opened
		handle
			.report_substream_opened(peer_id, ObservedRole::Full, None, sink)
			.await
			.unwrap();

		if let Some(NotificationEvent::NotificationStreamOpened {
			peer,
			role,
			negotiated_fallback,
		}) = notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(negotiated_fallback, None);
			assert_eq!(role, ObservedRole::Full);
		} else {
			panic!("invalid event received");
		}

		// report that a substream has been closed but don't poll `notif` to receive this
		// information
		handle.report_substream_closed(peer_id).await.unwrap();
		drop(sync_rx);

		// as per documentation, error is not reported but the notification is silently dropped
		assert!(notif.send_sync_notification(&peer_id, vec![1, 3, 3, 7]).is_ok());
	}

	#[tokio::test]
	async fn peer_disconnects_then_async_notification_is_sent() {
		let (proto, mut notif) = notification_service();
		let (sink, mut async_rx, _) = NotificationsSink::new(PeerId::random());
		let (mut handle, stream) = proto.split();
		let peer_id = PeerId::random();

		// validate inbound substream
		let result_rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).await.unwrap();

		if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
			notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(handshake, vec![1, 3, 3, 7]);
			result_tx.send(ValidationResult::Accept);
		} else {
			panic!("invalid event received");
		}
		assert_eq!(result_rx.await.unwrap(), ValidationResult::Accept);

		// report that a substream has been opened
		handle
			.report_substream_opened(peer_id, ObservedRole::Full, None, sink)
			.await
			.unwrap();

		if let Some(NotificationEvent::NotificationStreamOpened {
			peer,
			role,
			negotiated_fallback,
		}) = notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(negotiated_fallback, None);
			assert_eq!(role, ObservedRole::Full);
		} else {
			panic!("invalid event received");
		}

		// report that a substream has been closed but don't poll `notif` to receive this
		// information
		handle.report_substream_closed(peer_id).await.unwrap();
		drop(async_rx);

		// as per documentation, error is not reported but the notification is silently dropped
		if let Err(error::Error::ConnectionClosed) =
			notif.send_async_notification(&peer_id, vec![1, 3, 3, 7]).await
		{
		} else {
			panic!("invalid state after calling `send_async_notificatio()` on closed connection")
		}
	}
}
