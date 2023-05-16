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

use super::*;
use crate::protocol::notifications::handler::{
	NotificationsSinkMessage, ASYNC_NOTIFICATIONS_BUFFER_SIZE,
};

#[tokio::test]
async fn validate_and_accept_substream() {
	let (proto, mut notif) = notification_service("/proto/1".into());
	let (handle, _stream) = proto.split();

	let peer_id = PeerId::random();
	let rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).unwrap();

	if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
		notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		let _ = result_tx.send(ValidationResult::Accept).unwrap();
	} else {
		panic!("invalid event received");
	}

	assert_eq!(rx.await.unwrap(), ValidationResult::Accept);
}

#[tokio::test]
async fn substream_opened() {
	let (proto, mut notif) = notification_service("/proto/1".into());
	let (sink, _, _) = NotificationsSink::new(PeerId::random());
	let (mut handle, _stream) = proto.split();

	let peer_id = PeerId::random();
	handle
		.report_substream_opened(peer_id, vec![1, 3, 3, 7], ObservedRole::Full, None, sink)
		.unwrap();

	if let Some(NotificationEvent::NotificationStreamOpened {
		peer,
		role,
		negotiated_fallback,
		handshake,
	}) = notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(negotiated_fallback, None);
		assert_eq!(role, ObservedRole::Full);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
	} else {
		panic!("invalid event received");
	}
}

#[tokio::test]
async fn send_sync_notification() {
	let (proto, mut notif) = notification_service("/proto/1".into());
	let (sink, _, mut sync_rx) = NotificationsSink::new(PeerId::random());
	let (mut handle, _stream) = proto.split();
	let peer_id = PeerId::random();

	// validate inbound substream
	let result_rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).unwrap();

	if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
		notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		let _ = result_tx.send(ValidationResult::Accept).unwrap();
	} else {
		panic!("invalid event received");
	}
	assert_eq!(result_rx.await.unwrap(), ValidationResult::Accept);

	// report that a substream has been opened
	handle
		.report_substream_opened(peer_id, vec![1, 3, 3, 7], ObservedRole::Full, None, sink)
		.unwrap();

	if let Some(NotificationEvent::NotificationStreamOpened {
		peer,
		role,
		negotiated_fallback,
		handshake,
	}) = notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(negotiated_fallback, None);
		assert_eq!(role, ObservedRole::Full);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
	} else {
		panic!("invalid event received");
	}

	notif.send_sync_notification(&peer_id, vec![1, 3, 3, 8]).unwrap();
	assert_eq!(
		sync_rx.next().await,
		Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 8] })
	);
}

#[tokio::test]
async fn send_async_notification() {
	let (proto, mut notif) = notification_service("/proto/1".into());
	let (sink, mut async_rx, _) = NotificationsSink::new(PeerId::random());
	let (mut handle, _stream) = proto.split();
	let peer_id = PeerId::random();

	// validate inbound substream
	let result_rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).unwrap();

	if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
		notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		let _ = result_tx.send(ValidationResult::Accept).unwrap();
	} else {
		panic!("invalid event received");
	}
	assert_eq!(result_rx.await.unwrap(), ValidationResult::Accept);

	// report that a substream has been opened
	handle
		.report_substream_opened(peer_id, vec![1, 3, 3, 7], ObservedRole::Full, None, sink)
		.unwrap();

	if let Some(NotificationEvent::NotificationStreamOpened {
		peer,
		role,
		negotiated_fallback,
		handshake,
	}) = notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(negotiated_fallback, None);
		assert_eq!(role, ObservedRole::Full);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
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
	let (proto, notif) = notification_service("/proto/1".into());
	let (_sink, _, _sync_rx) = NotificationsSink::new(PeerId::random());
	let (_handle, _stream) = proto.split();
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
	let (proto, notif) = notification_service("/proto/1".into());
	let (_sink, _, _sync_rx) = NotificationsSink::new(PeerId::random());
	let (_handle, _stream) = proto.split();
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
	let (proto, mut notif) = notification_service("/proto/1".into());
	let (sink, _, _sync_rx) = NotificationsSink::new(PeerId::random());
	let (mut handle, _stream) = proto.split();
	let peer_id = PeerId::random();

	// validate inbound substream
	let result_rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).unwrap();

	if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
		notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		let _ = result_tx.send(ValidationResult::Accept).unwrap();
	} else {
		panic!("invalid event received");
	}
	assert_eq!(result_rx.await.unwrap(), ValidationResult::Accept);

	// report that a substream has been opened
	handle
		.report_substream_opened(peer_id, vec![1, 3, 3, 7], ObservedRole::Full, None, sink)
		.unwrap();

	if let Some(NotificationEvent::NotificationStreamOpened {
		peer,
		role,
		negotiated_fallback,
		handshake,
	}) = notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(negotiated_fallback, None);
		assert_eq!(role, ObservedRole::Full);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
	} else {
		panic!("invalid event received");
	}

	// notification is received
	handle.report_notification_received(peer_id, vec![1, 3, 3, 8]).unwrap();

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
	let (proto, mut notif) = notification_service("/proto/1".into());
	let (sink, mut async_rx, _) = NotificationsSink::new(PeerId::random());
	let (mut handle, _stream) = proto.split();
	let peer_id = PeerId::random();

	// validate inbound substream
	let result_rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).unwrap();

	if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
		notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		let _ = result_tx.send(ValidationResult::Accept).unwrap();
	} else {
		panic!("invalid event received");
	}
	assert_eq!(result_rx.await.unwrap(), ValidationResult::Accept);

	// report that a substream has been opened
	handle
		.report_substream_opened(peer_id, vec![1, 3, 3, 7], ObservedRole::Full, None, sink)
		.unwrap();

	if let Some(NotificationEvent::NotificationStreamOpened {
		peer,
		role,
		negotiated_fallback,
		handshake,
	}) = notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(negotiated_fallback, None);
		assert_eq!(role, ObservedRole::Full);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
	} else {
		panic!("invalid event received");
	}

	// fill the message buffer with messages
	for i in 0..=ASYNC_NOTIFICATIONS_BUFFER_SIZE {
		assert!(futures::poll!(notif.send_async_notification(&peer_id, vec![1, 3, 3, i as u8]))
			.is_ready());
	}

	// try to send one more message and verify that the call blocks
	assert!(futures::poll!(notif.send_async_notification(&peer_id, vec![1, 3, 3, 9])).is_pending());

	// release one slot from the buffer for new message
	assert_eq!(
		async_rx.next().await,
		Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 0] })
	);

	// verify that a message can be sent
	assert!(futures::poll!(notif.send_async_notification(&peer_id, vec![1, 3, 3, 9])).is_ready());
}

#[tokio::test]
async fn peer_disconnects_then_sync_notification_is_sent() {
	let (proto, mut notif) = notification_service("/proto/1".into());
	let (sink, _, sync_rx) = NotificationsSink::new(PeerId::random());
	let (mut handle, _stream) = proto.split();
	let peer_id = PeerId::random();

	// validate inbound substream
	let result_rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).unwrap();

	if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
		notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		let _ = result_tx.send(ValidationResult::Accept).unwrap();
	} else {
		panic!("invalid event received");
	}
	assert_eq!(result_rx.await.unwrap(), ValidationResult::Accept);

	// report that a substream has been opened
	handle
		.report_substream_opened(peer_id, vec![1, 3, 3, 7], ObservedRole::Full, None, sink)
		.unwrap();

	if let Some(NotificationEvent::NotificationStreamOpened {
		peer,
		role,
		negotiated_fallback,
		handshake,
	}) = notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(negotiated_fallback, None);
		assert_eq!(role, ObservedRole::Full);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
	} else {
		panic!("invalid event received");
	}

	// report that a substream has been closed but don't poll `notif` to receive this
	// information
	handle.report_substream_closed(peer_id).unwrap();
	drop(sync_rx);

	// as per documentation, error is not reported but the notification is silently dropped
	assert!(notif.send_sync_notification(&peer_id, vec![1, 3, 3, 7]).is_ok());
}

#[tokio::test]
async fn peer_disconnects_then_async_notification_is_sent() {
	let (proto, mut notif) = notification_service("/proto/1".into());
	let (sink, async_rx, _) = NotificationsSink::new(PeerId::random());
	let (mut handle, _stream) = proto.split();
	let peer_id = PeerId::random();

	// validate inbound substream
	let result_rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).unwrap();

	if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
		notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		let _ = result_tx.send(ValidationResult::Accept).unwrap();
	} else {
		panic!("invalid event received");
	}
	assert_eq!(result_rx.await.unwrap(), ValidationResult::Accept);

	// report that a substream has been opened
	handle
		.report_substream_opened(peer_id, vec![1, 3, 3, 7], ObservedRole::Full, None, sink)
		.unwrap();

	if let Some(NotificationEvent::NotificationStreamOpened {
		peer,
		role,
		negotiated_fallback,
		handshake,
	}) = notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(negotiated_fallback, None);
		assert_eq!(role, ObservedRole::Full);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
	} else {
		panic!("invalid event received");
	}

	// report that a substream has been closed but don't poll `notif` to receive this
	// information
	handle.report_substream_closed(peer_id).unwrap();
	drop(async_rx);

	// as per documentation, error is not reported but the notification is silently dropped
	if let Err(error::Error::ConnectionClosed) =
		notif.send_async_notification(&peer_id, vec![1, 3, 3, 7]).await
	{
	} else {
		panic!("invalid state after calling `send_async_notificatio()` on closed connection")
	}
}

#[tokio::test]
async fn cloned_service_opening_substream_works() {
	let (proto, mut notif1) = notification_service("/proto/1".into());
	let (_sink, _async_rx, _) = NotificationsSink::new(PeerId::random());
	let (handle, _stream) = proto.split();
	let mut notif2 = notif1.clone().unwrap();
	let peer_id = PeerId::random();

	// validate inbound substream
	let mut result_rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).unwrap();

	// verify that `stream1` also gets the event
	if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
		notif1.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		let _ = result_tx.send(ValidationResult::Accept).unwrap();
	} else {
		panic!("invalid event received");
	}

	// verify that because only one listener has thus far send their result, the result is
	// pending
	assert!(result_rx.try_recv().is_err());

	// verify that `stream2` also gets the event
	if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
		notif2.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		result_tx.send(ValidationResult::Accept).unwrap();
	} else {
		panic!("invalid event received");
	}

	assert_eq!(result_rx.await.unwrap(), ValidationResult::Accept);
}

#[tokio::test]
async fn cloned_service_one_service_rejects_substream() {
	let (proto, mut notif1) = notification_service("/proto/1".into());
	let (_sink, _async_rx, _) = NotificationsSink::new(PeerId::random());
	let (handle, _stream) = proto.split();
	let mut notif2 = notif1.clone().unwrap();
	let mut notif3 = notif2.clone().unwrap();
	let peer_id = PeerId::random();

	// validate inbound substream
	let mut result_rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).unwrap();

	for notif in vec![&mut notif1, &mut notif2] {
		if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
			notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(handshake, vec![1, 3, 3, 7]);
			let _ = result_tx.send(ValidationResult::Accept).unwrap();
		} else {
			panic!("invalid event received");
		}
	}

	// `notif3` has not yet sent their validation result
	assert!(result_rx.try_recv().is_err());

	if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
		notif3.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		let _ = result_tx.send(ValidationResult::Reject).unwrap();
	} else {
		panic!("invalid event received");
	}
	assert_eq!(result_rx.await.unwrap(), ValidationResult::Reject);
}

#[tokio::test]
async fn cloned_service_opening_substream_sending_and_receiving_notifications_work() {
	let (proto, mut notif1) = notification_service("/proto/1".into());
	let (sink, _, mut sync_rx) = NotificationsSink::new(PeerId::random());
	let (mut handle, _stream) = proto.split();
	let mut notif2 = notif1.clone().unwrap();
	let mut notif3 = notif1.clone().unwrap();
	let peer_id = PeerId::random();

	// validate inbound substream
	let result_rx = handle.report_incoming_substream(peer_id, vec![1, 3, 3, 7]).unwrap();

	for notif in vec![&mut notif1, &mut notif2, &mut notif3] {
		// accept the inbound substream for all services
		if let Some(NotificationEvent::ValidateInboundSubstream { peer, handshake, result_tx }) =
			notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(handshake, vec![1, 3, 3, 7]);
			let _ = result_tx.send(ValidationResult::Accept).unwrap();
		} else {
			panic!("invalid event received");
		}
	}
	assert_eq!(result_rx.await.unwrap(), ValidationResult::Accept);

	// report that then notification stream has been opened
	handle
		.report_substream_opened(peer_id, vec![1, 3, 3, 7], ObservedRole::Full, None, sink)
		.unwrap();

	for notif in vec![&mut notif1, &mut notif2, &mut notif3] {
		if let Some(NotificationEvent::NotificationStreamOpened {
			peer,
			role,
			negotiated_fallback,
			handshake,
		}) = notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(negotiated_fallback, None);
			assert_eq!(role, ObservedRole::Full);
			assert_eq!(handshake, vec![1, 3, 3, 7]);
		} else {
			panic!("invalid event received");
		}
	}
	// receive a notification from peer and verify all services receive it
	handle.report_notification_received(peer_id, vec![1, 3, 3, 8]).unwrap();

	for notif in vec![&mut notif1, &mut notif2, &mut notif3] {
		if let Some(NotificationEvent::NotificationReceived { peer, notification }) =
			notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(notification, vec![1, 3, 3, 8]);
		} else {
			panic!("invalid event received");
		}
	}

	for (i, notif) in vec![&mut notif1, &mut notif2, &mut notif3].iter().enumerate() {
		// send notification from each service and verify peer receives it
		notif.send_sync_notification(&peer_id, vec![1, 3, 3, i as u8]).unwrap();
		assert_eq!(
			sync_rx.next().await,
			Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, i as u8] })
		);
	}

	// close the substream for peer and verify all services receive the event
	handle.report_substream_closed(peer_id).unwrap();

	for notif in vec![&mut notif1, &mut notif2, &mut notif3] {
		if let Some(NotificationEvent::NotificationStreamClosed { peer }) = notif.next_event().await
		{
			assert_eq!(peer_id, peer);
		} else {
			panic!("invalid event received");
		}
	}
}
