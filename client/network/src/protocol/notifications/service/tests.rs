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

use std::future::Future;

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
		.report_substream_opened(peer_id, Direction::Inbound, vec![1, 3, 3, 7], None, sink)
		.unwrap();

	if let Some(NotificationEvent::NotificationStreamOpened {
		peer,
		negotiated_fallback,
		handshake,
		direction,
	}) = notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(negotiated_fallback, None);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		assert_eq!(direction, Direction::Inbound);
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
		.report_substream_opened(peer_id, Direction::Inbound, vec![1, 3, 3, 7], None, sink)
		.unwrap();

	if let Some(NotificationEvent::NotificationStreamOpened {
		peer,
		negotiated_fallback,
		handshake,
		direction,
	}) = notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(negotiated_fallback, None);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		assert_eq!(direction, Direction::Inbound);
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
		.report_substream_opened(peer_id, Direction::Inbound, vec![1, 3, 3, 7], None, sink)
		.unwrap();

	if let Some(NotificationEvent::NotificationStreamOpened {
		peer,
		negotiated_fallback,
		handshake,
		direction,
	}) = notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(negotiated_fallback, None);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		assert_eq!(direction, Direction::Inbound);
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

	// as per the original implementation, the call doesn't fail
	notif.send_sync_notification(&peer, vec![1, 3, 3, 7])
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
		panic!("invalid error received from `send_async_notification()`");
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
		.report_substream_opened(peer_id, Direction::Inbound, vec![1, 3, 3, 7], None, sink)
		.unwrap();

	if let Some(NotificationEvent::NotificationStreamOpened {
		peer,
		negotiated_fallback,
		handshake,
		direction,
	}) = notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(negotiated_fallback, None);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		assert_eq!(direction, Direction::Inbound);
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
		.report_substream_opened(peer_id, Direction::Inbound, vec![1, 3, 3, 7], None, sink)
		.unwrap();

	if let Some(NotificationEvent::NotificationStreamOpened {
		peer,
		negotiated_fallback,
		handshake,
		direction,
	}) = notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(negotiated_fallback, None);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		assert_eq!(direction, Direction::Inbound);
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
		.report_substream_opened(peer_id, Direction::Inbound, vec![1, 3, 3, 7], None, sink)
		.unwrap();

	if let Some(NotificationEvent::NotificationStreamOpened {
		peer,
		negotiated_fallback,
		handshake,
		direction,
	}) = notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(negotiated_fallback, None);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		assert_eq!(direction, Direction::Inbound);
	} else {
		panic!("invalid event received");
	}

	// report that a substream has been closed but don't poll `notif` to receive this
	// information
	handle.report_substream_closed(peer_id).unwrap();
	drop(sync_rx);

	// as per documentation, error is not reported but the notification is silently dropped
	notif.send_sync_notification(&peer_id, vec![1, 3, 3, 7]);
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
		.report_substream_opened(peer_id, Direction::Inbound, vec![1, 3, 3, 7], None, sink)
		.unwrap();

	if let Some(NotificationEvent::NotificationStreamOpened {
		peer,
		negotiated_fallback,
		handshake,
		direction,
	}) = notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(negotiated_fallback, None);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		assert_eq!(direction, Direction::Inbound);
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

	// verify that `notif1` gets the event
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

	// verify that `notif2` also gets the event
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
		.report_substream_opened(peer_id, Direction::Inbound, vec![1, 3, 3, 7], None, sink)
		.unwrap();

	for notif in vec![&mut notif1, &mut notif2, &mut notif3] {
		if let Some(NotificationEvent::NotificationStreamOpened {
			peer,
			negotiated_fallback,
			handshake,
			direction,
		}) = notif.next_event().await
		{
			assert_eq!(peer_id, peer);
			assert_eq!(negotiated_fallback, None);
			assert_eq!(handshake, vec![1, 3, 3, 7]);
			assert_eq!(direction, Direction::Inbound);
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
		notif.send_sync_notification(&peer_id, vec![1, 3, 3, i as u8]);
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

#[tokio::test]
async fn sending_notifications_using_notifications_sink_works() {
	let (proto, mut notif) = notification_service("/proto/1".into());
	let (sink, mut async_rx, mut sync_rx) = NotificationsSink::new(PeerId::random());
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
		.report_substream_opened(peer_id, Direction::Inbound, vec![1, 3, 3, 7], None, sink)
		.unwrap();

	if let Some(NotificationEvent::NotificationStreamOpened {
		peer,
		negotiated_fallback,
		handshake,
		direction,
	}) = notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(negotiated_fallback, None);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		assert_eq!(direction, Direction::Inbound);
	} else {
		panic!("invalid event received");
	}

	// get a copy of the notification sink and send a synchronous notification using.
	let sink = notif.message_sink(&peer_id).unwrap();
	sink.send_sync_notification(vec![1, 3, 3, 6]);

	// send an asynchronous notification using the acquired notifications sink.
	let _ = sink.send_async_notification(vec![1, 3, 3, 7]).await.unwrap();

	assert_eq!(
		sync_rx.next().await,
		Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 6] }),
	);
	assert_eq!(
		async_rx.next().await,
		Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 7] }),
	);

	// send notifications using the stored notification sink as well.
	notif.send_sync_notification(&peer_id, vec![1, 3, 3, 8]);
	notif.send_async_notification(&peer_id, vec![1, 3, 3, 9]).await.unwrap();

	assert_eq!(
		sync_rx.next().await,
		Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 8] }),
	);
	assert_eq!(
		async_rx.next().await,
		Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 9] }),
	);
}

#[test]
fn try_to_get_notifications_sink_for_non_existent_peer() {
	let (_proto, notif) = notification_service("/proto/1".into());
	assert!(notif.message_sink(&PeerId::random()).is_none());
}

#[tokio::test]
async fn notification_sink_replaced() {
	let (proto, mut notif) = notification_service("/proto/1".into());
	let (sink, mut async_rx, mut sync_rx) = NotificationsSink::new(PeerId::random());
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
		.report_substream_opened(peer_id, Direction::Inbound, vec![1, 3, 3, 7], None, sink)
		.unwrap();

	if let Some(NotificationEvent::NotificationStreamOpened {
		peer,
		negotiated_fallback,
		handshake,
		direction,
	}) = notif.next_event().await
	{
		assert_eq!(peer_id, peer);
		assert_eq!(negotiated_fallback, None);
		assert_eq!(handshake, vec![1, 3, 3, 7]);
		assert_eq!(direction, Direction::Inbound);
	} else {
		panic!("invalid event received");
	}

	// get a copy of the notification sink and send a synchronous notification using.
	let sink = notif.message_sink(&peer_id).unwrap();
	sink.send_sync_notification(vec![1, 3, 3, 6]);

	// send an asynchronous notification using the acquired notifications sink.
	let _ = sink.send_async_notification(vec![1, 3, 3, 7]).await.unwrap();

	assert_eq!(
		sync_rx.next().await,
		Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 6] }),
	);
	assert_eq!(
		async_rx.next().await,
		Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 7] }),
	);

	// send notifications using the stored notification sink as well.
	notif.send_sync_notification(&peer_id, vec![1, 3, 3, 8]);
	notif.send_async_notification(&peer_id, vec![1, 3, 3, 9]).await.unwrap();

	assert_eq!(
		sync_rx.next().await,
		Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 8] }),
	);
	assert_eq!(
		async_rx.next().await,
		Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 9] }),
	);

	// the initial connection was closed and `Notifications` switched to secondary connection
	// and emitted `CustomProtocolReplaced` which informs the local `NotificationService` that
	// the notification sink was replaced.
	let (new_sink, mut new_async_rx, mut new_sync_rx) = NotificationsSink::new(PeerId::random());
	handle.report_notification_sink_replaced(peer_id, new_sink).unwrap();

	// drop the old sinks and poll `notif` once to register the sink replacement
	drop(sync_rx);
	drop(async_rx);

	futures::future::poll_fn(|cx| {
		let _ = std::pin::Pin::new(&mut notif.next_event()).poll(cx);
		std::task::Poll::Ready(())
	})
	.await;

	// verify that using the `NotificationService` API automatically results in using the correct
	// sink
	notif.send_sync_notification(&peer_id, vec![1, 3, 3, 8]);
	notif.send_async_notification(&peer_id, vec![1, 3, 3, 9]).await.unwrap();

	assert_eq!(
		new_sync_rx.next().await,
		Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 8] }),
	);
	assert_eq!(
		new_async_rx.next().await,
		Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 9] }),
	);

	// now send two notifications using the acquired message sink and verify that
	// it's also updated
	sink.send_sync_notification(vec![1, 3, 3, 6]);

	// send an asynchronous notification using the acquired notifications sink.
	let _ = sink.send_async_notification(vec![1, 3, 3, 7]).await.unwrap();

	assert_eq!(
		new_sync_rx.next().await,
		Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 6] }),
	);
	assert_eq!(
		new_async_rx.next().await,
		Some(NotificationsSinkMessage::Notification { message: vec![1, 3, 3, 7] }),
	);
}
