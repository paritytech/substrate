// Copyright 2019 Parity Technologies (UK) Ltd.
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

/// Notifications protocol.
///
/// The Substrate notifications protocol consists in the following:
///
/// - Node A opens a substream to node B.
/// - If node B accepts the substream, it sends back a message which contains some
///   protocol-specific higher-level logic. This message is prefixed with a variable-length
///   integer message length. This message can be empty, in which case `0` is sent. Afterwards,
///   the sending side of B is closed.
/// - If instead the node refuses the connection (which typically happens because no empty slot
///   is available), then it immediately closes the substream after the multistream-select
///   negotiation.
/// - Node A can then send notifications to B, prefixed with a variable-length integer indicating
///   the length of the message.
/// - Node A closes its writing side if it doesn't want the notifications substream anymore.
///
/// Notification substreams are unidirectional. If A opens a substream with B, then B is
/// encouraged but not required to open a substream to A as well.
///

use bytes::BytesMut;
use futures::prelude::*;
use libp2p::core::{Negotiated, UpgradeInfo, InboundUpgrade, OutboundUpgrade, upgrade};
use libp2p::tokio_codec::Framed;
use log::error;
use std::{borrow::Cow, collections::VecDeque, io, iter, mem};
use tokio_io::{AsyncRead, AsyncWrite};
use unsigned_varint::codec::UviBytes;

/// Upgrade that accepts a substream, sends back a status message, then becomes a unidirectional
/// stream of messages.
#[derive(Debug, Clone)]
pub struct NotificationsIn {
	/// Protocol name to use when negotiating the substream.
	protocol_name: Cow<'static, [u8]>,
}

/// Upgrade that opens a substream, waits for the remote to accept by sending back a status
/// message, then becomes a unidirectional sink of data.
#[derive(Debug, Clone)]
pub struct NotificationsOut {
	/// Protocol name to use when negotiating the substream.
	protocol_name: Cow<'static, [u8]>,
}

/// A substream for incoming notification messages.
///
/// When creating, this struct starts in a state in which we must first send back a handshake
/// message to the remote. No message will come before this has been done.
pub struct NotificationsInSubstream<TSubstream> {
	socket: Framed<Negotiated<TSubstream>, UviBytes<Vec<u8>>>,
	handshake: NotificationsInSubstreamHandshake,
}

/// State of the handshake sending back process.
enum NotificationsInSubstreamHandshake {
	/// Waiting for the user to give us the handshake message.
	NotSent,
	/// User gave us the handshake message. Trying to push it in the socket.
	PendingSend(Vec<u8>),
	/// Handshake message was pushed in the socket. Still need to flush.
	Close,
	/// Handshake message successfully sent.
	Sent,
}

/// A substream for outgoing notification messages.
pub struct NotificationsOutSubstream<TSubstream> {
	/// Substream where to send messages.
	socket: Framed<Negotiated<TSubstream>, UviBytes<Vec<u8>>>,
	/// Queue of messages waiting to be sent.
	messages_queue: VecDeque<Vec<u8>>,
	/// If true, we need to flush `socket`.
	need_flush: bool,
}

impl NotificationsIn {
	/// Builds a new potential upgrade.
	pub fn new(proto_name: impl Into<Cow<'static, [u8]>>) -> Self {
		NotificationsIn {
			protocol_name: proto_name.into(),
		}
	}

	/// Returns the name of the protocol that we accept.
	pub fn protocol_name(&self) -> &[u8] {
		&self.protocol_name
	}
}

impl UpgradeInfo for NotificationsIn {
	type Info = Cow<'static, [u8]>;
	type InfoIter = iter::Once<Self::Info>;

	fn protocol_info(&self) -> Self::InfoIter {
		iter::once(self.protocol_name.clone())
	}
}

impl<TSubstream> InboundUpgrade<TSubstream> for NotificationsIn
where TSubstream: AsyncRead + AsyncWrite + 'static,
{
	type Output = NotificationsInSubstream<TSubstream>;
	type Future = futures::future::FutureResult<Self::Output, Self::Error>;
	type Error = upgrade::ReadOneError;

	fn upgrade_inbound(
		self,
		socket: Negotiated<TSubstream>,
		_: Self::Info,
	) -> Self::Future {
		futures::future::ok(NotificationsInSubstream {
			socket: Framed::new(socket, UviBytes::default()),
			handshake: NotificationsInSubstreamHandshake::NotSent,
		})
	}
}

impl<TSubstream> NotificationsInSubstream<TSubstream>
where TSubstream: AsyncRead + AsyncWrite + 'static,
{
	/// Sends the handshake in order to inform the remote that we accept the substream.
	// TODO: doesn't seem to work if `message` is empty
	pub fn send_handshake(&mut self, message: impl Into<Vec<u8>>) {
		match self.handshake {
			NotificationsInSubstreamHandshake::NotSent => {}
			_ => {
				error!(target: "sub-libp2p", "Tried to send handshake twice");
				return;
			}
		}

		self.handshake = NotificationsInSubstreamHandshake::PendingSend(message.into());
	}
}

impl<TSubstream> Stream for NotificationsInSubstream<TSubstream>
where TSubstream: AsyncRead + AsyncWrite + 'static,
{
	type Item = BytesMut;
	type Error = io::Error;

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		// This `Stream` implementation first tries to send back the handshake if necessary.
		loop {
			match mem::replace(&mut self.handshake, NotificationsInSubstreamHandshake::Sent) {
				NotificationsInSubstreamHandshake::Sent =>
					return self.socket.poll(),
				NotificationsInSubstreamHandshake::NotSent =>
					return Ok(Async::NotReady),
				NotificationsInSubstreamHandshake::PendingSend(msg) =>
					match self.socket.start_send(msg)? {
						AsyncSink::Ready =>
							self.handshake = NotificationsInSubstreamHandshake::Close,
						AsyncSink::NotReady(msg) =>
							self.handshake = NotificationsInSubstreamHandshake::PendingSend(msg),
					},
				NotificationsInSubstreamHandshake::Close =>
					match self.socket.poll_complete()? {		// TODO: close()
						Async::Ready(()) =>
							self.handshake = NotificationsInSubstreamHandshake::Sent,
						Async::NotReady =>
							self.handshake = NotificationsInSubstreamHandshake::Close,
					},
			}
		}
	}
}

impl NotificationsOut {
	/// Builds a new potential upgrade.
	pub fn new(proto_name: impl Into<Cow<'static, [u8]>>) -> Self {
		NotificationsOut {
			protocol_name: proto_name.into(),
		}
	}
}

impl UpgradeInfo for NotificationsOut {
	type Info = Cow<'static, [u8]>;
	type InfoIter = iter::Once<Self::Info>;

	fn protocol_info(&self) -> Self::InfoIter {
		iter::once(self.protocol_name.clone())
	}
}

impl<TSubstream> OutboundUpgrade<TSubstream> for NotificationsOut
where TSubstream: AsyncRead + AsyncWrite + Send + 'static,
{
	type Output = (BytesMut, NotificationsOutSubstream<TSubstream>);
	type Future = Box<dyn Future<Item = Self::Output, Error = Self::Error> + Send>;
	type Error = io::Error;

	fn upgrade_outbound(
		self,
		socket: Negotiated<TSubstream>,
		proto_name: Self::Info,
	) -> Self::Future {
		Box::new(Framed::new(socket, UviBytes::default())
			.into_future()
			.map_err(|(err, _)| err)
			.and_then(|(handshake, socket)| {
				if let Some(handshake) = handshake {
					let sub = NotificationsOutSubstream {
						socket,
						messages_queue: VecDeque::new(),
						need_flush: false,
					};
					Ok((handshake, sub))
				} else {
					Err(io::Error::from(io::ErrorKind::UnexpectedEof))
				}
			}))
	}
}

impl<TSubstream> NotificationsOutSubstream<TSubstream>
where TSubstream: AsyncRead + AsyncWrite + 'static,
{
	/// Pushes a message to the queue of messages.
	pub fn push_message(&mut self, message: Vec<u8>) {
		// TODO: limit the size of the queue
		self.messages_queue.push_back(message);
	}

	/// Processes the substream. Must be called within the context of a task.
	pub fn process(&mut self) -> Result<(), io::Error> {
		while let Some(msg) = self.messages_queue.pop_front() {
			match self.socket.start_send(msg) {
				Err(err) => return Err(err),
				Ok(AsyncSink::Ready) => self.need_flush = true,
				Ok(AsyncSink::NotReady(msg)) => {
					self.messages_queue.push_front(msg);
					return Ok(());
				}
			}
		}

		if self.need_flush {
			match self.socket.poll_complete() {
				Err(err) => return Err(err),
				Ok(Async::Ready(())) => self.need_flush = false,
				Ok(Async::NotReady) => {},
			}
		}

		Ok(())
	}
}
