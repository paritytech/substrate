// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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
/// - Node A opens a substream to node B and sends a message which contains some protocol-specific
///   higher-level logic. This message is prefixed with a variable-length integer message length.
///   This message can be empty, in which case `0` is sent.
/// - If node B accepts the substream, it sends back a message with the same properties.
/// - If instead B refuses the connection (which typically happens because no empty slot is
///   available), then it immediately closes the substream without sending back anything.
/// - Node A can then send notifications to B, prefixed with a variable-length integer indicating
///   the length of the message.
/// - Either node A or node B can signal that it doesn't want this notifications substream anymore
///   by closing its writing side. The other party should respond by also closing their own
///   writing side soon after.
///
/// Notification substreams are unidirectional. If A opens a substream with B, then B is
/// encouraged but not required to open a substream to A as well.
///

use bytes::BytesMut;
use futures::prelude::*;
use futures_codec::Framed;
use libp2p::core::{UpgradeInfo, InboundUpgrade, OutboundUpgrade, upgrade};
use log::error;
use std::{borrow::Cow, convert::Infallible, io, iter, mem, pin::Pin, task::{Context, Poll}};
use unsigned_varint::codec::UviBytes;

/// Maximum allowed size of the two handshake messages, in bytes.
const MAX_HANDSHAKE_SIZE: usize = 1024;

/// Upgrade that accepts a substream, sends back a status message, then becomes a unidirectional
/// stream of messages.
#[derive(Debug, Clone)]
pub struct NotificationsIn {
	/// Protocol name to use when negotiating the substream.
	protocol_name: Cow<'static, str>,
}

/// Upgrade that opens a substream, waits for the remote to accept by sending back a status
/// message, then becomes a unidirectional sink of data.
#[derive(Debug, Clone)]
pub struct NotificationsOut {
	/// Protocol name to use when negotiating the substream.
	protocol_name: Cow<'static, str>,
	/// Message to send when we start the handshake.
	initial_message: Vec<u8>,
}

/// A substream for incoming notification messages.
///
/// When creating, this struct starts in a state in which we must first send back a handshake
/// message to the remote. No message will come before this has been done.
#[pin_project::pin_project]
pub struct NotificationsInSubstream<TSubstream> {
	#[pin]
	socket: Framed<TSubstream, UviBytes<io::Cursor<Vec<u8>>>>,
	handshake: NotificationsInSubstreamHandshake,
}

/// State of the handshake sending back process.
enum NotificationsInSubstreamHandshake {
	/// Waiting for the user to give us the handshake message.
	NotSent,
	/// User gave us the handshake message. Trying to push it in the socket.
	PendingSend(Vec<u8>),
	/// Handshake message was pushed in the socket. Still need to flush.
	Flush,
	/// Handshake message successfully sent and flushed.
	Sent,
	/// Remote has closed their writing side. We close our own writing side in return.
	ClosingInResponseToRemote,
	/// Both our side and the remote have closed their writing side.
	BothSidesClosed,
}

/// A substream for outgoing notification messages.
#[pin_project::pin_project]
pub struct NotificationsOutSubstream<TSubstream> {
	/// Substream where to send messages.
	#[pin]
	socket: Framed<TSubstream, UviBytes<io::Cursor<Vec<u8>>>>,
}

impl NotificationsIn {
	/// Builds a new potential upgrade.
	pub fn new(protocol_name: impl Into<Cow<'static, str>>) -> Self {
		NotificationsIn {
			protocol_name: protocol_name.into(),
		}
	}

	/// Returns the name of the protocol that we accept.
	pub fn protocol_name(&self) -> &Cow<'static, str> {
		&self.protocol_name
	}
}

impl UpgradeInfo for NotificationsIn {
	type Info = Cow<'static, [u8]>;
	type InfoIter = iter::Once<Self::Info>;

	fn protocol_info(&self) -> Self::InfoIter {
		let bytes: Cow<'static, [u8]> = match &self.protocol_name {
			Cow::Borrowed(s) => Cow::Borrowed(s.as_bytes()),
			Cow::Owned(s) => Cow::Owned(s.as_bytes().to_vec())
		};
		iter::once(bytes)
	}
}

impl<TSubstream> InboundUpgrade<TSubstream> for NotificationsIn
where TSubstream: AsyncRead + AsyncWrite + Unpin + Send + 'static,
{
	type Output = (Vec<u8>, NotificationsInSubstream<TSubstream>);
	type Future = Pin<Box<dyn Future<Output = Result<Self::Output, Self::Error>> + Send>>;
	type Error = NotificationsHandshakeError;

	fn upgrade_inbound(
		self,
		mut socket: TSubstream,
		_: Self::Info,
	) -> Self::Future {
		Box::pin(async move {
			let initial_message_len = unsigned_varint::aio::read_usize(&mut socket).await?;
			if initial_message_len > MAX_HANDSHAKE_SIZE {
				return Err(NotificationsHandshakeError::TooLarge {
					requested: initial_message_len,
					max: MAX_HANDSHAKE_SIZE,
				});
			}

			let mut initial_message = vec![0u8; initial_message_len];
			if !initial_message.is_empty() {
				socket.read_exact(&mut initial_message).await?;
			}

			let substream = NotificationsInSubstream {
				socket: Framed::new(socket, UviBytes::default()),
				handshake: NotificationsInSubstreamHandshake::NotSent,
			};

			Ok((initial_message, substream))
		})
	}
}

impl<TSubstream> NotificationsInSubstream<TSubstream>
where TSubstream: AsyncRead + AsyncWrite + Unpin,
{
	/// Sends the handshake in order to inform the remote that we accept the substream.
	pub fn send_handshake(&mut self, message: impl Into<Vec<u8>>) {
		if !matches!(self.handshake, NotificationsInSubstreamHandshake::NotSent) {
			error!(target: "sub-libp2p", "Tried to send handshake twice");
			return;
		}

		self.handshake = NotificationsInSubstreamHandshake::PendingSend(message.into());
	}

	/// Equivalent to `Stream::poll_next`, except that it only drives the handshake and is
	/// guaranteed to not generate any notification.
	pub fn poll_process(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<Infallible, io::Error>> {
		let mut this = self.project();

		loop {
			match mem::replace(this.handshake, NotificationsInSubstreamHandshake::Sent) {
				NotificationsInSubstreamHandshake::PendingSend(msg) =>
					match Sink::poll_ready(this.socket.as_mut(), cx) {
						Poll::Ready(_) => {
							*this.handshake = NotificationsInSubstreamHandshake::Flush;
							match Sink::start_send(this.socket.as_mut(), io::Cursor::new(msg)) {
								Ok(()) => {},
								Err(err) => return Poll::Ready(Err(err)),
							}
						},
						Poll::Pending => {
							*this.handshake = NotificationsInSubstreamHandshake::PendingSend(msg);
							return Poll::Pending
						}
					},
				NotificationsInSubstreamHandshake::Flush =>
					match Sink::poll_flush(this.socket.as_mut(), cx)? {
						Poll::Ready(()) =>
							*this.handshake = NotificationsInSubstreamHandshake::Sent,
						Poll::Pending => {
							*this.handshake = NotificationsInSubstreamHandshake::Flush;
							return Poll::Pending
						}
					},

				st @ NotificationsInSubstreamHandshake::NotSent |
				st @ NotificationsInSubstreamHandshake::Sent |
				st @ NotificationsInSubstreamHandshake::ClosingInResponseToRemote |
				st @ NotificationsInSubstreamHandshake::BothSidesClosed => {
					*this.handshake = st;
					return Poll::Pending;
				}
			}
		}
	}
}

impl<TSubstream> Stream for NotificationsInSubstream<TSubstream>
where TSubstream: AsyncRead + AsyncWrite + Unpin,
{
	type Item = Result<BytesMut, io::Error>;

	fn poll_next(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		let mut this = self.project();

		// This `Stream` implementation first tries to send back the handshake if necessary.
		loop {
			match mem::replace(this.handshake, NotificationsInSubstreamHandshake::Sent) {
				NotificationsInSubstreamHandshake::NotSent => {
					*this.handshake = NotificationsInSubstreamHandshake::NotSent;
					return Poll::Pending
				},
				NotificationsInSubstreamHandshake::PendingSend(msg) =>
					match Sink::poll_ready(this.socket.as_mut(), cx) {
						Poll::Ready(_) => {
							*this.handshake = NotificationsInSubstreamHandshake::Flush;
							match Sink::start_send(this.socket.as_mut(), io::Cursor::new(msg)) {
								Ok(()) => {},
								Err(err) => return Poll::Ready(Some(Err(err))),
							}
						},
						Poll::Pending => {
							*this.handshake = NotificationsInSubstreamHandshake::PendingSend(msg);
							return Poll::Pending
						}
					},
				NotificationsInSubstreamHandshake::Flush =>
					match Sink::poll_flush(this.socket.as_mut(), cx)? {
						Poll::Ready(()) =>
							*this.handshake = NotificationsInSubstreamHandshake::Sent,
						Poll::Pending => {
							*this.handshake = NotificationsInSubstreamHandshake::Flush;
							return Poll::Pending
						}
					},

				NotificationsInSubstreamHandshake::Sent => {
					match Stream::poll_next(this.socket.as_mut(), cx) {
						Poll::Ready(None) => *this.handshake =
							NotificationsInSubstreamHandshake::ClosingInResponseToRemote,
						Poll::Ready(Some(msg)) => {
							*this.handshake = NotificationsInSubstreamHandshake::Sent;
							return Poll::Ready(Some(msg))
						},
						Poll::Pending => {
							*this.handshake = NotificationsInSubstreamHandshake::Sent;
							return Poll::Pending
						},
					}
				},

				NotificationsInSubstreamHandshake::ClosingInResponseToRemote =>
					match Sink::poll_close(this.socket.as_mut(), cx)? {
						Poll::Ready(()) =>
							*this.handshake = NotificationsInSubstreamHandshake::BothSidesClosed,
						Poll::Pending => {
							*this.handshake = NotificationsInSubstreamHandshake::ClosingInResponseToRemote;
							return Poll::Pending
						}
					},

				NotificationsInSubstreamHandshake::BothSidesClosed =>
					return Poll::Ready(None),
			}
		}
	}
}

impl NotificationsOut {
	/// Builds a new potential upgrade.
	pub fn new(protocol_name: impl Into<Cow<'static, str>>, initial_message: impl Into<Vec<u8>>) -> Self {
		let initial_message = initial_message.into();
		if initial_message.len() > MAX_HANDSHAKE_SIZE {
			error!(target: "sub-libp2p", "Outbound networking handshake is above allowed protocol limit");
		}

		NotificationsOut {
			protocol_name: protocol_name.into(),
			initial_message,
		}
	}
}

impl UpgradeInfo for NotificationsOut {
	type Info = Cow<'static, [u8]>;
	type InfoIter = iter::Once<Self::Info>;

	fn protocol_info(&self) -> Self::InfoIter {
		let bytes: Cow<'static, [u8]> = match &self.protocol_name {
			Cow::Borrowed(s) => Cow::Borrowed(s.as_bytes()),
			Cow::Owned(s) => Cow::Owned(s.as_bytes().to_vec())
		};
		iter::once(bytes)
	}
}

impl<TSubstream> OutboundUpgrade<TSubstream> for NotificationsOut
where TSubstream: AsyncRead + AsyncWrite + Unpin + Send + 'static,
{
	type Output = (Vec<u8>, NotificationsOutSubstream<TSubstream>);
	type Future = Pin<Box<dyn Future<Output = Result<Self::Output, Self::Error>> + Send>>;
	type Error = NotificationsHandshakeError;

	fn upgrade_outbound(
		self,
		mut socket: TSubstream,
		_: Self::Info,
	) -> Self::Future {
		Box::pin(async move {
			upgrade::write_with_len_prefix(&mut socket, &self.initial_message).await?;

			// Reading handshake.
			let handshake_len = unsigned_varint::aio::read_usize(&mut socket).await?;
			if handshake_len > MAX_HANDSHAKE_SIZE {
				return Err(NotificationsHandshakeError::TooLarge {
					requested: handshake_len,
					max: MAX_HANDSHAKE_SIZE,
				});
			}

			let mut handshake = vec![0u8; handshake_len];
			if !handshake.is_empty() {
				socket.read_exact(&mut handshake).await?;
			}

			Ok((handshake, NotificationsOutSubstream {
				socket: Framed::new(socket, UviBytes::default()),
			}))
		})
	}
}

impl<TSubstream> Sink<Vec<u8>> for NotificationsOutSubstream<TSubstream>
	where TSubstream: AsyncRead + AsyncWrite + Unpin,
{
	type Error = NotificationsOutError;

	fn poll_ready(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
		let mut this = self.project();
		Sink::poll_ready(this.socket.as_mut(), cx)
			.map_err(NotificationsOutError::Io)
	}

	fn start_send(self: Pin<&mut Self>, item: Vec<u8>) -> Result<(), Self::Error> {
		let mut this = self.project();
		Sink::start_send(this.socket.as_mut(), io::Cursor::new(item))
			.map_err(NotificationsOutError::Io)
	}

	fn poll_flush(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
		let mut this = self.project();
		Sink::poll_flush(this.socket.as_mut(), cx)
			.map_err(NotificationsOutError::Io)
	}

	fn poll_close(self: Pin<&mut Self>, cx: &mut Context) -> Poll<Result<(), Self::Error>> {
		let mut this = self.project();
		Sink::poll_close(this.socket.as_mut(), cx)
			.map_err(NotificationsOutError::Io)
	}
}

/// Error generated by sending on a notifications out substream.
#[derive(Debug, derive_more::From, derive_more::Display)]
pub enum NotificationsHandshakeError {
	/// I/O error on the substream.
	Io(io::Error),

	/// Initial message or handshake was too large.
	#[display(fmt = "Initial message or handshake was too large: {}", requested)]
	TooLarge {
		/// Size requested by the remote.
		requested: usize,
		/// Maximum allowed,
		max: usize,
	},

	/// Error while decoding the variable-length integer.
	VarintDecode(unsigned_varint::decode::Error),
}

impl From<unsigned_varint::io::ReadError> for NotificationsHandshakeError {
	fn from(err: unsigned_varint::io::ReadError) -> Self {
		match err {
			unsigned_varint::io::ReadError::Io(err) => NotificationsHandshakeError::Io(err),
			unsigned_varint::io::ReadError::Decode(err) => NotificationsHandshakeError::VarintDecode(err),
			_ => {
				log::warn!("Unrecognized varint decoding error");
				NotificationsHandshakeError::Io(From::from(io::ErrorKind::InvalidData))
			}
		}
	}
}

/// Error generated by sending on a notifications out substream.
#[derive(Debug, derive_more::From, derive_more::Display)]
pub enum NotificationsOutError {
	/// I/O error on the substream.
	Io(io::Error),
}

#[cfg(test)]
mod tests {
	use super::{NotificationsIn, NotificationsOut};

	use async_std::net::{TcpListener, TcpStream};
	use futures::{prelude::*, channel::oneshot};
	use libp2p::core::upgrade;
	use std::borrow::Cow;

	#[test]
	fn basic_works() {
		const PROTO_NAME: Cow<'static, str> = Cow::Borrowed("/test/proto/1");
		let (listener_addr_tx, listener_addr_rx) = oneshot::channel();

		let client = async_std::task::spawn(async move {
			let socket = TcpStream::connect(listener_addr_rx.await.unwrap()).await.unwrap();
			let (handshake, mut substream) = upgrade::apply_outbound(
				socket,
				NotificationsOut::new(PROTO_NAME, &b"initial message"[..]),
				upgrade::Version::V1
			).await.unwrap();

			assert_eq!(handshake, b"hello world");
			substream.send(b"test message".to_vec()).await.unwrap();
		});

		async_std::task::block_on(async move {
			let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
			listener_addr_tx.send(listener.local_addr().unwrap()).unwrap();

			let (socket, _) = listener.accept().await.unwrap();
			let (initial_message, mut substream) = upgrade::apply_inbound(
				socket,
				NotificationsIn::new(PROTO_NAME)
			).await.unwrap();

			assert_eq!(initial_message, b"initial message");
			substream.send_handshake(&b"hello world"[..]);

			let msg = substream.next().await.unwrap().unwrap();
			assert_eq!(msg.as_ref(), b"test message");
		});

		async_std::task::block_on(client);
	}

	#[test]
	fn empty_handshake() {
		// Check that everything still works when the handshake messages are empty.

		const PROTO_NAME: Cow<'static, str> = Cow::Borrowed("/test/proto/1");
		let (listener_addr_tx, listener_addr_rx) = oneshot::channel();

		let client = async_std::task::spawn(async move {
			let socket = TcpStream::connect(listener_addr_rx.await.unwrap()).await.unwrap();
			let (handshake, mut substream) = upgrade::apply_outbound(
				socket,
				NotificationsOut::new(PROTO_NAME, vec![]),
				upgrade::Version::V1
			).await.unwrap();

			assert!(handshake.is_empty());
			substream.send(Default::default()).await.unwrap();
		});

		async_std::task::block_on(async move {
			let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
			listener_addr_tx.send(listener.local_addr().unwrap()).unwrap();

			let (socket, _) = listener.accept().await.unwrap();
			let (initial_message, mut substream) = upgrade::apply_inbound(
				socket,
				NotificationsIn::new(PROTO_NAME)
			).await.unwrap();

			assert!(initial_message.is_empty());
			substream.send_handshake(vec![]);

			let msg = substream.next().await.unwrap().unwrap();
			assert!(msg.as_ref().is_empty());
		});

		async_std::task::block_on(client);
	}

	#[test]
	fn refused() {
		const PROTO_NAME: Cow<'static, str> = Cow::Borrowed("/test/proto/1");
		let (listener_addr_tx, listener_addr_rx) = oneshot::channel();

		let client = async_std::task::spawn(async move {
			let socket = TcpStream::connect(listener_addr_rx.await.unwrap()).await.unwrap();
			let outcome = upgrade::apply_outbound(
				socket,
				NotificationsOut::new(PROTO_NAME, &b"hello"[..]),
				upgrade::Version::V1
			).await;

			// Despite the protocol negotiation being successfully conducted on the listener
			// side, we have to receive an error here because the listener didn't send the
			// handshake.
			assert!(outcome.is_err());
		});

		async_std::task::block_on(async move {
			let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
			listener_addr_tx.send(listener.local_addr().unwrap()).unwrap();

			let (socket, _) = listener.accept().await.unwrap();
			let (initial_msg, substream) = upgrade::apply_inbound(
				socket,
				NotificationsIn::new(PROTO_NAME)
			).await.unwrap();

			assert_eq!(initial_msg, b"hello");

			// We successfully upgrade to the protocol, but then close the substream.
			drop(substream);
		});

		async_std::task::block_on(client);
	}

	#[test]
	fn large_initial_message_refused() {
		const PROTO_NAME: Cow<'static, str> = Cow::Borrowed("/test/proto/1");
		let (listener_addr_tx, listener_addr_rx) = oneshot::channel();

		let client = async_std::task::spawn(async move {
			let socket = TcpStream::connect(listener_addr_rx.await.unwrap()).await.unwrap();
			let ret = upgrade::apply_outbound(
				socket,
				// We check that an initial message that is too large gets refused.
				NotificationsOut::new(PROTO_NAME, (0..32768).map(|_| 0).collect::<Vec<_>>()),
				upgrade::Version::V1
			).await;
			assert!(ret.is_err());
		});

		async_std::task::block_on(async move {
			let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
			listener_addr_tx.send(listener.local_addr().unwrap()).unwrap();

			let (socket, _) = listener.accept().await.unwrap();
			let ret = upgrade::apply_inbound(
				socket,
				NotificationsIn::new(PROTO_NAME)
			).await;
			assert!(ret.is_err());
		});

		async_std::task::block_on(client);
	}

	#[test]
	fn large_handshake_refused() {
		const PROTO_NAME: Cow<'static, str> = Cow::Borrowed("/test/proto/1");
		let (listener_addr_tx, listener_addr_rx) = oneshot::channel();

		let client = async_std::task::spawn(async move {
			let socket = TcpStream::connect(listener_addr_rx.await.unwrap()).await.unwrap();
			let ret = upgrade::apply_outbound(
				socket,
				NotificationsOut::new(PROTO_NAME, &b"initial message"[..]),
				upgrade::Version::V1
			).await;
			assert!(ret.is_err());
		});

		async_std::task::block_on(async move {
			let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
			listener_addr_tx.send(listener.local_addr().unwrap()).unwrap();

			let (socket, _) = listener.accept().await.unwrap();
			let (initial_message, mut substream) = upgrade::apply_inbound(
				socket,
				NotificationsIn::new(PROTO_NAME)
			).await.unwrap();
			assert_eq!(initial_message, b"initial message");

			// We check that a handshake that is too large gets refused.
			substream.send_handshake((0..32768).map(|_| 0).collect::<Vec<_>>());
			let _ = substream.next().await;
		});

		async_std::task::block_on(client);
	}
}
