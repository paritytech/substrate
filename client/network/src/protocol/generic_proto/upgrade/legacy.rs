// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

use crate::config::ProtocolId;
use bytes::BytesMut;
use futures::prelude::*;
use asynchronous_codec::Framed;
use libp2p::core::{UpgradeInfo, InboundUpgrade, OutboundUpgrade, upgrade::ProtocolName};
use parking_lot::RwLock;
use std::{collections::VecDeque, io, pin::Pin, sync::Arc, vec::IntoIter as VecIntoIter};
use std::task::{Context, Poll};
use unsigned_varint::codec::UviBytes;

/// Connection upgrade for a single protocol.
///
/// Note that "a single protocol" here refers to `par` for example. However
/// each protocol can have multiple different versions for networking purposes.
pub struct RegisteredProtocol {
	/// Id of the protocol for API purposes.
	id: ProtocolId,
	/// Base name of the protocol as advertised on the network.
	/// Ends with `/` so that we can append a version number behind.
	base_name: Vec<u8>,
	/// List of protocol versions that we support.
	/// Ordered in descending order so that the best comes first.
	supported_versions: Vec<u8>,
	/// Handshake to send after the substream is open.
	handshake_message: Arc<RwLock<Vec<u8>>>,
}

impl RegisteredProtocol {
	/// Creates a new `RegisteredProtocol`.
	pub fn new(protocol: impl Into<ProtocolId>, versions: &[u8], handshake_message: Arc<RwLock<Vec<u8>>>)
		-> Self {
		let protocol = protocol.into();
		let mut base_name = b"/substrate/".to_vec();
		base_name.extend_from_slice(protocol.as_ref().as_bytes());
		base_name.extend_from_slice(b"/");

		RegisteredProtocol {
			base_name,
			id: protocol,
			supported_versions: {
				let mut tmp = versions.to_vec();
				tmp.sort_by(|a, b| b.cmp(&a));
				tmp
			},
			handshake_message,
		}
	}

	/// Returns the `Arc` to the handshake message that was passed at initialization.
	pub fn handshake_message(&self) -> &Arc<RwLock<Vec<u8>>> {
		&self.handshake_message
	}
}

impl Clone for RegisteredProtocol {
	fn clone(&self) -> Self {
		RegisteredProtocol {
			id: self.id.clone(),
			base_name: self.base_name.clone(),
			supported_versions: self.supported_versions.clone(),
			handshake_message: self.handshake_message.clone(),
		}
	}
}

/// Output of a `RegisteredProtocol` upgrade.
pub struct RegisteredProtocolSubstream<TSubstream> {
	/// If true, we are in the process of closing the sink.
	is_closing: bool,
	/// Buffer of packets to send.
	send_queue: VecDeque<BytesMut>,
	/// If true, we should call `poll_complete` on the inner sink.
	requires_poll_flush: bool,
	/// The underlying substream.
	inner: stream::Fuse<Framed<TSubstream, UviBytes<BytesMut>>>,
	/// If true, we have sent a "remote is clogged" event recently and shouldn't send another one
	/// unless the buffer empties then fills itself again.
	clogged_fuse: bool,
}

impl<TSubstream> RegisteredProtocolSubstream<TSubstream> {
	/// Starts a graceful shutdown process on this substream.
	///
	/// Note that "graceful" means that we sent a closing message. We don't wait for any
	/// confirmation from the remote.
	///
	/// After calling this, the stream is guaranteed to finish soon-ish.
	pub fn shutdown(&mut self) {
		self.is_closing = true;
		self.send_queue.clear();
	}
}

/// Event produced by the `RegisteredProtocolSubstream`.
#[derive(Debug, Clone)]
pub enum RegisteredProtocolEvent {
	/// Received a message from the remote.
	Message(BytesMut),

	/// Diagnostic event indicating that the connection is clogged and we should avoid sending too
	/// many messages to it.
	Clogged,
}

impl<TSubstream> Stream for RegisteredProtocolSubstream<TSubstream>
where TSubstream: AsyncRead + AsyncWrite + Unpin {
	type Item = Result<RegisteredProtocolEvent, io::Error>;

	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
		// Flushing the local queue.
		while !self.send_queue.is_empty() {
			match Pin::new(&mut self.inner).poll_ready(cx) {
				Poll::Ready(Ok(())) => {},
				Poll::Ready(Err(err)) => return Poll::Ready(Some(Err(err))),
				Poll::Pending => break,
			}

			if let Some(packet) = self.send_queue.pop_front() {
				Pin::new(&mut self.inner).start_send(packet)?;
				self.requires_poll_flush = true;
			}
		}

		// If we are closing, close as soon as the Sink is closed.
		if self.is_closing {
			return match Pin::new(&mut self.inner).poll_close(cx) {
				Poll::Pending => Poll::Pending,
				Poll::Ready(Ok(_)) => Poll::Ready(None),
				Poll::Ready(Err(err)) => Poll::Ready(Some(Err(err))),
			}
		}

		// Indicating that the remote is clogged if that's the case.
		if self.send_queue.len() >= 1536 {
			if !self.clogged_fuse {
				// Note: this fuse is important not just for preventing us from flooding the logs;
				// 	if you remove the fuse, then we will always return early from this function and
				//	thus never read any message from the network.
				self.clogged_fuse = true;
				return Poll::Ready(Some(Ok(RegisteredProtocolEvent::Clogged)))
			}
		} else {
			self.clogged_fuse = false;
		}

		// Flushing if necessary.
		if self.requires_poll_flush {
			if let Poll::Ready(()) = Pin::new(&mut self.inner).poll_flush(cx)? {
				self.requires_poll_flush = false;
			}
		}

		// Receiving incoming packets.
		// Note that `inner` is wrapped in a `Fuse`, therefore we can poll it forever.
		match Pin::new(&mut self.inner).poll_next(cx)? {
			Poll::Ready(Some(data)) => {
				Poll::Ready(Some(Ok(RegisteredProtocolEvent::Message(data))))
			}
			Poll::Ready(None) =>
				if !self.requires_poll_flush && self.send_queue.is_empty() {
					Poll::Ready(None)
				} else {
					Poll::Pending
				}
			Poll::Pending => Poll::Pending,
		}
	}
}

impl UpgradeInfo for RegisteredProtocol {
	type Info = RegisteredProtocolName;
	type InfoIter = VecIntoIter<Self::Info>;

	#[inline]
	fn protocol_info(&self) -> Self::InfoIter {
		// Report each version as an individual protocol.
		self.supported_versions.iter().map(|&version| {
			let num = version.to_string();

			let mut name = self.base_name.clone();
			name.extend_from_slice(num.as_bytes());
			RegisteredProtocolName {
				name,
				version,
			}
		}).collect::<Vec<_>>().into_iter()
	}
}

/// Implementation of `ProtocolName` for a custom protocol.
#[derive(Debug, Clone)]
pub struct RegisteredProtocolName {
	/// Protocol name, as advertised on the wire.
	name: Vec<u8>,
	/// Version number. Stored in string form in `name`, but duplicated here for easier retrieval.
	version: u8,
}

impl ProtocolName for RegisteredProtocolName {
	fn protocol_name(&self) -> &[u8] {
		&self.name
	}
}

impl<TSubstream> InboundUpgrade<TSubstream> for RegisteredProtocol
where TSubstream: AsyncRead + AsyncWrite + Unpin + Send + 'static,
{
	type Output = (RegisteredProtocolSubstream<TSubstream>, Vec<u8>);
	type Future = Pin<Box<dyn Future<Output = Result<Self::Output, io::Error>> + Send>>;
	type Error = io::Error;

	fn upgrade_inbound(
		self,
		socket: TSubstream,
		_: Self::Info,
	) -> Self::Future {
		Box::pin(async move {
			let mut framed = {
				let mut codec = UviBytes::default();
				codec.set_max_len(16 * 1024 * 1024);		// 16 MiB hard limit for packets.
				Framed::new(socket, codec)
			};

			let handshake = BytesMut::from(&self.handshake_message.read()[..]);
			framed.send(handshake).await?;
			let received_handshake = framed.next().await
				.ok_or_else(|| io::ErrorKind::UnexpectedEof)??;

			Ok((RegisteredProtocolSubstream {
				is_closing: false,
				send_queue: VecDeque::new(),
				requires_poll_flush: false,
				inner: framed.fuse(),
				clogged_fuse: false,
			}, received_handshake.to_vec()))
		})
	}
}

impl<TSubstream> OutboundUpgrade<TSubstream> for RegisteredProtocol
where TSubstream: AsyncRead + AsyncWrite + Unpin + Send + 'static,
{
	type Output = <Self as InboundUpgrade<TSubstream>>::Output;
	type Future = <Self as InboundUpgrade<TSubstream>>::Future;
	type Error = <Self as InboundUpgrade<TSubstream>>::Error;

	fn upgrade_outbound(
		self,
		socket: TSubstream,
		_: Self::Info,
	) -> Self::Future {
		Box::pin(async move {
			let mut framed = {
				let mut codec = UviBytes::default();
				codec.set_max_len(16 * 1024 * 1024);		// 16 MiB hard limit for packets.
				Framed::new(socket, codec)
			};

			let handshake = BytesMut::from(&self.handshake_message.read()[..]);
			framed.send(handshake).await?;
			let received_handshake = framed.next().await
				.ok_or_else(|| {
					io::Error::new(io::ErrorKind::UnexpectedEof, "Failed to receive handshake")
				})??;

			Ok((RegisteredProtocolSubstream {
				is_closing: false,
				send_queue: VecDeque::new(),
				requires_poll_flush: false,
				inner: framed.fuse(),
				clogged_fuse: false,
			}, received_handshake.to_vec()))
		})
	}
}
