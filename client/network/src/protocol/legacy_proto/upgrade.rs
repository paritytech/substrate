// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

use crate::config::ProtocolId;
use bytes::BytesMut;
use futures::prelude::*;
use futures_codec::Framed;
use libp2p::core::{Endpoint, UpgradeInfo, InboundUpgrade, OutboundUpgrade, upgrade::ProtocolName};
use std::{collections::VecDeque, io, pin::Pin, vec::IntoIter as VecIntoIter};
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
}

impl RegisteredProtocol {
	/// Creates a new `RegisteredProtocol`. The `custom_data` parameter will be
	/// passed inside the `RegisteredProtocolOutput`.
	pub fn new(protocol: impl Into<ProtocolId>, versions: &[u8])
		-> Self {
		let protocol = protocol.into();
		let mut base_name = b"/substrate/".to_vec();
		base_name.extend_from_slice(protocol.as_bytes());
		base_name.extend_from_slice(b"/");

		RegisteredProtocol {
			base_name,
			id: protocol,
			supported_versions: {
				let mut tmp = versions.to_vec();
				tmp.sort_unstable_by(|a, b| b.cmp(&a));
				tmp
			},
		}
	}
}

impl Clone for RegisteredProtocol {
	fn clone(&self) -> Self {
		RegisteredProtocol {
			id: self.id.clone(),
			base_name: self.base_name.clone(),
			supported_versions: self.supported_versions.clone(),
		}
	}
}

/// Output of a `RegisteredProtocol` upgrade.
pub struct RegisteredProtocolSubstream<TSubstream> {
	/// If true, we are in the process of closing the sink.
	is_closing: bool,
	/// Whether the local node opened this substream (dialer), or we received this substream from
	/// the remote (listener).
	endpoint: Endpoint,
	/// Buffer of packets to send.
	send_queue: VecDeque<BytesMut>,
	/// If true, we should call `poll_complete` on the inner sink.
	requires_poll_flush: bool,
	/// The underlying substream.
	inner: stream::Fuse<Framed<TSubstream, UviBytes<BytesMut>>>,
	/// Version of the protocol that was negotiated.
	protocol_version: u8,
	/// If true, we have sent a "remote is clogged" event recently and shouldn't send another one
	/// unless the buffer empties then fills itself again.
	clogged_fuse: bool,
}

impl<TSubstream> RegisteredProtocolSubstream<TSubstream> {
	/// Returns the version of the protocol that was negotiated.
	pub fn protocol_version(&self) -> u8 {
		self.protocol_version
	}

	/// Returns whether the local node opened this substream (dialer), or we received this
	/// substream from the remote (listener).
	pub fn endpoint(&self) -> Endpoint {
		self.endpoint
	}

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

	/// Sends a message to the substream.
	pub fn send_message(&mut self, data: Vec<u8>) {
		if self.is_closing {
			return
		}

		self.send_queue.push_back(From::from(&data[..]));
	}
}

/// Event produced by the `RegisteredProtocolSubstream`.
#[derive(Debug, Clone)]
pub enum RegisteredProtocolEvent {
	/// Received a message from the remote.
	Message(BytesMut),

	/// Diagnostic event indicating that the connection is clogged and we should avoid sending too
	/// many messages to it.
	Clogged {
		/// Copy of the messages that are within the buffer, for further diagnostic.
		messages: Vec<Vec<u8>>,
	},
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
		if self.send_queue.len() >= 2048 {
			if !self.clogged_fuse {
				// Note: this fuse is important not just for preventing us from flooding the logs;
				// 	if you remove the fuse, then we will always return early from this function and
				//	thus never read any message from the network.
				self.clogged_fuse = true;
				return Poll::Ready(Some(Ok(RegisteredProtocolEvent::Clogged {
					messages: self.send_queue.iter()
						.map(|m| m.clone().to_vec())
						.collect(),
				})))
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
where TSubstream: AsyncRead + AsyncWrite + Unpin,
{
	type Output = RegisteredProtocolSubstream<TSubstream>;
	type Future = future::Ready<Result<Self::Output, io::Error>>;
	type Error = io::Error;

	fn upgrade_inbound(
		self,
		socket: TSubstream,
		info: Self::Info,
	) -> Self::Future {
		let framed = {
			let mut codec = UviBytes::default();
			codec.set_max_len(16 * 1024 * 1024);		// 16 MiB hard limit for packets.
			Framed::new(socket, codec)
		};

		future::ok(RegisteredProtocolSubstream {
			is_closing: false,
			endpoint: Endpoint::Listener,
			send_queue: VecDeque::new(),
			requires_poll_flush: false,
			inner: framed.fuse(),
			protocol_version: info.version,
			clogged_fuse: false,
		})
	}
}

impl<TSubstream> OutboundUpgrade<TSubstream> for RegisteredProtocol
where TSubstream: AsyncRead + AsyncWrite + Unpin,
{
	type Output = <Self as InboundUpgrade<TSubstream>>::Output;
	type Future = <Self as InboundUpgrade<TSubstream>>::Future;
	type Error = <Self as InboundUpgrade<TSubstream>>::Error;

	fn upgrade_outbound(
		self,
		socket: TSubstream,
		info: Self::Info,
	) -> Self::Future {
		let framed = Framed::new(socket, UviBytes::default());

		future::ok(RegisteredProtocolSubstream {
			is_closing: false,
			endpoint: Endpoint::Dialer,
			send_queue: VecDeque::new(),
			requires_poll_flush: false,
			inner: framed.fuse(),
			protocol_version: info.version,
			clogged_fuse: false,
		})
	}
}
