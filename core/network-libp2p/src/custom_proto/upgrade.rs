// Copyright 2018 Parity Technologies (UK) Ltd.
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

use bytes::Bytes;
use libp2p::core::{UpgradeInfo, InboundUpgrade, OutboundUpgrade, upgrade::ProtocolName};
use libp2p::tokio_codec::Framed;
use std::{collections::VecDeque, io, vec::IntoIter as VecIntoIter};
use futures::{prelude::*, future, stream};
use tokio_io::{AsyncRead, AsyncWrite};
use unsigned_varint::codec::UviBytes;
use ProtocolId;

/// Connection upgrade for a single protocol.
///
/// Note that "a single protocol" here refers to `par` for example. However
/// each protocol can have multiple different versions for networking purposes.
#[derive(Clone)]
pub struct RegisteredProtocol {
	/// Id of the protocol for API purposes.
	id: ProtocolId,
	/// Base name of the protocol as advertised on the network.
	/// Ends with `/` so that we can append a version number behind.
	base_name: Bytes,
	/// List of protocol versions that we support.
	/// Ordered in descending order so that the best comes first.
	supported_versions: Vec<u8>,
}

impl RegisteredProtocol {
	/// Creates a new `RegisteredProtocol`. The `custom_data` parameter will be
	/// passed inside the `RegisteredProtocolOutput`.
	pub fn new(protocol: ProtocolId, versions: &[u8])
		-> Self {
		let mut base_name = Bytes::from_static(b"/substrate/");
		base_name.extend_from_slice(&protocol);
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

	/// Returns the ID of the protocol.
	#[inline]
	pub fn id(&self) -> ProtocolId {
		self.id
	}
}

/// Output of a `RegisteredProtocol` upgrade.
pub struct RegisteredProtocolSubstream<TSubstream> {
	/// If true, we are in the process of closing the sink.
	is_closing: bool,
	/// Buffer of packets to send.
	send_queue: VecDeque<Bytes>,
	/// If true, we should call `poll_complete` on the inner sink.
	requires_poll_complete: bool,
	/// The underlying substream.
	inner: stream::Fuse<Framed<TSubstream, UviBytes<Bytes>>>,
	/// Id of the protocol.
	protocol_id: ProtocolId,
	/// Version of the protocol that was negotiated.
	protocol_version: u8,
}

impl<TSubstream> RegisteredProtocolSubstream<TSubstream> {
	/// Returns the protocol id.
	#[inline]
	pub fn protocol_id(&self) -> ProtocolId {
		self.protocol_id
	}

	/// Returns the version of the protocol that was negotiated.
	#[inline]
	pub fn protocol_version(&self) -> u8 {
		self.protocol_version
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
	pub fn send_message(&mut self, data: Bytes) {
		if self.is_closing {
			return
		}

		self.send_queue.push_back(data);

		// If the length of the queue goes over a certain arbitrary threshold, we print a warning.
		if self.send_queue.len() >= 2048 {
			// TODO: this used to be a warning, but is now a `debug` in order to avoid too much
			//	noise in the logs; see https://github.com/paritytech/substrate/issues/1414
			debug!(target: "sub-libp2p", "Queue of packets to send over substream is pretty \
				large: {}", self.send_queue.len());
		}
	}
}

impl<TSubstream> Stream for RegisteredProtocolSubstream<TSubstream>
where TSubstream: AsyncRead + AsyncWrite,
{
	type Item = Bytes;
	type Error = io::Error;

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		// If we are closing, close as soon as the Sink is closed.
		if self.is_closing {
			return Ok(self.inner.close()?.map(|()| None))
		}

		// Flushing the local queue.
		while let Some(packet) = self.send_queue.pop_front() {
			match self.inner.start_send(packet)? {
				AsyncSink::NotReady(packet) => {
					self.send_queue.push_front(packet);
					break
				},
				AsyncSink::Ready => self.requires_poll_complete = true,
			}
		}

		// Flushing if necessary.
		if self.requires_poll_complete {
			if let Async::Ready(()) = self.inner.poll_complete()? {
				self.requires_poll_complete = false;
			}
		}

		// Receiving incoming packets.
		// Note that `inner` is wrapped in a `Fuse`, therefore we can poll it forever.
		match self.inner.poll()? {
			Async::Ready(Some(data)) => Ok(Async::Ready(Some(data.freeze()))),
			Async::Ready(None) =>
				if !self.requires_poll_complete && self.send_queue.is_empty() {
					Ok(Async::Ready(None))
				} else {
					Ok(Async::NotReady)
				},
			Async::NotReady => Ok(Async::NotReady),
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
	name: Bytes,
	/// Version number. Stored in string form in `name`, but duplicated here for easier retrieval.
	version: u8,
}

impl ProtocolName for RegisteredProtocolName {
	fn protocol_name(&self) -> &[u8] {
		&self.name
	}
}

impl<TSubstream> InboundUpgrade<TSubstream> for RegisteredProtocol
where TSubstream: AsyncRead + AsyncWrite,
{
	type Output = RegisteredProtocolSubstream<TSubstream>;
	type Future = future::FutureResult<Self::Output, io::Error>;
	type Error = io::Error;

	fn upgrade_inbound(
		self,
		socket: TSubstream,
		info: Self::Info,
	) -> Self::Future {
		let framed = Framed::new(socket, UviBytes::default());

		future::ok(RegisteredProtocolSubstream {
			is_closing: false,
			send_queue: VecDeque::new(),
			requires_poll_complete: false,
			inner: framed.fuse(),
			protocol_id: self.id,
			protocol_version: info.version,
		})
	}
}

impl<TSubstream> OutboundUpgrade<TSubstream> for RegisteredProtocol
where TSubstream: AsyncRead + AsyncWrite,
{
	type Output = <Self as InboundUpgrade<TSubstream>>::Output;
	type Future = <Self as InboundUpgrade<TSubstream>>::Future;
	type Error = <Self as InboundUpgrade<TSubstream>>::Error;

	fn upgrade_outbound(
		self,
		socket: TSubstream,
		info: Self::Info,
	) -> Self::Future {
		// Upgrades are symmetrical.
		self.upgrade_inbound(socket, info)
	}
}

// Connection upgrade for all the protocols contained in it.
#[derive(Clone)]
pub struct RegisteredProtocols(pub Vec<RegisteredProtocol>);

impl RegisteredProtocols {
	/// Returns the number of protocols.
	#[inline]
	pub fn len(&self) -> usize {
		self.0.len()
	}

	/// Returns true if the given protocol is in the list.
	pub fn has_protocol(&self, protocol: ProtocolId) -> bool {
		self.0.iter().any(|p| p.id == protocol)
	}
}

impl Default for RegisteredProtocols {
	fn default() -> Self {
		RegisteredProtocols(Vec::new())
	}
}

impl UpgradeInfo for RegisteredProtocols {
	type Info = RegisteredProtocolsName;
	type InfoIter = VecIntoIter<Self::Info>;

	#[inline]
	fn protocol_info(&self) -> Self::InfoIter {
		// We concat the lists of `RegisteredProtocol::protocol_names` for
		// each protocol.
		self.0.iter().enumerate().flat_map(|(n, proto)|
			UpgradeInfo::protocol_info(proto)
				.map(move |inner| {
					RegisteredProtocolsName {
						inner,
						index: n,
					}
				})
		).collect::<Vec<_>>().into_iter()
	}
}

/// Implementation of `ProtocolName` for several custom protocols.
#[derive(Debug, Clone)]
pub struct RegisteredProtocolsName {
	/// Inner registered protocol.
	inner: RegisteredProtocolName,
	/// Index of the protocol in the list of registered custom protocols.
	index: usize,
}

impl ProtocolName for RegisteredProtocolsName {
	fn protocol_name(&self) -> &[u8] {
		self.inner.protocol_name()
	}
}

impl<TSubstream> InboundUpgrade<TSubstream> for RegisteredProtocols
where TSubstream: AsyncRead + AsyncWrite,
{
	type Output = <RegisteredProtocol as InboundUpgrade<TSubstream>>::Output;
	type Future = <RegisteredProtocol as InboundUpgrade<TSubstream>>::Future;
	type Error = io::Error;

	#[inline]
	fn upgrade_inbound(
		self,
		socket: TSubstream,
		info: Self::Info,
	) -> Self::Future {
		self.0.into_iter()
			.nth(info.index)
			.expect("invalid protocol index ; programmer logic error")
			.upgrade_inbound(socket, info.inner)
	}
}

impl<TSubstream> OutboundUpgrade<TSubstream> for RegisteredProtocols
where TSubstream: AsyncRead + AsyncWrite,
{
	type Output = <Self as InboundUpgrade<TSubstream>>::Output;
	type Future = <Self as InboundUpgrade<TSubstream>>::Future;
	type Error = <Self as InboundUpgrade<TSubstream>>::Error;

	#[inline]
	fn upgrade_outbound(
		self,
		socket: TSubstream,
		info: Self::Info,
	) -> Self::Future {
		// Upgrades are symmetrical.
		self.upgrade_inbound(socket, info)
	}
}
