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

use bytes::{Bytes, BytesMut};
use libp2p::core::{Multiaddr, ConnectionUpgrade, Endpoint};
use libp2p::tokio_codec::Framed;
use std::collections::VecDeque;
use std::io::Error as IoError;
use std::vec::IntoIter as VecIntoIter;
use futures::{prelude::*, future, stream, task};
use tokio_io::{AsyncRead, AsyncWrite};
use unsigned_varint::codec::UviBytes;
use ProtocolId;

/// Connection upgrade for a single protocol.
///
/// Note that "a single protocol" here refers to `par` for example. However
/// each protocol can have multiple different versions for networking purposes.
#[derive(Clone)]
pub struct RegisteredProtocol<TUserData> {
	/// Id of the protocol for API purposes.
	id: ProtocolId,
	/// Base name of the protocol as advertised on the network.
	/// Ends with `/` so that we can append a version number behind.
	base_name: Bytes,
	/// List of protocol versions that we support, plus their packet count.
	/// Ordered in descending order so that the best comes first.
	/// The packet count is used to filter out invalid messages.
	supported_versions: Vec<(u8, u8)>,
	/// Custom data.
	custom_data: TUserData,
}

impl<TUserData> RegisteredProtocol<TUserData> {
	/// Creates a new `RegisteredProtocol`. The `custom_data` parameter will be
	/// passed inside the `RegisteredProtocolOutput`.
	pub fn new(custom_data: TUserData, protocol: ProtocolId, versions: &[(u8, u8)])
		-> Self {
		let mut base_name = Bytes::from_static(b"/substrate/");
		base_name.extend_from_slice(&protocol);
		base_name.extend_from_slice(b"/");

		RegisteredProtocol {
			base_name,
			id: protocol,
			supported_versions: {
				let mut tmp: Vec<_> = versions.iter().rev().cloned().collect();
				tmp.sort_unstable_by(|a, b| b.1.cmp(&a.1));
				tmp
			},
			custom_data,
		}
	}

	/// Returns the ID of the protocol.
	#[inline]
	pub fn id(&self) -> ProtocolId {
		self.id
	}

	/// Returns the custom data that was passed to `new`.
	#[inline]
	pub fn custom_data(&self) -> &TUserData {
		&self.custom_data
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
	/// Maximum packet id.
	packet_count: u8,
	/// Id of the protocol.
	protocol_id: ProtocolId,
	/// Version of the protocol that was negotiated.
	protocol_version: u8,
	/// Task to notify when something is changed and we need to be polled.
	to_notify: Option<task::Task>,
}

/// Packet of data that can be sent or received.
#[derive(Debug, Clone)]
pub struct Packet {
	/// Identifier of the packet.
	pub id: u8,
	/// The raw data.
	pub data: Bytes,
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
		if let Some(task) = self.to_notify.take() {
			task.notify();
		}
	}

	/// Sends a message to the substream.
	pub fn send_message(&mut self, Packet { id: packet_id, data }: Packet) {
		if packet_id >= self.packet_count {
			error!(target: "sub-libp2p", "Tried to send a packet with an invalid ID {}", packet_id);
			return;
		}

		let mut message = Bytes::with_capacity(1 + data.len());
		message.extend_from_slice(&[packet_id]);
		message.extend_from_slice(&data);
		self.send_queue.push_back(message);

		// If the length of the queue goes over a certain arbitrary threshold, we print a warning.
		// TODO: figure out a good threshold
		if self.send_queue.len() >= 2048 {
			warn!(target: "sub-libp2p", "Queue of packets to send over substream is pretty \
				large: {}", self.send_queue.len());
		}

		if let Some(task) = self.to_notify.take() {
			task.notify();
		}
	}

	/// Turns raw data into a packet and checks whether it is valid.
	fn data_to_packet(&self, mut data: BytesMut) -> Result<Packet, ()> {
		// The `data` should be prefixed by the packet ID, therefore an empty packet is invalid.
		if data.is_empty() {
			debug!(target: "sub-libp2p", "ignoring incoming packet because it was empty");
			return Err(());
		}

		let packet = {
			let id = data[0];
			let data = data.split_off(1);
			Packet { id, data: data.freeze() }
		};

		if packet.id >= self.packet_count {
			debug!(target: "sub-libp2p", "ignoring incoming packet because packet_id {} is \
				too large", packet.id);
			return Err(())
		}

		Ok(packet)
	}
}

impl<TSubstream> Stream for RegisteredProtocolSubstream<TSubstream>
where TSubstream: AsyncRead + AsyncWrite,
{
	type Item = Packet;
	type Error = IoError;

	fn poll(&mut self) -> Poll<Option<Self::Item>, Self::Error> {
		// If we are closing, close as soon as the Sink is closed.
		if self.is_closing {
			return Ok(self.inner.close()?.map(|()| None));
		}

		// Flushing the local queue.
		while let Some(packet) = self.send_queue.pop_front() {
			match self.inner.start_send(packet)? {
				AsyncSink::NotReady(packet) => {
					self.send_queue.push_front(packet);
					break;
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
		loop {
			match self.inner.poll()? {
				Async::Ready(Some(data)) =>
					if let Ok(packet) = self.data_to_packet(data) {
						return Ok(Async::Ready(Some(packet)))
					},
				Async::Ready(None) =>
					if !self.requires_poll_complete && self.send_queue.is_empty() {
						return Ok(Async::Ready(None))
					} else {
						break
					},
				Async::NotReady => break,
			}
		}

		self.to_notify = Some(task::current());
		Ok(Async::NotReady)
	}
}

impl<TSubstream, TUserData> ConnectionUpgrade<TSubstream> for RegisteredProtocol<TUserData>
where TSubstream: AsyncRead + AsyncWrite,
	  TUserData: Clone,
{
	type NamesIter = VecIntoIter<(Bytes, Self::UpgradeIdentifier)>;
	type UpgradeIdentifier = u8;		// Protocol version

	#[inline]
	fn protocol_names(&self) -> Self::NamesIter {
		// Report each version as an individual protocol.
		self.supported_versions.iter().map(|&(ver, _)| {
			let num = ver.to_string();
			let mut name = self.base_name.clone();
			name.extend_from_slice(num.as_bytes());
			(name, ver)
		}).collect::<Vec<_>>().into_iter()
	}

	type Output = RegisteredProtocolSubstream<TSubstream>;
	type Future = future::FutureResult<Self::Output, IoError>;

	#[allow(deprecated)]
	fn upgrade(
		self,
		socket: TSubstream,
		protocol_version: Self::UpgradeIdentifier,
		_: Endpoint,
		_: &Multiaddr
	) -> Self::Future {
		let packet_count = self.supported_versions
			.iter()
			.find(|&(v, _)| *v == protocol_version)
			.expect("negotiated protocol version that wasn't advertised ; \
				programmer error")
			.1;
		
		let framed = Framed::new(socket, UviBytes::default());

		future::ok(RegisteredProtocolSubstream {
			is_closing: false,
			send_queue: VecDeque::new(),
			requires_poll_complete: false,
			inner: framed.fuse(),
			packet_count,
			protocol_id: self.id,
			protocol_version,
			to_notify: None,
		})
	}
}

// Connection upgrade for all the protocols contained in it.
#[derive(Clone)]
pub struct RegisteredProtocols<TUserData>(pub Vec<RegisteredProtocol<TUserData>>);

impl<TUserData> RegisteredProtocols<TUserData> {
	/// Returns the number of protocols.
	#[inline]
	pub fn len(&self) -> usize {
		self.0.len()
	}

	/// Finds a protocol in the list by its id.
	pub fn find_protocol(&self, protocol: ProtocolId)
		-> Option<&RegisteredProtocol<TUserData>> {
		self.0.iter().find(|p| p.id == protocol)
	}

	/// Returns true if the given protocol is in the list.
	pub fn has_protocol(&self, protocol: ProtocolId) -> bool {
		self.0.iter().any(|p| p.id == protocol)
	}
}

impl<TUserData> Default for RegisteredProtocols<TUserData> {
	fn default() -> Self {
		RegisteredProtocols(Vec::new())
	}
}

impl<TSubstream, TUserData> ConnectionUpgrade<TSubstream> for RegisteredProtocols<TUserData>
where TSubstream: AsyncRead + AsyncWrite,
	  TUserData: Clone,
{
	type NamesIter = VecIntoIter<(Bytes, Self::UpgradeIdentifier)>;
	type UpgradeIdentifier = (usize,
		<RegisteredProtocol<TUserData> as ConnectionUpgrade<TSubstream>>::UpgradeIdentifier);

	fn protocol_names(&self) -> Self::NamesIter {
		// We concat the lists of `RegisteredProtocol::protocol_names` for
		// each protocol.
		self.0.iter().enumerate().flat_map(|(n, proto)|
			ConnectionUpgrade::<TSubstream>::protocol_names(proto)
				.map(move |(name, id)| (name, (n, id)))
		).collect::<Vec<_>>().into_iter()
	}

	type Output = <RegisteredProtocol<TUserData> as ConnectionUpgrade<TSubstream>>::Output;
	type Future = <RegisteredProtocol<TUserData> as ConnectionUpgrade<TSubstream>>::Future;

	#[inline]
	fn upgrade(
		self,
		socket: TSubstream,
		upgrade_identifier: Self::UpgradeIdentifier,
		endpoint: Endpoint,
		remote_addr: &Multiaddr
	) -> Self::Future {
		let (protocol_index, inner_proto_id) = upgrade_identifier;
		self.0.into_iter()
			.nth(protocol_index)
			.expect("invalid protocol index ; programmer logic error")
			.upgrade(socket, inner_proto_id, endpoint, remote_addr)
	}
}
