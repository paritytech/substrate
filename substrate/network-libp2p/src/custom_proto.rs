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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.?

use bytes::{Bytes, BytesMut};
use ProtocolId;
use libp2p::core::{Multiaddr, ConnectionUpgrade, Endpoint};
use PacketId;
use std::io::Error as IoError;
use std::vec::IntoIter as VecIntoIter;
use futures::{future, Future, stream, Stream, Sink};
use futures::sync::mpsc;
use tokio_io::{AsyncRead, AsyncWrite};
use varint::VarintCodec;

/// Connection upgrade for a single protocol.
///
/// Note that "a single protocol" here refers to `par` for example. However
/// each protocol can have multiple different versions for networking purposes.
#[derive(Clone)]
pub struct RegisteredProtocol<T> {
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
	custom_data: T,
}

/// Output of a `RegisteredProtocol` upgrade.
pub struct RegisteredProtocolOutput<T> {
	/// Data passed to `RegisteredProtocol::new`.
	pub custom_data: T,

	/// Id of the protocol.
	pub protocol_id: ProtocolId,

	/// Endpoint of the connection.
	pub endpoint: Endpoint,

	/// Version of the protocol that was negotiated.
	pub protocol_version: u8,

	/// Channel to sender outgoing messages to.
	// TODO: consider assembling packet_id here
	pub outgoing: mpsc::UnboundedSender<Bytes>,

	/// Stream where incoming messages are received. The stream ends whenever
	/// either side is closed.
	pub incoming: Box<Stream<Item = (PacketId, Bytes), Error = IoError>>,
}

impl<T> RegisteredProtocol<T> {
	/// Creates a new `RegisteredProtocol`. The `custom_data` parameter will be
	/// passed inside the `RegisteredProtocolOutput`.
	pub fn new(custom_data: T, protocol: ProtocolId, versions: &[(u8, u8)])
		-> Self {
		let mut proto_name = Bytes::from_static(b"/substrate/");
		proto_name.extend_from_slice(&protocol);
		proto_name.extend_from_slice(b"/");

		RegisteredProtocol {
			base_name: proto_name,
			id: protocol,
			supported_versions: {
				let mut tmp: Vec<_> = versions.iter().rev().cloned().collect();
				tmp.sort_unstable_by(|a, b| b.1.cmp(&a.1));
				tmp
			},
			custom_data: custom_data,
		}
	}

	/// Returns the ID of the protocol.
	pub fn id(&self) -> ProtocolId {
		self.id
	}

	/// Returns the custom data that was passed to `new`.
	pub fn custom_data(&self) -> &T {
		&self.custom_data
	}
}

// `Maf` is short for `MultiaddressFuture`
impl<T, C, Maf> ConnectionUpgrade<C, Maf> for RegisteredProtocol<T>
where C: AsyncRead + AsyncWrite + 'static,		// TODO: 'static :-/
	Maf: Future<Item = Multiaddr, Error = IoError> + 'static,		// TODO: 'static :(
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

	type Output = RegisteredProtocolOutput<T>;
	type MultiaddrFuture = Maf;
	type Future = future::FutureResult<(Self::Output, Self::MultiaddrFuture), IoError>;

	#[allow(deprecated)]
	fn upgrade(
		self,
		socket: C,
		protocol_version: Self::UpgradeIdentifier,
		endpoint: Endpoint,
		remote_addr: Maf
	) -> Self::Future {
		let packet_count = self.supported_versions
			.iter()
			.find(|&(v, _)| *v == protocol_version)
			.expect("negotiated protocol version that wasn't advertised ; \
				programmer error")
			.1;

		// This function is called whenever we successfully negotiated a
		// protocol with a remote (both if initiated by us or by the remote)

		// This channel is used to send outgoing packets to the custom_data
		// for this open substream.
		let (msg_tx, msg_rx) = mpsc::unbounded();

		// Build the sink for outgoing network bytes, and the stream for
		// incoming instructions. `stream` implements `Stream<Item = Message>`.
		enum Message {
			/// Received data from the network.
			RecvSocket(BytesMut),
			/// Data to send to the network.
			/// The packet_id must already be inside the `Bytes`.
			SendReq(Bytes),
			/// The socket has been closed.
			Finished,
		}

		let (sink, stream) = {
			let framed = AsyncRead::framed(socket, VarintCodec::default());
			let msg_rx = msg_rx.map(Message::SendReq)
				.map_err(|()| unreachable!("mpsc::UnboundedReceiver never errors"));
			let (sink, stream) = framed.split();
			let stream = stream.map(Message::RecvSocket)
				.chain(stream::once(Ok(Message::Finished)));
			(sink, msg_rx.select(stream))
		};

		let incoming = stream::unfold((sink, stream, false), move |(sink, stream, finished)| {
			if finished {
				return None
			}

			Some(stream
				.into_future()
				.map_err(|(err, _)| err)
				.and_then(move |(message, stream)|
					match message {
						Some(Message::RecvSocket(mut data)) => {
							// The `data` should be prefixed by the packet ID,
							// therefore an empty packet is invalid.
							if data.is_empty() {
								debug!(target: "sub-libp2p", "ignoring incoming \
									packet because it was empty");
								let f = future::ok((None, (sink, stream, false)));
								return future::Either::A(f)
							}

							let packet_id = data[0];
							let data = data.split_off(1);

							if packet_id >= packet_count {
								debug!(target: "sub-libp2p", "ignoring incoming packet \
									because packet_id {} is too large", packet_id);
								let f = future::ok((None, (sink, stream, false)));
								future::Either::A(f)
							} else {
								let out = Some((packet_id, data.freeze()));
								let f = future::ok((out, (sink, stream, false)));
								future::Either::A(f)
							}
						},

						Some(Message::SendReq(data)) => {
							let fut = sink.send(data)
								.map(move |sink| (None, (sink, stream, false)));
							future::Either::B(fut)
						},

						Some(Message::Finished) | None => {
							let f = future::ok((None, (sink, stream, true)));
							future::Either::A(f)
						},
					}
				))
		}).filter_map(|v| v);

		let out = RegisteredProtocolOutput {
			custom_data: self.custom_data,
			protocol_id: self.id,
			endpoint,
			protocol_version: protocol_version,
			outgoing: msg_tx,
			incoming: Box::new(incoming),
		};

		future::ok((out, remote_addr))
	}
}

// Connection upgrade for all the protocols contained in it.
#[derive(Clone)]
pub struct RegisteredProtocols<T>(pub Vec<RegisteredProtocol<T>>);

impl<T> RegisteredProtocols<T> {
	/// Finds a protocol in the list by its id.
	pub fn find_protocol(&self, protocol: ProtocolId)
		-> Option<&RegisteredProtocol<T>> {
		self.0.iter().find(|p| p.id == protocol)
	}

	/// Returns true if the given protocol is in the list.
	pub fn has_protocol(&self, protocol: ProtocolId) -> bool {
		self.0.iter().any(|p| p.id == protocol)
	}
}

impl<T> Default for RegisteredProtocols<T> {
	fn default() -> Self {
		RegisteredProtocols(Vec::new())
	}
}

impl<T, C, Maf> ConnectionUpgrade<C, Maf> for RegisteredProtocols<T>
where C: AsyncRead + AsyncWrite + 'static,		// TODO: 'static :-/
	Maf: Future<Item = Multiaddr, Error = IoError> + 'static,		// TODO: 'static :(
{
	type NamesIter = VecIntoIter<(Bytes, Self::UpgradeIdentifier)>;
	type UpgradeIdentifier = (usize,
		<RegisteredProtocol<T> as ConnectionUpgrade<C, Maf>>::UpgradeIdentifier);

	fn protocol_names(&self) -> Self::NamesIter {
		// We concat the lists of `RegisteredProtocol::protocol_names` for
		// each protocol.
		self.0.iter().enumerate().flat_map(|(n, proto)|
			ConnectionUpgrade::<C, Maf>::protocol_names(proto)
				.map(move |(name, id)| (name, (n, id)))
		).collect::<Vec<_>>().into_iter()
	}

	type Output = <RegisteredProtocol<T> as ConnectionUpgrade<C, Maf>>::Output;
	type MultiaddrFuture = <RegisteredProtocol<T> as
		ConnectionUpgrade<C, Maf>>::MultiaddrFuture;
	type Future = <RegisteredProtocol<T> as ConnectionUpgrade<C, Maf>>::Future;

	#[inline]
	fn upgrade(
		self,
		socket: C,
		upgrade_identifier: Self::UpgradeIdentifier,
		endpoint: Endpoint,
		remote_addr: Maf
	) -> Self::Future {
		let (protocol_index, inner_proto_id) = upgrade_identifier;
		self.0.into_iter()
			.nth(protocol_index)
			.expect("invalid protocol index ; programmer logic error")
			.upgrade(socket, inner_proto_id, endpoint, remote_addr)
	}
}
