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

use crate::ProtocolId;
use crate::custom_proto::upgrade::{RegisteredProtocol, RegisteredProtocols, RegisteredProtocolSubstream, RegisteredProtocolEvent};
use bytes::Bytes;
use futures::prelude::*;
use libp2p::core::{
	Endpoint, ProtocolsHandler, ProtocolsHandlerEvent,
	protocols_handler::ProtocolsHandlerUpgrErr,
	upgrade::{InboundUpgrade, OutboundUpgrade}
};
use log::{trace, warn};
use smallvec::SmallVec;
use std::{fmt, io};
use tokio_io::{AsyncRead, AsyncWrite};
use void::Void;

/// Protocol handler that tries to maintain one substream per registered custom protocol.
///
/// The handler initially starts in the "Disable" state. It can then be enabled by sending an
/// `Enable` message.
/// The handler can then be enabled and disabled at any time with the `Enable` and `Disable`
/// messages.
pub struct CustomProtosHandler<TSubstream> {
	/// List of all the protocols we support.
	protocols: RegisteredProtocols,

	/// See the documentation of `State`.
	state: State,

	/// The active substreams. There should always ever be only one substream per protocol.
	substreams: SmallVec<[RegisteredProtocolSubstream<TSubstream>; 6]>,

	/// Queue of events to send to the outside.
	events_queue: SmallVec<[ProtocolsHandlerEvent<RegisteredProtocol, (), CustomProtosHandlerOut>; 16]>,
}

/// State of the handler.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum State {
	/// Normal functionning.
	Normal,

	/// We are disabled. We close existing substreams and refuse incoming connections, but don't
	/// shut down the entire handler.
	Disabled,

	/// We are trying to shut down the existing node and thus should refuse any incoming
	/// connection.
	ShuttingDown,
}

/// Event that can be received by a `CustomProtosHandler`.
#[derive(Debug)]
pub enum CustomProtosHandlerIn {
	/// The node should start using custom protocols and actively open substreams.
	EnableActive,

	/// The node should listen to custom protocols but not open substreams.
	EnablePassive,

	/// The node should stop using custom protocols.
	Disable,

	/// Sends a message through a custom protocol substream.
	SendCustomMessage {
		/// The protocol to use.
		protocol: ProtocolId,
		/// The data to send.
		data: Bytes,
	},
}

/// Event that can be emitted by a `CustomProtosHandler`.
#[derive(Debug)]
pub enum CustomProtosHandlerOut {
	/// Opened a custom protocol with the remote.
	CustomProtocolOpen {
		/// Identifier of the protocol.
		protocol_id: ProtocolId,
		/// Version of the protocol that has been opened.
		version: u8,
	},

	/// Closed a custom protocol with the remote.
	CustomProtocolClosed {
		/// Identifier of the protocol.
		protocol_id: ProtocolId,
		/// Reason why the substream closed. If `Ok`, then it's a graceful exit (EOF).
		result: io::Result<()>,
	},

	/// Receives a message on a custom protocol substream.
	CustomMessage {
		/// Protocol which generated the message.
		protocol_id: ProtocolId,
		/// Data that has been received.
		data: Bytes,
	},

	/// A substream to the remote is clogged. The send buffer is very large, and we should print
	/// a diagnostic message and/or avoid sending more data.
	Clogged {
		/// Protocol which is clogged.
		protocol_id: ProtocolId,
		/// Copy of the messages that are within the buffer, for further diagnostic.
		messages: Vec<Bytes>,
	},
}

impl<TSubstream> CustomProtosHandler<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
{
	/// Builds a new `CustomProtosHandler`.
	pub fn new(protocols: RegisteredProtocols) -> Self {
		CustomProtosHandler {
			protocols,
			state: State::Disabled,
			substreams: SmallVec::new(),
			events_queue: SmallVec::new(),
		}
	}

	/// Called by `inject_fully_negotiated_inbound` and `inject_fully_negotiated_outbound`.
	fn inject_fully_negotiated(
		&mut self,
		proto: RegisteredProtocolSubstream<TSubstream>,
		_: Endpoint,
	) {
		match self.state {
			State::Disabled | State::ShuttingDown => return,
			State::Normal => ()
		}

		if self.substreams.iter().any(|p| p.protocol_id() == proto.protocol_id()) {
			// Skipping protocol that's already open.
			return
		}

		let event = CustomProtosHandlerOut::CustomProtocolOpen {
			protocol_id: proto.protocol_id(),
			version: proto.protocol_version(),
		};

		self.substreams.push(proto);
		self.events_queue.push(ProtocolsHandlerEvent::Custom(event));
	}
}

impl<TSubstream> ProtocolsHandler for CustomProtosHandler<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
{
	type InEvent = CustomProtosHandlerIn;
	type OutEvent = CustomProtosHandlerOut;
	type Substream = TSubstream;
	type Error = Void;
	type InboundProtocol = RegisteredProtocols;
	type OutboundProtocol = RegisteredProtocol;
	type OutboundOpenInfo = ();

	#[inline]
	fn listen_protocol(&self) -> Self::InboundProtocol {
		self.protocols.clone()
	}

	fn inject_fully_negotiated_inbound(
		&mut self,
		proto: <Self::InboundProtocol as InboundUpgrade<TSubstream>>::Output
	) {
		self.inject_fully_negotiated(proto, Endpoint::Listener);
	}

	#[inline]
	fn inject_fully_negotiated_outbound(
		&mut self,
		proto: <Self::OutboundProtocol as OutboundUpgrade<TSubstream>>::Output,
		_: Self::OutboundOpenInfo
	) {
		self.inject_fully_negotiated(proto, Endpoint::Dialer);
	}

	fn inject_event(&mut self, message: CustomProtosHandlerIn) {
		match message {
			CustomProtosHandlerIn::Disable => {
				match self.state {
					State::Normal => self.state = State::Disabled,
					State::Disabled | State::ShuttingDown => (),
				}

				for substream in self.substreams.iter_mut() {
					substream.shutdown();
				}
			},
			CustomProtosHandlerIn::EnableActive | CustomProtosHandlerIn::EnablePassive => {
				match self.state {
					State::Disabled => self.state = State::Normal,
					State::Normal | State::ShuttingDown => (),
				}

				// Try open one substream for each registered protocol.
				if let CustomProtosHandlerIn::EnableActive = message {
					for protocol in self.protocols.0.iter() {
						if self.substreams.iter().any(|p| p.protocol_id() == protocol.id()) {
							// Skipping protocol that's already open.
							continue
						}

						self.events_queue.push(ProtocolsHandlerEvent::OutboundSubstreamRequest {
							upgrade: protocol.clone(),
							info: (),
						});
					}
				}
			},
			CustomProtosHandlerIn::SendCustomMessage { protocol, data } => {
				debug_assert!(self.protocols.has_protocol(protocol),
					"invalid protocol id requested in the API of the libp2p networking");
				let proto = match self.substreams.iter_mut().find(|p| p.protocol_id() == protocol) {
					Some(proto) => proto,
					None => {
						// We are processing a message event before we could report to the outside
						// that we disconnected from the protocol. This is not an error.
						trace!(target: "sub-libp2p", "Tried to send message through closed \
							protocol");
						return
					},
				};

				proto.send_message(data);
			},
		}
	}

	#[inline]
	fn inject_inbound_closed(&mut self) {}

	#[inline]
	fn inject_dial_upgrade_error(&mut self, _: Self::OutboundOpenInfo, err: ProtocolsHandlerUpgrErr<io::Error>) {
		warn!(target: "sub-libp2p", "Error while opening custom protocol: {:?}", err);
	}

	#[inline]
	fn connection_keep_alive(&self) -> bool {
		// Right now if the remote doesn't support one of the custom protocols, we shut down the
		// entire connection. This is a hack-ish solution to the problem where we connect to nodes
		// that support libp2p but not the testnet that we want.
		self.substreams.len() == self.protocols.len()
	}

	fn shutdown(&mut self) {
		match self.state {
			State::Normal | State::Disabled => self.state = State::ShuttingDown,
			State::ShuttingDown => (),
		}

		for substream in self.substreams.iter_mut() {
			substream.shutdown();
		}
	}

	fn poll(
		&mut self,
	) -> Poll<
		ProtocolsHandlerEvent<Self::OutboundProtocol, Self::OutboundOpenInfo, Self::OutEvent>,
		Self::Error,
	> {
		if !self.events_queue.is_empty() {
			let event = self.events_queue.remove(0);
			return Ok(Async::Ready(event))
		}

		if self.state == State::ShuttingDown && self.substreams.is_empty() {
			return Ok(Async::Ready(ProtocolsHandlerEvent::Shutdown))
		}

		for n in (0..self.substreams.len()).rev() {
			let mut substream = self.substreams.swap_remove(n);
			match substream.poll() {
				Ok(Async::Ready(Some(RegisteredProtocolEvent::Message(data)))) => {
					let event = CustomProtosHandlerOut::CustomMessage {
						protocol_id: substream.protocol_id(),
						data
					};
					self.substreams.push(substream);
					return Ok(Async::Ready(ProtocolsHandlerEvent::Custom(event)))
				},
				Ok(Async::Ready(Some(RegisteredProtocolEvent::Clogged { messages }))) => {
					let event = CustomProtosHandlerOut::Clogged {
						protocol_id: substream.protocol_id(),
						messages,
					};
					self.substreams.push(substream);
					return Ok(Async::Ready(ProtocolsHandlerEvent::Custom(event)))
				},
				Ok(Async::NotReady) =>
					self.substreams.push(substream),
				Ok(Async::Ready(None)) => {
					let event = CustomProtosHandlerOut::CustomProtocolClosed {
						protocol_id: substream.protocol_id(),
						result: Ok(())
					};
					return Ok(Async::Ready(ProtocolsHandlerEvent::Custom(event)))
				},
				Err(err) => {
					let event = CustomProtosHandlerOut::CustomProtocolClosed {
						protocol_id: substream.protocol_id(),
						result: Err(err)
					};
					return Ok(Async::Ready(ProtocolsHandlerEvent::Custom(event)))
				},
			}
		}

		Ok(Async::NotReady)
	}
}

impl<TSubstream> fmt::Debug for CustomProtosHandler<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
{
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
		f.debug_struct("CustomProtosHandler")
			.field("protocols", &self.protocols.len())
			.field("state", &self.state)
			.field("substreams", &self.substreams.len())
			.finish()
	}
}
