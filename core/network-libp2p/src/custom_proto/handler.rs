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
use crate::custom_proto::upgrade::{CustomMessage, RegisteredProtocol, RegisteredProtocols};
use crate::custom_proto::upgrade::{RegisteredProtocolSubstream, RegisteredProtocolEvent};
use futures::prelude::*;
use libp2p::core::{
	ProtocolsHandler, ProtocolsHandlerEvent,
	protocols_handler::KeepAlive,
	protocols_handler::ProtocolsHandlerUpgrErr,
	upgrade::{InboundUpgrade, OutboundUpgrade}
};
use log::trace;
use smallvec::SmallVec;
use std::{fmt, io, time::Duration, time::Instant};
use tokio_io::{AsyncRead, AsyncWrite};
use void::Void;

/// Protocol handler that tries to maintain one substream per registered custom protocol.
///
/// The handler initially starts in the "Disable" state. It can then be enabled by sending an
/// `Enable` message.
/// The handler can then be enabled and disabled at any time with the `Enable` and `Disable`
/// messages.
pub struct CustomProtosHandler<TMessage, TSubstream> {
	/// List of all the protocols we support.
	protocols: RegisteredProtocols<TMessage>,

	/// See the documentation of `State`.
	state: State<TMessage, TSubstream>,

	/// Value to be returned by `connection_keep_alive()`.
	keep_alive: KeepAlive,

	/// The active substreams. There should always ever be only one substream per protocol.
	substreams: SmallVec<[RegisteredProtocolSubstream<TMessage, TSubstream>; 6]>,

	/// Queue of events to send to the outside.
	events_queue: SmallVec<[ProtocolsHandlerEvent<RegisteredProtocol<TMessage>, ProtocolId, CustomProtosHandlerOut<TMessage>>; 16]>,
}

/// State of the handler.
enum State<TMessage, TSubstream> {
	/// Waiting for the behaviour to tell the handler whether it is enabled or disabled.
	/// Contains a list of substreams opened by the remote and that we will integrate to
	/// `substreams` only if we get enabled.
	Init(SmallVec<[RegisteredProtocolSubstream<TMessage, TSubstream>; 6]>),

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
pub enum CustomProtosHandlerIn<TMessage> {
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
		/// The message to send.
		message: TMessage,
	},
}

/// Event that can be emitted by a `CustomProtosHandler`.
#[derive(Debug)]
pub enum CustomProtosHandlerOut<TMessage> {
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
		/// Message that has been received.
		message: TMessage,
	},

	/// A substream to the remote is clogged. The send buffer is very large, and we should print
	/// a diagnostic message and/or avoid sending more data.
	Clogged {
		/// Protocol which is clogged.
		protocol_id: ProtocolId,
		/// Copy of the messages that are within the buffer, for further diagnostic.
		messages: Vec<TMessage>,
	},

	/// An error has happened on the protocol level with this node.
	ProtocolError {
		/// Protocol for which the error happened.
		protocol_id: ProtocolId,
		/// The error that happened.
		error: ProtocolsHandlerUpgrErr<io::Error>,
	},
}

impl<TMessage, TSubstream> CustomProtosHandler<TMessage, TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
{
	/// Builds a new `CustomProtosHandler`.
	pub fn new(protocols: RegisteredProtocols<TMessage>) -> Self {
		CustomProtosHandler {
			protocols,
			// We keep the connection alive for at least 5 seconds, waiting for what happens.
			keep_alive: KeepAlive::Until(Instant::now() + Duration::from_secs(5)),
			state: State::Init(SmallVec::new()),
			substreams: SmallVec::new(),
			events_queue: SmallVec::new(),
		}
	}

	/// Called by `inject_fully_negotiated_inbound` and `inject_fully_negotiated_outbound`.
	fn inject_fully_negotiated(
		&mut self,
		proto: RegisteredProtocolSubstream<TMessage, TSubstream>,
	) {
		if self.substreams.iter().any(|p| p.protocol_id() == proto.protocol_id()) {
			// Skipping protocol that's already open.
			return
		}

		match self.state {
			State::Init(ref mut pending) => {
				if pending.iter().all(|p| p.protocol_id() != proto.protocol_id()) {
					pending.push(proto);
				}
				return
			},
			// TODO: we should shut down refused substreams gracefully; this should be fixed
			// at the same time as https://github.com/paritytech/substrate/issues/1517
			State::Disabled | State::ShuttingDown => return,
			State::Normal => ()
		}

		let event = CustomProtosHandlerOut::CustomProtocolOpen {
			protocol_id: proto.protocol_id(),
			version: proto.protocol_version(),
		};

		self.keep_alive = KeepAlive::Forever;

		self.substreams.push(proto);
		self.events_queue.push(ProtocolsHandlerEvent::Custom(event));
	}
}

impl<TMessage, TSubstream> ProtocolsHandler for CustomProtosHandler<TMessage, TSubstream>
where TSubstream: AsyncRead + AsyncWrite, TMessage: CustomMessage {
	type InEvent = CustomProtosHandlerIn<TMessage>;
	type OutEvent = CustomProtosHandlerOut<TMessage>;
	type Substream = TSubstream;
	type Error = Void;
	type InboundProtocol = RegisteredProtocols<TMessage>;
	type OutboundProtocol = RegisteredProtocol<TMessage>;
	type OutboundOpenInfo = ProtocolId;

	#[inline]
	fn listen_protocol(&self) -> Self::InboundProtocol {
		self.protocols.clone()
	}

	fn inject_fully_negotiated_inbound(
		&mut self,
		proto: <Self::InboundProtocol as InboundUpgrade<TSubstream>>::Output
	) {
		self.inject_fully_negotiated(proto);
	}

	#[inline]
	fn inject_fully_negotiated_outbound(
		&mut self,
		proto: <Self::OutboundProtocol as OutboundUpgrade<TSubstream>>::Output,
		_: Self::OutboundOpenInfo
	) {
		self.inject_fully_negotiated(proto);
	}

	fn inject_event(&mut self, message: CustomProtosHandlerIn<TMessage>) {
		match message {
			CustomProtosHandlerIn::Disable => {
				match self.state {
					State::Init(_) | State::Normal => self.state = State::Disabled,
					State::Disabled | State::ShuttingDown => (),
				}

				self.keep_alive = KeepAlive::Now;
				for substream in self.substreams.iter_mut() {
					substream.shutdown();
				}
			},
			CustomProtosHandlerIn::EnableActive | CustomProtosHandlerIn::EnablePassive => {
				match self.state {
					State::Init(ref mut list) => {
						for proto in list.drain() {
							let event = CustomProtosHandlerOut::CustomProtocolOpen {
								protocol_id: proto.protocol_id(),
								version: proto.protocol_version(),
							};

							self.substreams.push(proto);
							self.events_queue.push(ProtocolsHandlerEvent::Custom(event));
						}

						self.state = State::Normal;
					}
					State::Disabled => self.state = State::Normal,
					State::Normal | State::ShuttingDown => (),
				}

				self.keep_alive = KeepAlive::Forever;

				// Try open one substream for each registered protocol.
				if let CustomProtosHandlerIn::EnableActive = message {
					for protocol in self.protocols.0.iter() {
						if self.substreams.iter().any(|p| p.protocol_id() == protocol.id()) {
							// Skipping protocol that's already open.
							continue
						}

						self.events_queue.push(ProtocolsHandlerEvent::OutboundSubstreamRequest {
							upgrade: protocol.clone(),
							info: protocol.id(),
						});
					}
				}
			},
			CustomProtosHandlerIn::SendCustomMessage { protocol, message } => {
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

				proto.send_message(message);
			},
		}
	}

	#[inline]
	fn inject_inbound_closed(&mut self) {}

	#[inline]
	fn inject_dial_upgrade_error(&mut self, protocol_id: Self::OutboundOpenInfo, error: ProtocolsHandlerUpgrErr<io::Error>) {
		if let State::Normal = self.state {
			let event = CustomProtosHandlerOut::ProtocolError { protocol_id, error };
			self.events_queue.push(ProtocolsHandlerEvent::Custom(event));
		}

		// Right now if the remote doesn't support one of the custom protocols, we shut down the
		// entire connection. This is a hack-ish solution to the problem where we connect to nodes
		// that support libp2p but not the testnet that we want.
		self.shutdown();
	}

	#[inline]
	fn connection_keep_alive(&self) -> KeepAlive {
		self.keep_alive
	}

	fn shutdown(&mut self) {
		match self.state {
			State::Init(_) | State::Normal | State::Disabled => self.state = State::ShuttingDown,
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

		if let State::ShuttingDown = self.state {
			if self.substreams.is_empty() {
				return Ok(Async::Ready(ProtocolsHandlerEvent::Shutdown))
			}
		}

		for n in (0..self.substreams.len()).rev() {
			let mut substream = self.substreams.swap_remove(n);
			match substream.poll() {
				Ok(Async::Ready(Some(RegisteredProtocolEvent::Message(message)))) => {
					let event = CustomProtosHandlerOut::CustomMessage {
						protocol_id: substream.protocol_id(),
						message
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
					// Close the connection as soon as possible.
					if self.substreams.is_empty() {
						self.keep_alive = KeepAlive::Now;
					}
					let event = CustomProtosHandlerOut::CustomProtocolClosed {
						protocol_id: substream.protocol_id(),
						result: Ok(())
					};
					return Ok(Async::Ready(ProtocolsHandlerEvent::Custom(event)))
				},
				Err(err) => {
					// Close the connection as soon as possible.
					if self.substreams.is_empty() {
						self.keep_alive = KeepAlive::Now;
					}
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

impl<TMessage, TSubstream> fmt::Debug for CustomProtosHandler<TMessage, TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
{
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
		f.debug_struct("CustomProtosHandler")
			.field("protocols", &self.protocols.len())
			.field("substreams", &self.substreams.len())
			.finish()
	}
}
