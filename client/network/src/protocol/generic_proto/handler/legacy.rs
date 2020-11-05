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

use crate::protocol::generic_proto::upgrade::{RegisteredProtocol, RegisteredProtocolEvent, RegisteredProtocolSubstream};

use bytes::BytesMut;
use futures::prelude::*;
use libp2p::core::{ConnectedPoint, PeerId};
use libp2p::core::upgrade::{InboundUpgrade, OutboundUpgrade};
use libp2p::swarm::{
	ProtocolsHandler, ProtocolsHandlerEvent,
	IntoProtocolsHandler,
	KeepAlive,
	ProtocolsHandlerUpgrErr,
	SubstreamProtocol,
	NegotiatedSubstream,
};
use smallvec::SmallVec;
use std::{collections::VecDeque, convert::Infallible, error, fmt, io};
use std::{pin::Pin, task::{Context, Poll}};

/// Handler for the legacy substream.
///
/// The so-called legacy substream is a deprecated way of establishing a Substrate-specific
/// substream in an active connection.
///
/// Pro-actively opening a legacy substream is no longer supported. Only accepting incoming legacy
/// substreams is possible. As part of the protocol, only the dialing side of a connection
/// (emphasis *connection*, not substream) is allowed to open a legacy substream.
///
/// # Usage
///
/// The handler can spontaneously generate `CustomProtocolOpen` and `CustomProtocolClosed` events
/// if the remote opens or closes the substream. Send a `Close` message in order to shut down any
/// active substream. After `Close` has beent sent, a `CustomProtocolClosed` event will be sent
/// back in the near future.
///
pub struct LegacyProtoHandlerProto {
	/// Configuration for the protocol upgrade to negotiate.
	protocol: RegisteredProtocol,
}

impl LegacyProtoHandlerProto {
	/// Builds a new `LegacyProtoHandlerProto`.
	pub fn new(protocol: RegisteredProtocol) -> Self {
		LegacyProtoHandlerProto {
			protocol,
		}
	}
}

impl IntoProtocolsHandler for LegacyProtoHandlerProto {
	type Handler = LegacyProtoHandler;

	fn inbound_protocol(&self) -> RegisteredProtocol {
		self.protocol.clone()
	}

	fn into_handler(self, _: &PeerId, _: &ConnectedPoint) -> Self::Handler {
		LegacyProtoHandler {
			protocol: self.protocol,
			substreams: SmallVec::new(),
			shutdown: SmallVec::new(),
			events_queue: VecDeque::new(),
		}
	}
}

/// The actual handler once the connection has been established.
pub struct LegacyProtoHandler {
	/// Configuration for the protocol upgrade to negotiate.
	protocol: RegisteredProtocol,

	/// The substreams where bidirectional communications happen.
	substreams: SmallVec<[RegisteredProtocolSubstream<NegotiatedSubstream>; 4]>,

	/// Contains substreams which are being shut down.
	shutdown: SmallVec<[RegisteredProtocolSubstream<NegotiatedSubstream>; 4]>,

	/// Queue of events to send to the outside.
	///
	/// This queue must only ever be modified to insert elements at the back, or remove the first
	/// element.
	events_queue: VecDeque<
		ProtocolsHandlerEvent<RegisteredProtocol, Infallible, LegacyProtoHandlerOut, ConnectionKillError>
	>,
}

/// Event that can be received by a `LegacyProtoHandler`.
#[derive(Debug)]
pub enum LegacyProtoHandlerIn {
	/// The handler should close any existing substream.
	Close,
}

/// Event that can be emitted by a `LegacyProtoHandler`.
#[derive(Debug)]
pub enum LegacyProtoHandlerOut {
	/// Opened a custom protocol with the remote.
	CustomProtocolOpen {
		/// Version of the protocol that has been opened.
		version: u8,
		/// Handshake message that has been sent to us.
		/// This is normally a "Status" message, but this out of the concern of this code.
		received_handshake: Vec<u8>,
	},

	/// Closed a custom protocol with the remote.
	CustomProtocolClosed,

	/// Receives a message on a custom protocol substream.
	CustomMessage {
		/// Message that has been received.
		message: BytesMut,
	},
}

impl LegacyProtoHandler {
	/// Polls the state for events. Optionally returns an event to produce.
	#[must_use]
	fn poll_state(&mut self, cx: &mut Context)
		-> Option<ProtocolsHandlerEvent<RegisteredProtocol, Infallible, LegacyProtoHandlerOut, ConnectionKillError>> {
		shutdown_list(&mut self.shutdown, cx);

		for n in (0..self.substreams.len()).rev() {
			let mut substream = self.substreams.swap_remove(n);
			match Pin::new(&mut substream).poll_next(cx) {
				Poll::Pending => self.substreams.push(substream),
				Poll::Ready(Some(Ok(RegisteredProtocolEvent::Message(message)))) => {
					let event = LegacyProtoHandlerOut::CustomMessage {
						message
					};
					self.substreams.push(substream);
					return Some(ProtocolsHandlerEvent::Custom(event));
				},
				Poll::Ready(Some(Ok(RegisteredProtocolEvent::Clogged))) => {
					self.shutdown.push(substream);
					if self.substreams.is_empty() {
						let event = LegacyProtoHandlerOut::CustomProtocolClosed;
						return Some(ProtocolsHandlerEvent::Custom(event));
					}
				}
				Poll::Ready(None) => {
					self.shutdown.push(substream);
					if self.substreams.is_empty() {
						let event = LegacyProtoHandlerOut::CustomProtocolClosed;
						return Some(ProtocolsHandlerEvent::Custom(event));
					}
				}
				Poll::Ready(Some(Err(err))) => {
					if self.substreams.is_empty() {
						let event = LegacyProtoHandlerOut::CustomProtocolClosed;
						return Some(ProtocolsHandlerEvent::Custom(event));
					} else {
						log::debug!(target: "sub-libp2p", "Error on extra substream: {:?}", err);
					}
				}
			}
		}

		None
	}
}

impl ProtocolsHandler for LegacyProtoHandler {
	type InEvent = LegacyProtoHandlerIn;
	type OutEvent = LegacyProtoHandlerOut;
	type Error = ConnectionKillError;
	type InboundProtocol = RegisteredProtocol;
	type OutboundProtocol = RegisteredProtocol;
	type OutboundOpenInfo = Infallible;
	type InboundOpenInfo = ();

	fn listen_protocol(&self) -> SubstreamProtocol<Self::InboundProtocol, ()> {
		SubstreamProtocol::new(self.protocol.clone(), ())
	}

	fn inject_fully_negotiated_inbound(
		&mut self,
		(substream, received_handshake): <Self::InboundProtocol as InboundUpgrade<NegotiatedSubstream>>::Output,
		(): ()
	) {
		if self.substreams.is_empty() {
			let event = LegacyProtoHandlerOut::CustomProtocolOpen {
				version: substream.protocol_version(),
				received_handshake,
			};
			self.events_queue.push_back(ProtocolsHandlerEvent::Custom(event));
		}

		self.substreams.push(substream);
	}

	fn inject_fully_negotiated_outbound(
		&mut self,
		_: <Self::OutboundProtocol as OutboundUpgrade<NegotiatedSubstream>>::Output,
		unreachable: Self::OutboundOpenInfo
	) {
		match unreachable {}
	}

	fn inject_event(&mut self, message: LegacyProtoHandlerIn) {
		// Only the `Close` message exists at the moment.
		let LegacyProtoHandlerIn::Close = message;

		if !self.substreams.is_empty() {
			let event = LegacyProtoHandlerOut::CustomProtocolClosed;
			self.events_queue.push_back(ProtocolsHandlerEvent::Custom(event));
		}

		for mut substream in self.substreams.drain() {
			substream.shutdown();
			self.shutdown.push(substream);
		}
	}

	fn inject_dial_upgrade_error(
		&mut self,
		unreachable: Self::OutboundOpenInfo,
		_: ProtocolsHandlerUpgrErr<io::Error>
	) {
		match unreachable {}
	}

	fn connection_keep_alive(&self) -> KeepAlive {
		if self.substreams.is_empty() {
			KeepAlive::No
		} else {
			KeepAlive::Yes
		}
	}

	fn poll(
		&mut self,
		cx: &mut Context,
	) -> Poll<
		ProtocolsHandlerEvent<Self::OutboundProtocol, Self::OutboundOpenInfo, Self::OutEvent, Self::Error>
	> {
		// Flush the events queue if necessary.
		if let Some(event) = self.events_queue.pop_front() {
			return Poll::Ready(event)
		}

		// Process all the substreams.
		if let Some(event) = self.poll_state(cx) {
			return Poll::Ready(event)
		}

		Poll::Pending
	}
}

impl fmt::Debug for LegacyProtoHandler {
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
		f.debug_struct("LegacyProtoHandler")
			.finish()
	}
}

/// Given a list of substreams, tries to shut them down. The substreams that have been successfully
/// shut down are removed from the list.
fn shutdown_list
	(list: &mut SmallVec<impl smallvec::Array<Item = RegisteredProtocolSubstream<NegotiatedSubstream>>>,
	cx: &mut Context)
{
	'outer: for n in (0..list.len()).rev() {
		let mut substream = list.swap_remove(n);
		loop {
			match substream.poll_next_unpin(cx) {
				Poll::Ready(Some(Ok(_))) => {}
				Poll::Pending => break,
				Poll::Ready(Some(Err(_))) | Poll::Ready(None) => continue 'outer,
			}
		}
		list.push(substream);
	}
}

/// Error returned when switching from normal to disabled.
#[derive(Debug)]
pub struct ConnectionKillError;

impl error::Error for ConnectionKillError {
}

impl fmt::Display for ConnectionKillError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Connection kill when switching from normal to disabled")
	}
}
