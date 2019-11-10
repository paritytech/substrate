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

use crate::generic_proto::{
	handler::legacy::{LegacyProtoHandler, LegacyProtoHandlerProto},
	handler::notif_in::{NotifsInHandlerProto, NotifsInHandler},
	handler::notif_out::{NotifsOutHandlerProto, NotifsOutHandler},
	upgrade::{NotificationsIn, NotificationsOut, RegisteredProtocol, UpgradeCollec},
};
use bytes::BytesMut;
use futures::prelude::*;
use libp2p::core::{ConnectedPoint, PeerId};
use libp2p::core::either::EitherError;
use libp2p::core::upgrade::{ReadOneError, InboundUpgrade, OutboundUpgrade};
use libp2p::swarm::{
	ProtocolsHandler, ProtocolsHandlerEvent,
	IntoProtocolsHandler,
	KeepAlive,
	ProtocolsHandlerUpgrErr,
	SubstreamProtocol,
};
use std::{borrow::Cow, error};
use tokio_io::{AsyncRead, AsyncWrite};

/// Implements the `IntoProtocolsHandler` trait of libp2p.
///
/// Every time a connection with a remote starts, an instance of this struct is created and
/// sent to a background task dedicated to this connection. Once the connection is established,
/// it is turned into a [`NotifsHandler`].
pub struct NotifsHandlerProto<TSubstream> {
	/// Prototypes for handlers for ingoing substreams.
	in_handlers: Vec<NotifsInHandlerProto<TSubstream>>,

	/// Prototypes for handlers for outgoing substreams.
	out_handlers: Vec<NotifsOutHandlerProto<TSubstream>>,

	/// Prototype for handler for backwards-compatibility.
	legacy: LegacyProtoHandlerProto<TSubstream>,
}

/// The actual handler once the connection has been established.
pub struct NotifsHandler<TSubstream> {
	/// Handlers for ingoing substreams.
	in_handlers: Vec<NotifsInHandler<TSubstream>>,

	/// Handlers for outgoing substreams.
	out_handlers: Vec<NotifsOutHandler<TSubstream>>,

	/// Handler for backwards-compatibility.
	legacy: LegacyProtoHandler<TSubstream>,
}

impl<TSubstream> IntoProtocolsHandler for NotifsHandlerProto<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite + 'static,
{
	type Handler = NotifsHandler<TSubstream>;

	fn inbound_protocol(&self) -> UpgradeCollec<NotificationsIn> {
		unimplemented!()	// TODO:
	}

	fn into_handler(self, remote_peer_id: &PeerId, connected_point: &ConnectedPoint) -> Self::Handler {
		NotifsHandler {
			in_handlers: self.in_handlers
				.into_iter()
				.map(|p| p.into_handler(remote_peer_id, connected_point))
				.collect(),
			out_handlers: self.out_handlers
				.into_iter()
				.map(|p| p.into_handler(remote_peer_id, connected_point))
				.collect(),
			legacy: self.legacy.into_handler(remote_peer_id, connected_point),
		}
	}
}

/// Event that can be received by a `NotifsHandler`.
#[derive(Debug)]
pub enum NotifsHandlerIn {
	/// The node should start using custom protocols.
	Enable,

	/// The node should stop using custom protocols.
	Disable,

	/// Sends a message through a custom protocol substream.
	SendCustomMessage {
		/// The message to send.
		message: Vec<u8>,
	},
}

/// Event that can be emitted by a `NotifsHandler`.
#[derive(Debug)]
pub enum NotifsHandlerOut {
	/// Opened a custom protocol with the remote.
	CustomProtocolOpen {
		/// Version of the protocol that has been opened.
		version: u8,
	},

	/// Closed a custom protocol with the remote.
	CustomProtocolClosed {
		/// Reason why the substream closed, for diagnostic purposes.
		reason: Cow<'static, str>,
	},

	/// Receives a message on a custom protocol substream.
	CustomMessage {
		/// Message that has been received.
		message: BytesMut,
	},

	/// A substream to the remote is clogged. The send buffer is very large, and we should print
	/// a diagnostic message and/or avoid sending more data.
	Clogged {
		/// Copy of the messages that are within the buffer, for further diagnostic.
		messages: Vec<Vec<u8>>,
	},

	/// An error has happened on the protocol level with this node.
	ProtocolError {
		/// If true the error is severe, such as a protocol violation.
		is_severe: bool,
		/// The error that happened.
		error: Box<dyn error::Error + Send + Sync>,
	},
}

impl<TSubstream> NotifsHandlerProto<TSubstream> {
	pub fn new(legacy: RegisteredProtocol, list: impl Into<Vec<(Cow<'static, [u8]>, Vec<u8>)>>) -> Self {
		let list = list.into();

		NotifsHandlerProto {
			in_handlers: list.clone().into_iter().map(|(p, msg)| NotifsInHandlerProto::new(p, msg)).collect(),
			out_handlers: list.clone().into_iter().map(|(p, _)| NotifsOutHandlerProto::new(p)).collect(),
			legacy: LegacyProtoHandlerProto::new(legacy),
		}
	}
}

impl<TSubstream> ProtocolsHandler for NotifsHandler<TSubstream>
where TSubstream: AsyncRead + AsyncWrite + 'static {
	type InEvent = NotifsHandlerIn;
	type OutEvent = NotifsHandlerOut;
	type Substream = TSubstream;
	type Error = EitherError<
		<NotifsInHandler<TSubstream> as ProtocolsHandler>::Error,
		<NotifsOutHandler<TSubstream> as ProtocolsHandler>::Error,
	>;
	type InboundProtocol = UpgradeCollec<NotificationsIn>;
	type OutboundProtocol = UpgradeCollec<NotificationsOut>;
	type OutboundOpenInfo = ();

	fn listen_protocol(&self) -> SubstreamProtocol<Self::InboundProtocol> {
		unimplemented!()	// TODO:
	}

	fn inject_fully_negotiated_inbound(
		&mut self,
		(out, num): <Self::InboundProtocol as InboundUpgrade<TSubstream>>::Output
	) {
		self.in_handlers[num].inject_fully_negotiated_inbound(out)
	}

	fn inject_fully_negotiated_outbound(
		&mut self,
		(out, num): <Self::OutboundProtocol as OutboundUpgrade<TSubstream>>::Output,
		_: Self::OutboundOpenInfo
	) {
		self.out_handlers[num].inject_fully_negotiated_outbound(out, ())
	}

	fn inject_event(&mut self, message: NotifsHandlerIn) {
		unimplemented!()		// TODO:
	}

	fn inject_dial_upgrade_error(&mut self, _: (), err: ProtocolsHandlerUpgrErr<(ReadOneError, usize)>) {
		unimplemented!()		// TODO:
	}

	fn connection_keep_alive(&self) -> KeepAlive {
		// Iterate over each handler and return the maximum value.
		let mut ret = KeepAlive::No;

		for handler in &self.in_handlers {
			let val = handler.connection_keep_alive();
			if val.is_yes() {
				return KeepAlive::Yes;
			}
			if ret < val { ret = val; }
		}

		for handler in &self.out_handlers {
			let val = handler.connection_keep_alive();
			if val.is_yes() {
				return KeepAlive::Yes;
			}
			if ret < val { ret = val; }
		}

		ret
	}

	fn poll(
		&mut self,
	) -> Poll<
		ProtocolsHandlerEvent<Self::OutboundProtocol, Self::OutboundOpenInfo, Self::OutEvent>,
		Self::Error,
	> {
		for handler in &mut self.in_handlers {
			if let Async::Ready(v) = handler.poll().map_err(EitherError::A)? {
				unimplemented!() // TODO: return Ok(Async::Ready(v));
			}
		}

		for handler in &mut self.out_handlers {
			if let Async::Ready(v) = handler.poll().map_err(EitherError::B)? {
				unimplemented!() // TODO: return Ok(Async::Ready(v));
			}
		}

		Ok(Async::NotReady)
	}
}
