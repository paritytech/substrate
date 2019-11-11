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
	handler::legacy::{LegacyProtoHandler, LegacyProtoHandlerProto, LegacyProtoHandlerIn, LegacyProtoHandlerOut},
	handler::notif_in::{NotifsInHandlerProto, NotifsInHandler, NotifsInHandlerIn, NotifsInHandlerOut},
	handler::notif_out::{NotifsOutHandlerProto, NotifsOutHandler, NotifsOutHandlerIn, NotifsOutHandlerOut},
	upgrade::{NotificationsIn, NotificationsOut, RegisteredProtocol, SelectUpgrade, UpgradeCollec},
};
use bytes::BytesMut;
use futures::prelude::*;
use libp2p::core::{ConnectedPoint, PeerId};
use libp2p::core::either::{EitherError, EitherOutput};
use libp2p::core::upgrade::{EitherUpgrade, ReadOneError, UpgradeError, InboundUpgrade, OutboundUpgrade};
use libp2p::swarm::{
	ProtocolsHandler, ProtocolsHandlerEvent,
	IntoProtocolsHandler,
	KeepAlive,
	ProtocolsHandlerUpgrErr,
	SubstreamProtocol,
};
use log::error;
use std::{borrow::Cow, error, io};
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

	/// True if the handler is in the enabled state.
	enabled: bool,
}

impl<TSubstream> IntoProtocolsHandler for NotifsHandlerProto<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite + 'static,
{
	type Handler = NotifsHandler<TSubstream>;

	fn inbound_protocol(&self) -> SelectUpgrade<UpgradeCollec<NotificationsIn>, RegisteredProtocol> {
		let in_handlers = self.in_handlers.iter()
			.map(|h| h.inbound_protocol())
			.collect::<UpgradeCollec<_>>();

		SelectUpgrade::new(in_handlers, self.legacy.inbound_protocol())
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
			enabled: false,
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
	Send {
		/// Name of the protocol for the message, or `None` to force the legacy protocol.
		///
		/// If `Some`, must match one of the registered protocols. For backwards-compatibility
		/// reasons, if the remote doesn't support this protocol, we use the legacy substream.
		proto_name: Option<Cow<'static, [u8]>>,

		/// The message to send.
		message: Vec<u8>,
	},
}

/// Event that can be emitted by a `NotifsHandler`.
#[derive(Debug)]
pub enum NotifsHandlerOut {
	/// Opened a custom protocol with the remote.
	CustomProtocolOpen,

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
		EitherError<
			<NotifsInHandler<TSubstream> as ProtocolsHandler>::Error,
			<NotifsOutHandler<TSubstream> as ProtocolsHandler>::Error,
		>,
		<LegacyProtoHandler<TSubstream> as ProtocolsHandler>::Error,
	>;
	type InboundProtocol = SelectUpgrade<UpgradeCollec<NotificationsIn>, RegisteredProtocol>;
	type OutboundProtocol = EitherUpgrade<NotificationsOut, RegisteredProtocol>;
	type OutboundOpenInfo = Option<usize>;	// Index within the `out_handlers`; None for legacy

	fn listen_protocol(&self) -> SubstreamProtocol<Self::InboundProtocol> {
		let in_handlers = self.in_handlers.iter()
			.map(|h| h.listen_protocol().into_upgrade().1)		// TODO: map_upgrade() instead
			.collect::<UpgradeCollec<_>>();

		// TODO: map_upgrade() instead
		let proto = SelectUpgrade::new(in_handlers, self.legacy.listen_protocol().into_upgrade().1);
		SubstreamProtocol::new(proto)
	}

	fn inject_fully_negotiated_inbound(
		&mut self,
		out: <Self::InboundProtocol as InboundUpgrade<TSubstream>>::Output
	) {
		match out {
			EitherOutput::First((out, num)) =>
				self.in_handlers[num].inject_fully_negotiated_inbound(out),
			EitherOutput::Second(out) =>
				self.legacy.inject_fully_negotiated_inbound(out),
		}
	}

	fn inject_fully_negotiated_outbound(
		&mut self,
		out: <Self::OutboundProtocol as OutboundUpgrade<TSubstream>>::Output,
		num: Self::OutboundOpenInfo
	) {
		match (out, num) {
			(EitherOutput::First(out), Some(num)) =>
				self.out_handlers[num].inject_fully_negotiated_outbound(out, ()),
			(EitherOutput::Second(out), None) =>
				self.legacy.inject_fully_negotiated_outbound(out, ()),
			_ => error!("inject_fully_negotiated_outbound called with wrong parameters"),
		}
	}

	fn inject_event(&mut self, message: NotifsHandlerIn) {
		match message {
			NotifsHandlerIn::Enable => {
				self.enabled = true;
				self.legacy.inject_event(LegacyProtoHandlerIn::Enable);
				for handler in &mut self.out_handlers {
					handler.inject_event(NotifsOutHandlerIn::Enable);
				}
			},
			NotifsHandlerIn::Disable => {
				self.enabled = false;
				self.legacy.inject_event(LegacyProtoHandlerIn::Disable);
				for handler in &mut self.out_handlers {
					handler.inject_event(NotifsOutHandlerIn::Disable);
				}
			},
			NotifsHandlerIn::Send { proto_name, message } => {
				if let Some(proto_name) = proto_name {
					for handler in &mut self.out_handlers {
						if handler.is_open() && handler.protocol_name() == &proto_name[..] {
							handler.inject_event(NotifsOutHandlerIn::Send(message));
							return;
						}
					}
				}

				self.legacy.inject_event(LegacyProtoHandlerIn::SendCustomMessage { message });
			},
		}
	}

	fn inject_dial_upgrade_error(
		&mut self,
		num: Option<usize>,
		err: ProtocolsHandlerUpgrErr<EitherError<ReadOneError, io::Error>>
	) {
		match (err, num) {
			(ProtocolsHandlerUpgrErr::Timeout, Some(num)) =>
				self.out_handlers[num].inject_dial_upgrade_error(
					(),
					ProtocolsHandlerUpgrErr::Timeout
				),
			(ProtocolsHandlerUpgrErr::Timeout, None) =>
				self.legacy.inject_dial_upgrade_error((), ProtocolsHandlerUpgrErr::Timeout),
			(ProtocolsHandlerUpgrErr::Timer, Some(num)) =>
				self.out_handlers[num].inject_dial_upgrade_error(
					(),
					ProtocolsHandlerUpgrErr::Timer
				),
			(ProtocolsHandlerUpgrErr::Timer, None) =>
				self.legacy.inject_dial_upgrade_error((), ProtocolsHandlerUpgrErr::Timer),
			(ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Select(err)), Some(num)) =>
				self.out_handlers[num].inject_dial_upgrade_error(
					(),
					ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Select(err))
				),
			(ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Select(err)), None) =>
				self.legacy.inject_dial_upgrade_error(
					(),
					ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Select(err))
				),
			(ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Apply(EitherError::A(err))), Some(num)) =>
				self.out_handlers[num].inject_dial_upgrade_error(
					(),
					ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Apply(err))
				),
			(ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Apply(EitherError::B(err))), None) =>
				self.legacy.inject_dial_upgrade_error(
					(),
					ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Apply(err))
				),
			_ => error!("inject_dial_upgrade_error called with bad parameters"),
		}
	}

	fn connection_keep_alive(&self) -> KeepAlive {
		// Iterate over each handler and return the maximum value.

		let mut ret = self.legacy.connection_keep_alive();
		if ret.is_yes() {
			return KeepAlive::Yes;
		}

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
		for (handler_num, handler) in self.in_handlers.iter_mut().enumerate() {
			if let Async::Ready(ev) = handler.poll().map_err(|e| EitherError::A(EitherError::A(e)))? {
				match ev {
					ProtocolsHandlerEvent::OutboundSubstreamRequest { protocol, info: () } =>
						error!("Incoming substream handler tried to open a substream"),
					ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::OpenRequest) =>
						if self.enabled {
							// TODO: also open outbound
							//handler.inject_event(NotifsInHandlerIn::Accept(Vec::new()));		// TODO: message
						} else {
							handler.inject_event(NotifsInHandlerIn::Refuse);
						},
					ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::Closed) => unimplemented!(),
					ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::Notif(msg)) => unimplemented!(),
				}
			}
		}

		for (handler_num, handler) in self.out_handlers.iter_mut().enumerate() {
			if let Async::Ready(ev) = handler.poll().map_err(|e| EitherError::A(EitherError::B(e)))? {
				match ev {
					ProtocolsHandlerEvent::OutboundSubstreamRequest { protocol, info: () } =>
						return Ok(Async::Ready(ProtocolsHandlerEvent::OutboundSubstreamRequest {
							protocol: protocol.map_upgrade(EitherUpgrade::A),
							info: Some(handler_num),
						})),
					// TODO:
					/*ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Open { .. }) =>
						return ProtocolsHandlerEvent::Custom(NotifsHandlerOut::CustomProtocolOpen { version }),
					ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Closed) =>
						return ProtocolsHandlerEvent::Custom(NotifsHandlerOut::CustomProtocolClosed { reason }),
					ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Refused) =>
						return ProtocolsHandlerEvent::Custom(NotifsHandlerOut::CustomMessage { message }),
					ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::ProtocolError { is_severe, error }) =>
						return ProtocolsHandlerEvent::Custom(NotifsHandlerOut::ProtocolError { is_severe, error }),*/
					_ => {}
				}
			}
		}

		if let Async::Ready(ev) = self.legacy.poll().map_err(EitherError::B)? {
			return Ok(Async::Ready(ev
				.map_protocol(EitherUpgrade::B)
				.map_outbound_open_info(|()| None)
				.map_custom(|ev| match ev {
					LegacyProtoHandlerOut::CustomProtocolOpen { .. } =>
						NotifsHandlerOut::CustomProtocolOpen,
					LegacyProtoHandlerOut::CustomProtocolClosed { reason } =>
						NotifsHandlerOut::CustomProtocolClosed { reason },
					LegacyProtoHandlerOut::CustomMessage { message } =>
						NotifsHandlerOut::CustomMessage { message },
					LegacyProtoHandlerOut::Clogged { messages } =>
						NotifsHandlerOut::Clogged { messages },
					LegacyProtoHandlerOut::ProtocolError { is_severe, error } =>
						NotifsHandlerOut::ProtocolError { is_severe, error },
				})));
		}

		Ok(Async::NotReady)
	}
}
