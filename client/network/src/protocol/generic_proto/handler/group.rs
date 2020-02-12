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

//! Implementations of the `IntoProtocolsHandler` and `ProtocolsHandler` traits for both ingoing
//! and outgoing substreams for all gossiping protocols together.
//!
//! This is the main implementation of `ProtocolsHandler` in this crate, that handles all the
//! protocols that are Substrate-related and outside of the scope of libp2p.
//!
//! # Usage
//!
//! The handler can be in one of the following states: `Initial`, `Enabled`, `Disabled`.
//!
//! The `Initial` state is the state that the handler initially is in. It is a temporary state
//! during which the user must either enable or disable the handler. After that, the handler stays
//! either enabled or disabled.
//!
//! On the wire, we try to open the following substreams:
//!
//! - One substream for each notification protocol passed as parameter to the
//!   `NotifsHandlerProto::new` function.
//! - One "legacy" substream used for anything non-related to gossiping, and used as a fallback
//!   in case the notification protocol can't be opened.
//!
//! When the handler is in the `Enabled` state, we immediately open and try to maintain all the
//! aforementioned substreams. When the handler is in the `Disabled` state, we immediately close
//! (or abort opening) all these substreams. It is intended that in the future we allow states in
//! which some protocols are open and not others. Symmetrically, we allow incoming
//! Substrate-related substreams if and only if we are in the `Enabled` state.
//!
//! The user has the choice between sending a message with `SendNotification`, to send a
//! notification, and `SendLegacy`, to send any other kind of message.
//!

use crate::protocol::generic_proto::{
	handler::legacy::{LegacyProtoHandler, LegacyProtoHandlerProto, LegacyProtoHandlerIn, LegacyProtoHandlerOut},
	handler::notif_in::{NotifsInHandlerProto, NotifsInHandler, NotifsInHandlerIn, NotifsInHandlerOut},
	handler::notif_out::{NotifsOutHandlerProto, NotifsOutHandler, NotifsOutHandlerIn, NotifsOutHandlerOut},
	upgrade::{NotificationsIn, NotificationsOut, RegisteredProtocol, UpgradeCollec},
};
use crate::protocol::message::generic::{Message as GenericMessage, ConsensusMessage};

use bytes::BytesMut;
use codec::Encode as _;
use futures::prelude::*;
use libp2p::core::{either::{EitherError, EitherOutput}, ConnectedPoint, Negotiated, PeerId};
use libp2p::core::upgrade::{EitherUpgrade, ReadOneError, UpgradeError, SelectUpgrade, InboundUpgrade, OutboundUpgrade};
use libp2p::swarm::{
	ProtocolsHandler, ProtocolsHandlerEvent,
	IntoProtocolsHandler,
	KeepAlive,
	ProtocolsHandlerUpgrErr,
	SubstreamProtocol,
};
use log::error;
use sp_runtime::ConsensusEngineId;
use std::{borrow::Cow, error, io, task::{Context, Poll}};

/// Implements the `IntoProtocolsHandler` trait of libp2p.
///
/// Every time a connection with a remote starts, an instance of this struct is created and
/// sent to a background task dedicated to this connection. Once the connection is established,
/// it is turned into a [`NotifsHandler`].
///
/// See the documentation at the module level for more information.
pub struct NotifsHandlerProto<TSubstream> {
	/// Prototypes for handlers for ingoing substreams.
	in_handlers: Vec<(NotifsInHandlerProto<TSubstream>, ConsensusEngineId)>,

	/// Prototypes for handlers for outgoing substreams.
	out_handlers: Vec<(NotifsOutHandlerProto<TSubstream>, ConsensusEngineId)>,

	/// Prototype for handler for backwards-compatibility.
	legacy: LegacyProtoHandlerProto<TSubstream>,
}

/// The actual handler once the connection has been established.
///
/// See the documentation at the module level for more information.
pub struct NotifsHandler<TSubstream> {
	/// Handlers for ingoing substreams.
	in_handlers: Vec<(NotifsInHandler<TSubstream>, ConsensusEngineId)>,

	/// Handlers for outgoing substreams.
	out_handlers: Vec<(NotifsOutHandler<TSubstream>, ConsensusEngineId)>,

	/// Handler for backwards-compatibility.
	legacy: LegacyProtoHandler<TSubstream>,

	/// State of this handler.
	enabled: EnabledState,

	/// If we receive inbound substream requests while in initialization mode,
	/// we push the corresponding index here and process them when the handler
	/// gets enabled/disabled.
	pending_in: Vec<usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum EnabledState {
	Initial,
	Enabled,
	Disabled,
}

impl<TSubstream> IntoProtocolsHandler for NotifsHandlerProto<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite + Unpin + Send + 'static,
{
	type Handler = NotifsHandler<TSubstream>;

	fn inbound_protocol(&self) -> SelectUpgrade<UpgradeCollec<NotificationsIn>, RegisteredProtocol> {
		let in_handlers = self.in_handlers.iter()
			.map(|(h, _)| h.inbound_protocol())
			.collect::<UpgradeCollec<_>>();

		SelectUpgrade::new(in_handlers, self.legacy.inbound_protocol())
	}

	fn into_handler(self, remote_peer_id: &PeerId, connected_point: &ConnectedPoint) -> Self::Handler {
		NotifsHandler {
			in_handlers: self.in_handlers
				.into_iter()
				.map(|(p, e)| (p.into_handler(remote_peer_id, connected_point), e))
				.collect(),
			out_handlers: self.out_handlers
				.into_iter()
				.map(|(p, e)| (p.into_handler(remote_peer_id, connected_point), e))
				.collect(),
			legacy: self.legacy.into_handler(remote_peer_id, connected_point),
			enabled: EnabledState::Initial,
			pending_in: Vec::new(),
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

	/// Sends a message through the custom protocol substream.
	///
	/// > **Note**: This must **not** be an encoded `ConsensusMessage` message.
	SendLegacy {
		/// The message to send.
		message: Vec<u8>,
	},

	/// Sends a notifications message.
	SendNotification {
		/// Name of the protocol for the message.
		///
		/// Must match one of the registered protocols. For backwards-compatibility reasons, if
		/// the remote doesn't support this protocol, we use the legacy substream to send a
		/// `ConsensusMessage` message.
		proto_name: Cow<'static, [u8]>,

		/// The engine ID to use, in case we need to send this message over the legacy substream.
		///
		/// > **Note**: Ideally this field wouldn't be necessary, and we would deduce the engine
		/// >			ID from the existing handlers. However, it is possible (especially in test
		/// >			situations) that we open connections before all the notification protocols
		/// >			have been registered, in which case we always rely on the legacy substream.
		engine_id: ConsensusEngineId,

		/// The message to send.
		message: Vec<u8>,
	},
}

/// Event that can be emitted by a `NotifsHandler`.
#[derive(Debug)]
pub enum NotifsHandlerOut {
	/// Opened the substreams with the remote.
	Open,

	/// Closed the substreams with the remote.
	Closed {
		/// Reason why the substream closed, for diagnostic purposes.
		reason: Cow<'static, str>,
	},

	/// Received a non-gossiping message on the legacy substream.
	CustomMessage {
		/// Message that has been received.
		///
		/// Keep in mind that this can be a `ConsensusMessage` message, which then contains a
		/// notification.
		message: BytesMut,
	},

	/// Received a message on a custom protocol substream.
	Notification {
		/// Engine corresponding to the message.
		proto_name: Cow<'static, [u8]>,

		/// For legacy reasons, the name to use if we had received the message from the legacy
		/// substream.
		engine_id: ConsensusEngineId,

		/// Message that has been received.
		///
		/// If `proto_name` is `None`, this decodes to a `Message`. If `proto_name` is `Some`,
		/// this is directly a gossiping message.
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

impl<TSubstream> NotifsHandlerProto<TSubstream>
where TSubstream: AsyncRead + AsyncWrite + Unpin + Send + 'static {
	/// Builds a new handler.
	pub fn new(legacy: RegisteredProtocol, list: impl Into<Vec<(Cow<'static, [u8]>, ConsensusEngineId, Vec<u8>)>>) -> Self {
		let list = list.into();

		NotifsHandlerProto {
			in_handlers: list.clone().into_iter().map(|(p, e, _)| (NotifsInHandlerProto::new(p), e)).collect(),
			out_handlers: list.clone().into_iter().map(|(p, e, _)| (NotifsOutHandlerProto::new(p), e)).collect(),
			legacy: LegacyProtoHandlerProto::new(legacy),
		}
	}
}

impl<TSubstream> ProtocolsHandler for NotifsHandler<TSubstream>
where TSubstream: AsyncRead + AsyncWrite + Unpin + Send + 'static {
	type InEvent = NotifsHandlerIn;
	type OutEvent = NotifsHandlerOut;
	type Substream = TSubstream;
	type Error = EitherError<
		EitherError<
			<NotifsInHandler<Negotiated<TSubstream>> as ProtocolsHandler>::Error,
			<NotifsOutHandler<Negotiated<TSubstream>> as ProtocolsHandler>::Error,
		>,
		<LegacyProtoHandler<Negotiated<TSubstream>> as ProtocolsHandler>::Error,
	>;
	type InboundProtocol = SelectUpgrade<UpgradeCollec<NotificationsIn>, RegisteredProtocol>;
	type OutboundProtocol = EitherUpgrade<NotificationsOut, RegisteredProtocol>;
	// Index within the `out_handlers`; None for legacy
	type OutboundOpenInfo = Option<usize>;

	fn listen_protocol(&self) -> SubstreamProtocol<Self::InboundProtocol> {
		let in_handlers = self.in_handlers.iter()
			.map(|h| h.0.listen_protocol().into_upgrade().1)
			.collect::<UpgradeCollec<_>>();

		let proto = SelectUpgrade::new(in_handlers, self.legacy.listen_protocol().into_upgrade().1);
		SubstreamProtocol::new(proto)
	}

	fn inject_fully_negotiated_inbound(
		&mut self,
		out: <Self::InboundProtocol as InboundUpgrade<Negotiated<TSubstream>>>::Output
	) {
		match out {
			EitherOutput::First((out, num)) =>
				self.in_handlers[num].0.inject_fully_negotiated_inbound(out),
			EitherOutput::Second(out) =>
				self.legacy.inject_fully_negotiated_inbound(out),
		}
	}

	fn inject_fully_negotiated_outbound(
		&mut self,
		out: <Self::OutboundProtocol as OutboundUpgrade<Negotiated<TSubstream>>>::Output,
		num: Self::OutboundOpenInfo
	) {
		match (out, num) {
			(EitherOutput::First(out), Some(num)) =>
				self.out_handlers[num].0.inject_fully_negotiated_outbound(out, ()),
			(EitherOutput::Second(out), None) =>
				self.legacy.inject_fully_negotiated_outbound(out, ()),
			_ => error!("inject_fully_negotiated_outbound called with wrong parameters"),
		}
	}

	fn inject_event(&mut self, message: NotifsHandlerIn) {
		match message {
			NotifsHandlerIn::Enable => {
				self.enabled = EnabledState::Enabled;
				self.legacy.inject_event(LegacyProtoHandlerIn::Enable);
				for (handler, _) in &mut self.out_handlers {
					handler.inject_event(NotifsOutHandlerIn::Enable {
						initial_message: vec![]
					});
				}
				for num in self.pending_in.drain(..) {
					self.in_handlers[num].0.inject_event(NotifsInHandlerIn::Accept(vec![]));
				}
			},
			NotifsHandlerIn::Disable => {
				self.legacy.inject_event(LegacyProtoHandlerIn::Disable);
				// The notifications protocols start in the disabled state. If we were in the
				// "Initial" state, then we shouldn't disable the notifications protocols again.
				if self.enabled != EnabledState::Initial {
					for (handler, _) in &mut self.out_handlers {
						handler.inject_event(NotifsOutHandlerIn::Disable);
					}
				}
				self.enabled = EnabledState::Disabled;
				for num in self.pending_in.drain(..) {
					self.in_handlers[num].0.inject_event(NotifsInHandlerIn::Refuse);
				}
			},
			NotifsHandlerIn::SendLegacy { message } =>
				self.legacy.inject_event(LegacyProtoHandlerIn::SendCustomMessage { message }),
			NotifsHandlerIn::SendNotification { message, engine_id, proto_name } => {
				for (handler, ngn_id) in &mut self.out_handlers {
					if handler.protocol_name() != &proto_name[..] {
						break;
					}

					if handler.is_open() {
						handler.inject_event(NotifsOutHandlerIn::Send(message));
						return;
					} else {
						debug_assert_eq!(engine_id, *ngn_id);
					}
				}

				let message = GenericMessage::<(), (), (), ()>::Consensus(ConsensusMessage {
					engine_id,
					data: message,
				});

				self.legacy.inject_event(LegacyProtoHandlerIn::SendCustomMessage {
					message: message.encode()
				});
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
				self.out_handlers[num].0.inject_dial_upgrade_error(
					(),
					ProtocolsHandlerUpgrErr::Timeout
				),
			(ProtocolsHandlerUpgrErr::Timeout, None) =>
				self.legacy.inject_dial_upgrade_error((), ProtocolsHandlerUpgrErr::Timeout),
			(ProtocolsHandlerUpgrErr::Timer, Some(num)) =>
				self.out_handlers[num].0.inject_dial_upgrade_error(
					(),
					ProtocolsHandlerUpgrErr::Timer
				),
			(ProtocolsHandlerUpgrErr::Timer, None) =>
				self.legacy.inject_dial_upgrade_error((), ProtocolsHandlerUpgrErr::Timer),
			(ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Select(err)), Some(num)) =>
				self.out_handlers[num].0.inject_dial_upgrade_error(
					(),
					ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Select(err))
				),
			(ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Select(err)), None) =>
				self.legacy.inject_dial_upgrade_error(
					(),
					ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Select(err))
				),
			(ProtocolsHandlerUpgrErr::Upgrade(UpgradeError::Apply(EitherError::A(err))), Some(num)) =>
				self.out_handlers[num].0.inject_dial_upgrade_error(
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

		for (handler, _) in &self.in_handlers {
			let val = handler.connection_keep_alive();
			if val.is_yes() {
				return KeepAlive::Yes;
			}
			if ret < val { ret = val; }
		}

		for (handler, _) in &self.out_handlers {
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
		cx: &mut Context,
	) -> Poll<
		ProtocolsHandlerEvent<Self::OutboundProtocol, Self::OutboundOpenInfo, Self::OutEvent, Self::Error>
	> {
		for (handler_num, (handler, engine_id)) in self.in_handlers.iter_mut().enumerate() {
			while let Poll::Ready(ev) = handler.poll(cx) {
				match ev {
					ProtocolsHandlerEvent::OutboundSubstreamRequest { .. } =>
						error!("Incoming substream handler tried to open a substream"),
					ProtocolsHandlerEvent::Close(err) => void::unreachable(err),
					ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::OpenRequest(_)) =>
						match self.enabled {
							EnabledState::Initial => self.pending_in.push(handler_num),
							EnabledState::Enabled =>
								handler.inject_event(NotifsInHandlerIn::Accept(vec![])),
							EnabledState::Disabled =>
								handler.inject_event(NotifsInHandlerIn::Refuse),
						},
					ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::Closed) => {},
					ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::Notif(message)) => {
						// Note that right now the legacy substream has precedence over
						// everything. If it is not open, then we consider that nothing is open.
						if self.legacy.is_open() {
							let msg = NotifsHandlerOut::Notification {
								message,
								engine_id: *engine_id,
								proto_name: handler.protocol_name().to_owned().into(),
							};
							return Poll::Ready(ProtocolsHandlerEvent::Custom(msg));
						}
					},
				}
			}
		}

		for (handler_num, (handler, _)) in self.out_handlers.iter_mut().enumerate() {
			while let Poll::Ready(ev) = handler.poll(cx) {
				match ev {
					ProtocolsHandlerEvent::OutboundSubstreamRequest { protocol, info: () } =>
						return Poll::Ready(ProtocolsHandlerEvent::OutboundSubstreamRequest {
							protocol: protocol.map_upgrade(EitherUpgrade::A),
							info: Some(handler_num),
						}),
					ProtocolsHandlerEvent::Close(err) => void::unreachable(err),

					// At the moment we don't actually care whether any notifications protocol
					// opens or closes.
					// Whether our communications with the remote are open or closed entirely
					// depends on the legacy substream, because as long as we are open the user of
					// this struct might try to send legacy protocol messages which we need to
					// deliver for things to work properly.
					ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Open { .. }) => {},
					ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Closed) => {},
					ProtocolsHandlerEvent::Custom(NotifsOutHandlerOut::Refused) => {},
				}
			}
		}

		while let Poll::Ready(ev) = self.legacy.poll(cx) {
			match ev {
				ProtocolsHandlerEvent::OutboundSubstreamRequest { protocol, info: () } =>
					return Poll::Ready(ProtocolsHandlerEvent::OutboundSubstreamRequest {
						protocol: protocol.map_upgrade(EitherUpgrade::B),
						info: None,
					}),
				ProtocolsHandlerEvent::Custom(LegacyProtoHandlerOut::CustomProtocolOpen { .. }) =>
					return Poll::Ready(ProtocolsHandlerEvent::Custom(
						NotifsHandlerOut::Open
					)),
				ProtocolsHandlerEvent::Custom(LegacyProtoHandlerOut::CustomProtocolClosed { reason }) =>
					return Poll::Ready(ProtocolsHandlerEvent::Custom(
						NotifsHandlerOut::Closed { reason }
					)),
				ProtocolsHandlerEvent::Custom(LegacyProtoHandlerOut::CustomMessage { message }) =>
					return Poll::Ready(ProtocolsHandlerEvent::Custom(
						NotifsHandlerOut::CustomMessage { message }
					)),
				ProtocolsHandlerEvent::Custom(LegacyProtoHandlerOut::Clogged { messages }) =>
					return Poll::Ready(ProtocolsHandlerEvent::Custom(
						NotifsHandlerOut::Clogged { messages }
					)),
				ProtocolsHandlerEvent::Custom(LegacyProtoHandlerOut::ProtocolError { is_severe, error }) =>
					return Poll::Ready(ProtocolsHandlerEvent::Custom(
						NotifsHandlerOut::ProtocolError { is_severe, error }
					)),
				ProtocolsHandlerEvent::Close(err) =>
					return Poll::Ready(ProtocolsHandlerEvent::Close(EitherError::B(err))),
			}
		}

		Poll::Pending
	}
}
