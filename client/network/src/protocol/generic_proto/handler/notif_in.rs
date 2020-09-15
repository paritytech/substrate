// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Implementations of the `IntoProtocolsHandler` and `ProtocolsHandler` traits for ingoing
//! substreams for a single gossiping protocol.
//!
//! > **Note**: Each instance corresponds to a single protocol. In order to support multiple
//! >			protocols, you need to create multiple instances and group them.
//!

use crate::protocol::generic_proto::upgrade::{NotificationsIn, NotificationsInSubstream};
use bytes::BytesMut;
use futures::prelude::*;
use libp2p::core::{ConnectedPoint, PeerId};
use libp2p::core::upgrade::{DeniedUpgrade, InboundUpgrade, OutboundUpgrade};
use libp2p::swarm::{
	ProtocolsHandler, ProtocolsHandlerEvent,
	IntoProtocolsHandler,
	KeepAlive,
	ProtocolsHandlerUpgrErr,
	SubstreamProtocol,
	NegotiatedSubstream,
};
use log::{error, warn};
use std::{borrow::Cow, collections::VecDeque, fmt, pin::Pin, task::{Context, Poll}};

/// Implements the `IntoProtocolsHandler` trait of libp2p.
///
/// Every time a connection with a remote starts, an instance of this struct is created and
/// sent to a background task dedicated to this connection. Once the connection is established,
/// it is turned into a [`NotifsInHandler`].
pub struct NotifsInHandlerProto {
	/// Configuration for the protocol upgrade to negotiate.
	in_protocol: NotificationsIn,
}

/// The actual handler once the connection has been established.
pub struct NotifsInHandler {
	/// Configuration for the protocol upgrade to negotiate for inbound substreams.
	in_protocol: NotificationsIn,

	/// Substream that is open with the remote.
	substream: Option<NotificationsInSubstream<NegotiatedSubstream>>,

	/// If the substream is opened and closed rapidly, we can emit several `OpenRequest` and
	/// `Closed` messages in a row without the handler having time to respond with `Accept` or
	/// `Refuse`.
	///
	/// In order to keep the state consistent, we increment this variable every time an
	/// `OpenRequest` is emitted and decrement it every time an `Accept` or `Refuse` is received.
	pending_accept_refuses: usize,

	/// Queue of events to send to the outside.
	///
	/// This queue is only ever modified to insert elements at the back, or remove the first
	/// element.
	events_queue: VecDeque<ProtocolsHandlerEvent<DeniedUpgrade, (), NotifsInHandlerOut, void::Void>>,
}

/// Event that can be received by a `NotifsInHandler`.
#[derive(Debug, Clone)]
pub enum NotifsInHandlerIn {
	/// Can be sent back as a response to an `OpenRequest`. Contains the status message to send
	/// to the remote.
	///
	/// After sending this to the handler, the substream is now considered open and `Notif` events
	/// can be received.
	Accept(Vec<u8>),

	/// Can be sent back as a response to an `OpenRequest`.
	Refuse,
}

/// Event that can be emitted by a `NotifsInHandler`.
#[derive(Debug)]
pub enum NotifsInHandlerOut {
	/// The remote wants to open a substream. Contains the initial message sent by the remote
	/// when the substream has been opened.
	///
	/// Every time this event is emitted, a corresponding `Accepted` or `Refused` **must** be sent
	/// back even if a `Closed` is received.
	OpenRequest(Vec<u8>),

	/// The notifications substream has been closed by the remote. In order to avoid race
	/// conditions, this does **not** cancel any previously-sent `OpenRequest`.
	Closed,

	/// Received a message on the notifications substream.
	///
	/// Can only happen after an `Accept` and before a `Closed`.
	Notif(BytesMut),
}

impl NotifsInHandlerProto {
	/// Builds a new `NotifsInHandlerProto`.
	pub fn new(
		protocol_name: impl Into<Cow<'static, str>>
	) -> Self {
		NotifsInHandlerProto {
			in_protocol: NotificationsIn::new(protocol_name),
		}
	}
}

impl IntoProtocolsHandler for NotifsInHandlerProto {
	type Handler = NotifsInHandler;

	fn inbound_protocol(&self) -> NotificationsIn {
		self.in_protocol.clone()
	}

	fn into_handler(self, _: &PeerId, _: &ConnectedPoint) -> Self::Handler {
		NotifsInHandler {
			in_protocol: self.in_protocol,
			substream: None,
			pending_accept_refuses: 0,
			events_queue: VecDeque::new(),
		}
	}
}

impl NotifsInHandler {
	/// Returns the name of the protocol that we accept.
	pub fn protocol_name(&self) -> &Cow<'static, str> {
		self.in_protocol.protocol_name()
	}

	/// Equivalent to the `poll` method of `ProtocolsHandler`, except that it is guaranteed to
	/// never generate [`NotifsInHandlerOut::Notif`].
	///
	/// Use this method in situations where it is not desirable to receive events but still
	/// necessary to drive any potential incoming handshake or request.
	pub fn poll_process(
		&mut self,
		cx: &mut Context
	) -> Poll<
		ProtocolsHandlerEvent<DeniedUpgrade, (), NotifsInHandlerOut, void::Void>
	> {
		if let Some(event) = self.events_queue.pop_front() {
			return Poll::Ready(event)
		}

		match self.substream.as_mut().map(|s| NotificationsInSubstream::poll_process(Pin::new(s), cx)) {
			None | Some(Poll::Pending) => {},
			Some(Poll::Ready(Ok(v))) => match v {},
			Some(Poll::Ready(Err(_))) => {
				self.substream = None;
				return Poll::Ready(ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::Closed));
			},
		}

		Poll::Pending
	}
}

impl ProtocolsHandler for NotifsInHandler {
	type InEvent = NotifsInHandlerIn;
	type OutEvent = NotifsInHandlerOut;
	type Error = void::Void;
	type InboundProtocol = NotificationsIn;
	type OutboundProtocol = DeniedUpgrade;
	type OutboundOpenInfo = ();
	type InboundOpenInfo = ();

	fn listen_protocol(&self) -> SubstreamProtocol<Self::InboundProtocol, ()> {
		SubstreamProtocol::new(self.in_protocol.clone(), ())
	}

	fn inject_fully_negotiated_inbound(
		&mut self,
		(msg, proto): <Self::InboundProtocol as InboundUpgrade<NegotiatedSubstream>>::Output,
		(): ()
	) {
		// If a substream already exists, we drop it and replace it with the new incoming one.
		if self.substream.is_some() {
			self.events_queue.push_back(ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::Closed));
		}

		// Note that we drop the existing substream, which will send an equivalent to a TCP "RST"
		// to the remote and force-close the substream. It might seem like an unclean way to get
		// rid of a substream. However, keep in mind that it is invalid for the remote to open
		// multiple such substreams, and therefore sending a "RST" is not an incorrect thing to do.
		self.substream = Some(proto);

		self.events_queue.push_back(ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::OpenRequest(msg)));
		self.pending_accept_refuses = self.pending_accept_refuses
			.checked_add(1)
			.unwrap_or_else(|| {
				error!(target: "sub-libp2p", "Overflow in pending_accept_refuses");
				usize::max_value()
			});
	}

	fn inject_fully_negotiated_outbound(
		&mut self,
		out: <Self::OutboundProtocol as OutboundUpgrade<NegotiatedSubstream>>::Output,
		_: Self::OutboundOpenInfo
	) {
		// We never emit any outgoing substream.
		void::unreachable(out)
	}

	fn inject_event(&mut self, message: NotifsInHandlerIn) {
		self.pending_accept_refuses = match self.pending_accept_refuses.checked_sub(1) {
			Some(v) => v,
			None => {
				error!(
					target: "sub-libp2p",
					"Inconsistent state: received Accept/Refuse when no pending request exists"
				);
				return;
			}
		};

		// If we send multiple `OpenRequest`s in a row, we will receive back multiple
		// `Accept`/`Refuse` messages. All of them are obsolete except the last one.
		if self.pending_accept_refuses != 0 {
			return;
		}

		match (message, self.substream.as_mut()) {
			(NotifsInHandlerIn::Accept(message), Some(sub)) => sub.send_handshake(message),
			(NotifsInHandlerIn::Accept(_), None) => {},
			(NotifsInHandlerIn::Refuse, _) => self.substream = None,
		}
	}

	fn inject_dial_upgrade_error(&mut self, _: (), _: ProtocolsHandlerUpgrErr<void::Void>) {
		error!(target: "sub-libp2p", "Received dial upgrade error in inbound-only handler");
	}

	fn connection_keep_alive(&self) -> KeepAlive {
		if self.substream.is_some() {
			KeepAlive::Yes
		} else {
			KeepAlive::No
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

		match self.substream.as_mut().map(|s| Stream::poll_next(Pin::new(s), cx)) {
			None | Some(Poll::Pending) => {},
			Some(Poll::Ready(Some(Ok(msg)))) => {
				if self.pending_accept_refuses != 0 {
					warn!(
						target: "sub-libp2p",
						"Bad state in inbound-only handler: notif before accepting substream"
					);
				}
				return Poll::Ready(ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::Notif(msg)))
			},
			Some(Poll::Ready(None)) | Some(Poll::Ready(Some(Err(_)))) => {
				self.substream = None;
				return Poll::Ready(ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::Closed));
			},
		}

		Poll::Pending
	}
}

impl fmt::Debug for NotifsInHandler {
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
		f.debug_struct("NotifsInHandler")
			.field("substream_open", &self.substream.is_some())
			.finish()
	}
}
