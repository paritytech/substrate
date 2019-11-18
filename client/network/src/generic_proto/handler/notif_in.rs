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

use crate::generic_proto::upgrade::{NotificationsIn, NotificationsInSubstream};
use bytes::BytesMut;
use futures::prelude::*;
use libp2p::core::{ConnectedPoint, PeerId, Endpoint};
use libp2p::core::upgrade::{DeniedUpgrade, InboundUpgrade, OutboundUpgrade};
use libp2p::swarm::{
	ProtocolsHandler, ProtocolsHandlerEvent,
	IntoProtocolsHandler,
	KeepAlive,
	ProtocolsHandlerUpgrErr,
	SubstreamProtocol,
};
use log::{error, warn};
use smallvec::SmallVec;
use std::{borrow::Cow, error, fmt, marker::PhantomData};
use tokio_io::{AsyncRead, AsyncWrite};

/// Implements the `IntoProtocolsHandler` trait of libp2p.
///
/// Every time a connection with a remote starts, an instance of this struct is created and
/// sent to a background task dedicated to this connection. Once the connection is established,
/// it is turned into a [`NotifsInHandler`].
pub struct NotifsInHandlerProto<TSubstream> {
	/// Configuration for the protocol upgrade to negotiate.
	in_protocol: NotificationsIn,

	/// Marker to pin the generic type.
	marker: PhantomData<TSubstream>,
}

impl<TSubstream> NotifsInHandlerProto<TSubstream> {
	/// Builds a new `NotifsInHandlerProto`.
	pub fn new(
		proto_name: impl Into<Cow<'static, [u8]>>
	) -> Self {
		NotifsInHandlerProto {
			in_protocol: NotificationsIn::new(proto_name),
			marker: PhantomData,
		}
	}
}

impl<TSubstream> IntoProtocolsHandler for NotifsInHandlerProto<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite + 'static,
{
	type Handler = NotifsInHandler<TSubstream>;

	fn inbound_protocol(&self) -> NotificationsIn {
		self.in_protocol.clone()
	}

	fn into_handler(self, remote_peer_id: &PeerId, connected_point: &ConnectedPoint) -> Self::Handler {
		NotifsInHandler {
			in_protocol: self.in_protocol,
			substream: None,
			pending_accept_refuses: 0,
			endpoint: connected_point.to_endpoint(),
			remote_peer_id: remote_peer_id.clone(),
			events_queue: SmallVec::new(),
		}
	}
}

/// The actual handler once the connection has been established.
pub struct NotifsInHandler<TSubstream> {
	/// Configuration for the protocol upgrade to negotiate for inbound substreams.
	in_protocol: NotificationsIn,

	/// Identifier of the node we're talking to. Used only for logging purposes and shouldn't have
	/// any influence on the behaviour.
	// TODO: remove?
	remote_peer_id: PeerId,

	/// Whether we are the connection dialer or listener. Used only for logging purposes and
	/// shouldn't have any influence on the behaviour.
	// TODO: remove?
	endpoint: Endpoint,

	/// Substream that is open with the remote.
	substream: Option<NotificationsInSubstream<TSubstream>>,

	/// If the substream is opened and closed rapidly, we can emit several `OpenRequest` messages
	/// without the handler having time to respond with `Accept` or `Refuse`. Every time an
	/// `OpenRequest` is emitted, we increment this variable in order to keep the state consistent.
	pending_accept_refuses: usize,

	/// Queue of events to send to the outside.
	///
	/// This queue must only ever be modified to insert elements at the back, or remove the first
	/// element.
	events_queue: SmallVec<[ProtocolsHandlerEvent<DeniedUpgrade, (), NotifsInHandlerOut>; 16]>,
}

/// Event that can be received by a `NotifsInHandler`.
#[derive(Debug)]
pub enum NotifsInHandlerIn {
	/// Can be sent back as a response to an `OpenRequest`. Contains the status message to send
	/// to the remote.
	///
	/// The substream is now considered open, and `Notif` events can be received.
	Accept(Vec<u8>),

	/// Can be sent back as a response to an `OpenRequest`.
	Refuse,
}

/// Event that can be emitted by a `NotifsInHandler`.
#[derive(Debug)]
pub enum NotifsInHandlerOut {
	/// The remote wants to open a substream.
	///
	/// Every time this event is emitted, a corresponding `Accepted` or `Refused` **must** be sent
	/// back.
	OpenRequest,

	/// The notifications substream has been closed by the remote. In order to avoid race
	/// conditions, this does **not** cancel any previously-sent `OpenRequest`.
	Closed,

	/// Received a message on the notifications substream.
	///
	/// Can only happen after an `Accept` and before a `Closed`.
	Notif(BytesMut),
}

impl<TSubstream> NotifsInHandler<TSubstream> {
	/// Returns the name of the protocol that we accept.
	pub fn protocol_name(&self) -> &[u8] {
		self.in_protocol.protocol_name()
	}
}

impl<TSubstream> ProtocolsHandler for NotifsInHandler<TSubstream>
where TSubstream: AsyncRead + AsyncWrite + 'static {
	type InEvent = NotifsInHandlerIn;
	type OutEvent = NotifsInHandlerOut;
	type Substream = TSubstream;
	type Error = ConnectionKillError;
	type InboundProtocol = NotificationsIn;
	type OutboundProtocol = DeniedUpgrade;
	type OutboundOpenInfo = ();

	fn listen_protocol(&self) -> SubstreamProtocol<Self::InboundProtocol> {
		SubstreamProtocol::new(self.in_protocol.clone())
	}

	fn inject_fully_negotiated_inbound(
		&mut self,
		proto: <Self::InboundProtocol as InboundUpgrade<TSubstream>>::Output
	) {
		if self.substream.is_some() {
			warn!(target: "sub-libp2p", "Received duplicate inbound substream");
			return;
		}

		self.substream = Some(proto);
		self.events_queue.push(ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::OpenRequest));
		self.pending_accept_refuses += 1;
	}

	fn inject_fully_negotiated_outbound(
		&mut self,
		out: <Self::OutboundProtocol as OutboundUpgrade<TSubstream>>::Output,
		_: Self::OutboundOpenInfo
	) {
		// We never emit any outgoing substream.
		void::unreachable(out)
	}

	fn inject_event(&mut self, message: NotifsInHandlerIn) {
		self.pending_accept_refuses = match self.pending_accept_refuses.checked_sub(1) {
			Some(v) => v,
			None => {
				error!(target: "sub-libp2p", "Inconsistent state: received Accept/Refuse when no \
					pending request exists");
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

	fn inject_dial_upgrade_error(&mut self, _: (), err: ProtocolsHandlerUpgrErr<void::Void>) {
		unimplemented!()		// TODO:
		/*let is_severe = match err {
			ProtocolsHandlerUpgrErr::Upgrade(_) => true,
			_ => false,
		};

		self.events_queue.push(ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::ProtocolError {
			is_severe,
			error: Box::new(err),
		}));*/
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
	) -> Poll<
		ProtocolsHandlerEvent<Self::OutboundProtocol, Self::OutboundOpenInfo, Self::OutEvent>,
		Self::Error,
	> {
		// Flush the events queue if necessary.
		if !self.events_queue.is_empty() {
			let event = self.events_queue.remove(0);
			return Ok(Async::Ready(event))
		}

		if let Some(substream) = self.substream.as_mut() {
			match substream.poll() {
				Ok(Async::Ready(Some(msg))) =>
					return Ok(Async::Ready(ProtocolsHandlerEvent::Custom(NotifsInHandlerOut::Notif(msg)))),
				Ok(Async::NotReady) => {},
				Ok(Async::Ready(None)) | Err(_) => return Err(ConnectionKillError),		// TODO: ?
			}
		}

		Ok(Async::NotReady)
	}
}

impl<TSubstream> fmt::Debug for NotifsInHandler<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
{
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
		f.debug_struct("NotifsInHandler")
			.finish()
	}
}

// TODO: remove
#[derive(Debug)]
pub struct ConnectionKillError;

impl error::Error for ConnectionKillError {
}

impl fmt::Display for ConnectionKillError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		unimplemented!()		// TODO:
	}
}
