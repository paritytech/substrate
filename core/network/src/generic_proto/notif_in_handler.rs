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

use crate::generic_proto::upgrade::NotificationsIn;
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

impl<TSubstream> NotifsInHandlerProto<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
{
	/// Builds a new `NotifsInHandlerProto`.
	pub fn new(proto_name: impl Into<Cow<'static, [u8]>>, handshake_msg: impl Into<Vec<u8>>) -> Self {
		NotifsInHandlerProto {
			in_protocol: NotificationsIn::new(proto_name, handshake_msg),
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
			endpoint: connected_point.to_endpoint(),
			remote_peer_id: remote_peer_id.clone(),
			events_queue: SmallVec::new(),
			marker: PhantomData,
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

	/// Queue of events to send to the outside.
	///
	/// This queue must only ever be modified to insert elements at the back, or remove the first
	/// element.
	events_queue: SmallVec<[ProtocolsHandlerEvent<DeniedUpgrade, (), NotifsInHandlerOut>; 16]>,

	/// Marker to pin the generic type.
	marker: PhantomData<TSubstream>,
}

/// Event that can be received by a `NotifsInHandler`.
#[derive(Debug)]
pub enum NotifsInHandlerIn {
	/// Whenever a remote opens a notifications substream, we send to it a "node information"
	/// handshake message. This message is cached in the `ProtocolsHandler`, and `UpdateNodeInfos`
	/// updates this cached message.
	UpdateNodeInfos {
		/// Information sent to the remote.
		infos: Vec<u8>,
	},
}

/// Event that can be emitted by a `NotifsInHandler`.
#[derive(Debug)]
pub enum NotifsInHandlerOut {
	/// The notifications substream has been open by the remote.
	NotifOpen,

	/// The notifications substream has been closed by the remote.
	NotifClosed,

	/// Received a message on the notifications substream.
	///
	/// Can only happen after a `NotifOpen` and before a `NotifClosed`.
	Notif(Vec<u8>),

	// TODO: needed?
	/*/// An error has happened on the protocol level with this node.
	ProtocolError {
		/// If true the error is severe, such as a protocol violation.
		is_severe: bool,
		/// The error that happened.
		error: Box<dyn error::Error + Send + Sync>,
	},*/
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
		unimplemented!()
	}

	fn inject_fully_negotiated_outbound(
		&mut self,
		out: <Self::OutboundProtocol as OutboundUpgrade<TSubstream>>::Output,
		_: Self::OutboundOpenInfo
	) {
		// We never emit any outgoing substream.
		match out {}
	}

	fn inject_event(&mut self, message: NotifsInHandlerIn) {
		match message {
			NotifsInHandlerIn::UpdateNodeInfos { infos } =>
				self.in_protocol.set_handshake_message(infos),
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
		KeepAlive::No
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

#[derive(Debug)]
pub struct ConnectionKillError;

impl error::Error for ConnectionKillError {
}

impl fmt::Display for ConnectionKillError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		unimplemented!()		// TODO:
	}
}
