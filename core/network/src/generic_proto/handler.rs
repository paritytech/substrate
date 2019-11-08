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

use crate::generic_proto::upgrade::{NotificationsIn, NotificationsOut, RequestResponse, Responder, ResponderResponse, SelectUpgrade};
use futures::prelude::*;
use libp2p::core::{ConnectedPoint, PeerId, Endpoint};
use libp2p::core::either::EitherError;
use libp2p::core::upgrade::{EitherUpgrade, ReadOneError, InboundUpgrade, OutboundUpgrade};
use libp2p::swarm::{
	ProtocolsHandler, ProtocolsHandlerEvent,
	IntoProtocolsHandler,
	KeepAlive,
	ProtocolsHandlerUpgrErr,
	SubstreamProtocol,
};
use smallvec::SmallVec;
use std::{borrow::Cow, error, fmt, marker::PhantomData, time::Duration};
use tokio_io::{AsyncRead, AsyncWrite};

/// Implements the `IntoProtocolsHandler` trait of libp2p.
///
/// Every time a connection with a remote starts, an instance of this struct is created and
/// sent to a background task dedicated to this connection. Once the connection is established,
/// it is turned into a [`CustomProtoHandler`].
pub struct CustomProtoHandlerProto<TSubstream> {
	/// Configuration for the protocol upgrade to negotiate.
	in_protocol: SelectUpgrade<NotificationsIn, Responder>,

	/// Marker to pin the generic type.
	marker: PhantomData<TSubstream>,
}

impl<TSubstream> CustomProtoHandlerProto<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
{
	/// Builds a new `CustomProtoHandlerProto`.
	pub fn new() -> Self {
		CustomProtoHandlerProto {
			in_protocol: SelectUpgrade(Default::default(), Default::default()),
			marker: PhantomData,
		}
	}
}

impl<TSubstream> IntoProtocolsHandler for CustomProtoHandlerProto<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite + 'static,
{
	type Handler = CustomProtoHandler<TSubstream>;

	fn inbound_protocol(&self) -> SelectUpgrade<NotificationsIn, Responder> {
		self.in_protocol.clone()
	}

	fn into_handler(self, remote_peer_id: &PeerId, connected_point: &ConnectedPoint) -> Self::Handler {
		CustomProtoHandler {
			in_protocol: self.in_protocol,
			endpoint: connected_point.to_endpoint(),
			remote_peer_id: remote_peer_id.clone(),
			events_queue: SmallVec::new(),
		}
	}
}

/// The actual handler once the connection has been established.
pub struct CustomProtoHandler<TSubstream> {
	/// Configuration for the protocol upgrade to negotiate for inbound substreams.
	in_protocol: SelectUpgrade<NotificationsIn, Responder>,

	/// Identifier of the node we're talking to. Used only for logging purposes and shouldn't have
	/// any influence on the behaviour.
	remote_peer_id: PeerId,

	/// Whether we are the connection dialer or listener. Used only for logging purposes and
	/// shouldn't have any influence on the behaviour.
	endpoint: Endpoint,

	/// Queue of events to send to the outside.
	///
	/// This queue must only ever be modified to insert elements at the back, or remove the first
	/// element.
	events_queue: SmallVec<[ProtocolsHandlerEvent<EitherUpgrade<NotificationsOut, RequestResponse>, (), CustomProtoHandlerOut<TSubstream>>; 16]>,
}

/// Event that can be received by a `CustomProtoHandler`.
#[derive(Debug)]
pub enum CustomProtoHandlerIn {
	/// Open a substream for notifications.
	OpenNotif {
		/// Identifier for the substream. Decided by the user.
		unique_id: u64,		// TODO: strongly typed user data?
		/// Name of the protocol for the substream.
		proto_name: Cow<'static, [u8]>,
	},

	/// Whenever a remote opens a notifications substream, we send to it a "node information"
	/// handshake message. This message is cached in the `ProtocolsHandler`, and `UpdateNodeInfos`
	/// updates this cached message.
	UpdateNodeInfos {
		/// Name of the protocol to upgrade node information for.
		proto_name: Cow<'static, [u8]>,
		/// Information sent to the remote.
		infos: Vec<u8>,
	},

	/// Open a substream and send a request on it. Wait for an answer.
	SendRequest {
		/// Identifier for the request. Decided by the user.
		unique_id: u64,
		/// Name of the protocol for the substream where the request is sent.
		proto_name: Cow<'static, [u8]>,
		/// Message to send on the substream.
		message: Vec<u8>,
		/// Time after which we stop waiting for an answer.
		timeout: Duration,
	},
}

/// Event that can be emitted by a `CustomProtoHandler`.
#[derive(Debug)]
pub enum CustomProtoHandlerOut<TSubstream> {
	/// Received a request from a remote, and we should answer it.
	Request {
		/// Object that allows answering the request.
		responder: ResponderResponse<TSubstream>,
	},

	/// A response to a request-response has been received.
	Response {
		/// Matches the value passed in [`CustomProtoHandlerIn::Request`].
		unique_id: u64,
		/// Response received from the remote.
		response: Vec<u8>,
	},

	/// A gossiping substream has been open.
	GossipOpen {
		/// Name of the protocol that's been open.
		proto_name: String,
		/// Message that the remote sent for the handshake. Usually contains important
		/// information about the gossiping.
		handshake_message: String,
	},

	/// A gossiping substream has been closed by the remote.
	GossipClosed {
	},

	/// Receives a message on a gossiping substream.
	GossipMessage {
		/// Message that has been received.
		message: Vec<u8>,
	},

	/// An error has happened on the protocol level with this node.
	ProtocolError {
		/// If true the error is severe, such as a protocol violation.
		is_severe: bool,
		/// The error that happened.
		error: Box<dyn error::Error + Send + Sync>,
	},
}

impl<TSubstream> ProtocolsHandler for CustomProtoHandler<TSubstream>
where TSubstream: AsyncRead + AsyncWrite + 'static {
	type InEvent = CustomProtoHandlerIn;
	type OutEvent = CustomProtoHandlerOut<TSubstream>;
	type Substream = TSubstream;
	type Error = ConnectionKillError;
	type InboundProtocol = SelectUpgrade<NotificationsIn, Responder>;
	type OutboundProtocol = EitherUpgrade<NotificationsOut, RequestResponse>;
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
		proto: <Self::OutboundProtocol as OutboundUpgrade<TSubstream>>::Output,
		_: Self::OutboundOpenInfo
	) {
		unimplemented!()
	}

	fn inject_event(&mut self, message: CustomProtoHandlerIn) {
		match message {
			/*CustomProtoHandlerIn::OpenNotif { } => {
				self.events_queue.push(ProtocolsHandlerEvent::OutboundSubstreamRequest {
					protocol: SubstreamProtocol::new(self.protocol.clone()),
					info: (),
				});
			},*/
			CustomProtoHandlerIn::SendRequest { unique_id, proto_name, message, timeout } => {
				let protocol = RequestResponse::new(proto_name, message);

				self.events_queue.push(ProtocolsHandlerEvent::OutboundSubstreamRequest {
					protocol: SubstreamProtocol::new(EitherUpgrade::B(protocol))
						.with_timeout(timeout),
					info: (),
				});
			},
			_ => unimplemented!()		// TODO:
		}
	}

	fn inject_dial_upgrade_error(&mut self, _: (), err: ProtocolsHandlerUpgrErr<EitherError<ReadOneError, ReadOneError>>) {
		let is_severe = match err {
			ProtocolsHandlerUpgrErr::Upgrade(_) => true,
			_ => false,
		};

		self.events_queue.push(ProtocolsHandlerEvent::Custom(CustomProtoHandlerOut::ProtocolError {
			is_severe,
			error: Box::new(err),
		}));
	}

	fn connection_keep_alive(&self) -> KeepAlive {
		KeepAlive::Yes
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

impl<TSubstream> fmt::Debug for CustomProtoHandler<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
{
	fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
		f.debug_struct("CustomProtoHandler")
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
