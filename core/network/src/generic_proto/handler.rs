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

use crate::legacy_proto::upgrade::{RegisteredProtocol, RegisteredProtocolEvent, RegisteredProtocolSubstream};
use bytes::BytesMut;
use futures::prelude::*;
use futures03::{compat::Compat, TryFutureExt as _};
use futures_timer::Delay;
use libp2p::core::{ConnectedPoint, PeerId, Endpoint};
use libp2p::core::upgrade::{InboundUpgrade, OutboundUpgrade};
use libp2p::swarm::{
	OneShotHandler,
	ProtocolsHandler, ProtocolsHandlerEvent,
	IntoProtocolsHandler,
	KeepAlive,
	ProtocolsHandlerUpgrErr,
	SubstreamProtocol,
};
use log::{debug, error};
use smallvec::{smallvec, SmallVec};
use std::{borrow::Cow, error, fmt, io, marker::PhantomData, mem, time::Duration};
use tokio_io::{AsyncRead, AsyncWrite};

/// Implements the `IntoProtocolsHandler` trait of libp2p.
///
/// Every time a connection with a remote starts, an instance of this struct is created and
/// sent to a background task dedicated to this connection. Once the connection is established,
/// it is turned into a `CustomProtoHandler`. It then handles all communications that are specific
/// to Substrate on that single connection.
///
/// Note that there can be multiple instance of this struct simultaneously for same peer. However
/// if that happens, only one main instance can communicate with the outer layers of the code. In
/// other words, the outer layers of the code only ever see one handler.
///
/// ## State of the handler
///
/// There are six possible states for the handler:
///
/// - Enabled and open, which is a normal operation.
/// - Enabled and closed, in which case it will try to open substreams.
/// - Disabled and open, in which case it will try to close substreams.
/// - Disabled and closed, in which case the handler is idle. The connection will be
///   garbage-collected after a few seconds if nothing more happens.
/// - Initializing and open.
/// - Initializing and closed, which is the state the handler starts in.
///
/// The Init/Enabled/Disabled state is entirely controlled by the user by sending `Enable` or
/// `Disable` messages to the handler. The handler itself never transitions automatically between
/// these states. For example, if the handler reports a network misbehaviour, it will close the
/// substreams but it is the role of the user to send a `Disabled` event if it wants the connection
/// to close. Otherwise, the handler will try to reopen substreams.
/// The handler starts in the "Initializing" state and must be transitionned to Enabled or Disabled
/// as soon as possible.
///
/// The Open/Closed state is decided by the handler and is reported with the `CustomProtocolOpen`
/// and `CustomProtocolClosed` events. The `CustomMessage` event can only be generated if the
/// handler is open.
///
/// ## How it works
///
/// When the handler is created, it is initially in the `Init` state and waits for either a
/// `Disable` or an `Enable` message from the outer layer. At any time, the outer layer is free to
/// toggle the handler between the disabled and enabled states.
///
/// When the handler switches to "enabled", it opens a substream and negotiates the protocol named
/// `/substrate/xxx`, where `xxx` is chosen by the user and depends on the chain.
///
/// For backwards compatibility reasons, when we switch to "enabled" for the first time (while we
/// are still in "init" mode) and we are the connection listener, we don't open a substream.
///
/// In order the handle the situation where both the remote and us get enabled at the same time,
/// we tolerate multiple substreams open at the same time. Messages are transmitted on an arbitrary
/// substream. The endpoints don't try to agree on a single substream.
///
/// We consider that we are now "closed" if the remote closes all the existing substreams.
/// Re-opening it can then be performed by closing all active substream and re-opening one.
///
pub struct CustomProtoHandlerProto<TSubstream> {
	/// Configuration for the protocol upgrade to negotiate.
	protocol: RegisteredProtocol,

	/// Marker to pin the generic type.
	marker: PhantomData<TSubstream>,
}

impl<TSubstream> CustomProtoHandlerProto<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
{
	/// Builds a new `CustomProtoHandlerProto`.
	pub fn new(protocol: RegisteredProtocol) -> Self {
		CustomProtoHandlerProto {
			requests_responses: OneShotHandler::new(proto, Duration::from_secs(20)),
			protocol,
			marker: PhantomData,
		}
	}
}

impl<TSubstream> IntoProtocolsHandler for CustomProtoHandlerProto<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
{
	type Handler = CustomProtoHandler<TSubstream>;

	fn inbound_protocol(&self) -> RegisteredProtocol {
		self.protocol.clone()
	}

	fn into_handler(self, remote_peer_id: &PeerId, connected_point: &ConnectedPoint) -> Self::Handler {
		CustomProtoHandler {
			protocol: self.protocol,
			endpoint: connected_point.to_endpoint(),
			remote_peer_id: remote_peer_id.clone(),
			state: ProtocolState::Init {
				substreams: SmallVec::new(),
				init_deadline: Delay::new(Duration::from_secs(5)).compat()
			},
			events_queue: SmallVec::new(),
		}
	}
}

/// The actual handler once the connection has been established.
pub struct CustomProtoHandler<TSubstream> {
	/// Configuration for the protocol upgrade to negotiate.
	protocol: RegisteredProtocol,

	/// State of the communications with the remote.
	state: ProtocolState<TSubstream>,

	/// Handling all request-responses.
	requests_responses: OneShotHandler<TSubstream, FooProto, FooProto, FooOut>,

	/// Identifier of the node we're talking to. Used only for logging purposes and shouldn't have
	/// any influence on the behaviour.
	remote_peer_id: PeerId,

	/// Queue of events to send to the outside.
	///
	/// This queue must only ever be modified to insert elements at the back, or remove the first
	/// element.
	events_queue: SmallVec<[ProtocolsHandlerEvent<RegisteredProtocol, (), CustomProtoHandlerOut>; 16]>,
}

/// Event that can be received by a `CustomProtoHandler`.
#[derive(Debug)]
pub enum CustomProtoHandlerIn {
	/// Open a substream.
	OpenSubstream {

	},

	/// Open a substream and send a request on it. Wait for an answer.
	SendRequest {
		/// Identifier for the request. Decided by the user.
		unique_id: u64,
		/// Name of the protocol for the substream where the request is sent.
		proto_name: Cow<'static, str>,
		/// Message to send on the substream.
		message: Vec<u8>,
		/// Time after which we stop waiting for an answer.
		timeout: Duration,
	},
}

/// Event that can be emitted by a `CustomProtoHandler`.
#[derive(Debug)]
pub enum CustomProtoHandlerOut {
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
where TSubstream: AsyncRead + AsyncWrite {
	type InEvent = CustomProtoHandlerIn;
	type OutEvent = CustomProtoHandlerOut;
	type Substream = TSubstream;
	type Error = ConnectionKillError;
	type InboundProtocol = RegisteredProtocol;
	type OutboundProtocol = RegisteredProtocol;
	type OutboundOpenInfo = ();

	fn listen_protocol(&self) -> SubstreamProtocol<Self::InboundProtocol> {
		SubstreamProtocol::new(self.protocol.clone())
	}

	fn inject_fully_negotiated_inbound(
		&mut self,
		proto: <Self::InboundProtocol as InboundUpgrade<TSubstream>>::Output
	) {
		self.inject_fully_negotiated(proto);
	}

	fn inject_fully_negotiated_outbound(
		&mut self,
		proto: <Self::OutboundProtocol as OutboundUpgrade<TSubstream>>::Output,
		_: Self::OutboundOpenInfo
	) {
		self.inject_fully_negotiated(proto);
	}

	fn inject_event(&mut self, message: CustomProtoHandlerIn) {
		match message {
			CustomProtoHandlerIn::Disable => self.disable(),
			CustomProtoHandlerIn::Enable => self.enable(),
			CustomProtoHandlerIn::SendCustomMessage { message } =>
				self.send_message(message),
		}
	}

	#[inline]
	fn inject_dial_upgrade_error(&mut self, _: (), err: ProtocolsHandlerUpgrErr<io::Error>) {
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
		match self.state {
			ProtocolState::Init { .. } | ProtocolState::Opening { .. } |
			ProtocolState::Normal { .. } => KeepAlive::Yes,
			ProtocolState::Disabled { .. } | ProtocolState::Poisoned |
	  		ProtocolState::KillAsap => KeepAlive::No,
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

		// Kill the connection if needed.
		if let ProtocolState::KillAsap = self.state {
			return Err(ConnectionKillError);
		}

		// Process all the substreams.
		if let Some(event) = self.poll_state() {
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

/// Given a list of substreams, tries to shut them down. The substreams that have been successfully
/// shut down are removed from the list.
fn shutdown_list<TSubstream>
	(list: &mut SmallVec<impl smallvec::Array<Item = RegisteredProtocolSubstream<TSubstream>>>)
where TSubstream: AsyncRead + AsyncWrite {
	'outer: for n in (0..list.len()).rev() {
		let mut substream = list.swap_remove(n);
		loop {
			match substream.poll() {
				Ok(Async::Ready(Some(_))) => {}
				Ok(Async::NotReady) => break,
				Err(_) | Ok(Async::Ready(None)) => continue 'outer,
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
