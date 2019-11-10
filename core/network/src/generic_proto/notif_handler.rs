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
	notif_in_handler::{NotifsInHandlerProto, NotifsInHandler},
	notif_out_handler::{NotifsOutHandlerProto, NotifsOutHandler},
	upgrade::{NotificationsIn, NotificationsOut, UpgradeCollec},
};
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
use std::borrow::Cow;
use tokio_io::{AsyncRead, AsyncWrite};

/// Implements the `IntoProtocolsHandler` trait of libp2p.
///
/// Every time a connection with a remote starts, an instance of this struct is created and
/// sent to a background task dedicated to this connection. Once the connection is established,
/// it is turned into a [`NotifsHandler`].
pub struct NotifsHandlerProto<TSubstream> {
	in_handlers: Vec<NotifsInHandlerProto<TSubstream>>,
	out_handlers: Vec<NotifsOutHandlerProto<TSubstream>>,
}

impl<TSubstream> NotifsHandlerProto<TSubstream>
where
	TSubstream: AsyncRead + AsyncWrite,
{
	/// Builds a new `NotifsHandlerProto`.
	pub fn new() -> Self {
		NotifsHandlerProto {
			in_handlers: Vec::new(),
			out_handlers: Vec::new(),
		}
	}
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
		}
	}
}

/// The actual handler once the connection has been established.
pub struct NotifsHandler<TSubstream> {
	/// Handlers for ingoing substreams.
	in_handlers: Vec<NotifsInHandler<TSubstream>>,

	/// Handlers for outgoing substreams.
	out_handlers: Vec<NotifsOutHandler<TSubstream>>,
}

/// Event that can be received by a `NotifsHandler`.
#[derive(Debug)]
pub enum NotifsHandlerIn {
	/// Whenever a remote opens a notifications substream, we send to it a "node information"
	/// handshake message. This message is cached in the `ProtocolsHandler`, and `UpdateNodeInfos`
	/// updates this cached message.
	UpdateNodeInfos {
		/// Notifications protocol for which we want to modify the information.
		proto_name: Cow<'static, [u8]>,
		/// Information sent to the remote.
		infos: Vec<u8>,
	},

	/// Enables the notifications substream for this node for this protocol. The handler will try
	/// to maintain a substream with the remote.
	Enable {
		/// Protocol for which we should open a substream.
		proto_name: Cow<'static, [u8]>,
	},

	/// Disables the notifications substream for this node for this protocol.
	Disable {
		/// Protocol for which we close the substream.
		proto_name: Cow<'static, [u8]>,
	},

	/// Sends a message on the notifications substream. Ignored if the substream isn't open.
	///
	/// It is only valid to send this if the handler has been enabled.
	// TODO: is ignoring the correct way to do this?
	Send {
		/// Protocol for which we opened a substream.
		proto_name: Cow<'static, [u8]>,
		/// Message to send.
		message: Vec<u8>,
	},
}

/// Event that can be emitted by a `NotifsHandler`.
#[derive(Debug)]
pub enum NotifsHandlerOut {
	/// The notifications substream has been open by the remote.
	RemoteOpen {
		/// Protocol for which we opened a substream.
		proto_name: Cow<'static, [u8]>,
	},

	/// The notifications substream has been closed by the remote.
	RemoteClosed {
		/// Protocol for the substream was closed.
		proto_name: Cow<'static, [u8]>,
	},

	/// Received a message on the notifications substream.
	///
	/// Can only happen after a `NotifOpen` and before a `NotifClosed` for the corresponding
	/// protocol.
	InNotif {
		/// Protocol for which we received a message.
		proto_name: Cow<'static, [u8]>,
		/// The message.
		message: Vec<u8>,
	},

	/// Our notifications substream has been accepted by the remote.
	LocalOpen {
		/// Protocol for which we opened a substream.
		proto_name: Cow<'static, [u8]>,
		/// Handshake message sent by the remote after we opened the substream.
		handshake: Vec<u8>,
	},

	/// Our notifications substream has been closed by the remote.
	LocalClosed {
		/// Protocol for the substream was closed.
		proto_name: Cow<'static, [u8]>,
	},

	/// We tried to open a notifications substream, but the remote refused it.
	///
	/// The handler is still enabled and will try again in a few seconds.
	Refused {
		/// Protocol for the substream was refused.
		proto_name: Cow<'static, [u8]>,
	},
}

impl<TSubstream> NotifsHandlerProto<TSubstream> {
	pub fn new(list: impl Into<Vec<(Cow<'static, [u8]>, Vec<u8>)>>) -> Self {
		let list = list.into();

		NotifsHandlerProto {
			in_handlers: list.clone().into_iter().map(|(p, msg)| NotifsInHandlerProto::new(p, msg)),
			out_handlers: list.clone().into_iter().map(|(p, _)| NotifsOutHandlerProto::new(p)),
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
