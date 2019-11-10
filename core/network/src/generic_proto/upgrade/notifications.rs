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

/// Notifications protocol.
///
/// The Substrate notifications protocol consists in the following:
///
/// - Node A opens a substream to node B.
/// - If node B accepts the substream, it sends back a message which contains some
///   protocol-specific higher-level logic. This message is prefixed with a variable-length
///   integer message length. This message can be empty, in which case `0` is sent. Afterwards,
///   the sending side of B is closed.
/// - If instead the node refuses the connection (which typically happens because no empty slot
///   is available), then it immediately closes the substream after the multistream-select
///   negotiation.
/// - Node A can then send notifications to B, prefixed with a variable-length integer indicating
///   the length of the message.
/// - Node A closes its writing side if it doesn't want the notifications substream anymore.
///
/// Notification substreams are unidirectional. If A opens a substream with B, then B is
/// encouraged but not required to open a substream to A as well.
///

use libp2p::core::{Negotiated, UpgradeInfo, InboundUpgrade, OutboundUpgrade, upgrade, upgrade::ProtocolName};
use std::{borrow::Cow, iter};
use futures::prelude::*;
use tokio_io::{AsyncRead, AsyncWrite};

/// Upgrade that accepts a substream, sends back a status message, then becomes a unidirectional
/// stream of messages.
#[derive(Debug, Clone)]
pub struct NotificationsIn {
	/// Protocol name to use when negotiating the substream.
	protocol_name: Cow<'static, [u8]>,
	/// Handshake message to send to the remote when they open a substream.
	handshake_message: Vec<u8>,
}

/// Upgrade that opens a substream, waits for the remote to accept by sending back a status
/// message, then becomes a unidirectional sink of data.
#[derive(Debug, Clone)]
pub struct NotificationsOut {
	/// Protocol name to use when negotiating the substream.
	protocol_name: Cow<'static, [u8]>,
}

impl NotificationsIn {
	/// Builds a new potential upgrade.
	// TODO: don't send back the handshake message; instead the user should be able to choose
	// whether to accept or refuse the substream
	pub fn new(proto_name: impl Into<Cow<'static, [u8]>>, handshake_msg: impl Into<Vec<u8>>) -> Self {
		NotificationsIn {
			protocol_name: proto_name.into(),
			handshake_message: handshake_msg.into(),
		}
	}

	/// Modifies the handshake message.
	// TODO: remove
	pub fn set_handshake_message(&mut self, message: impl Into<Vec<u8>>) {
		self.handshake_message = message.into();
	}
}

impl NotificationsOut {
	/// Builds a new potential upgrade.
	pub fn new(proto_name: impl Into<Cow<'static, [u8]>>) -> Self {
		NotificationsOut {
			protocol_name: proto_name.into(),
		}
	}
}

impl UpgradeInfo for NotificationsIn {
	type Info = Cow<'static, [u8]>;
	type InfoIter = iter::Once<Self::Info>;

	fn protocol_info(&self) -> Self::InfoIter {
		iter::once(self.protocol_name.clone())
	}
}

impl UpgradeInfo for NotificationsOut {
	type Info = Cow<'static, [u8]>;
	type InfoIter = iter::Once<Self::Info>;

	fn protocol_info(&self) -> Self::InfoIter {
		iter::once(self.protocol_name.clone())
	}
}

impl<TSubstream> InboundUpgrade<TSubstream> for NotificationsIn
where TSubstream: AsyncRead + AsyncWrite + 'static,
{
	type Output = Vec<u8>;
	type Future = Box<dyn Future<Item = Self::Output, Error = Self::Error> + Send>;
	type Error = upgrade::ReadOneError;

	fn upgrade_inbound(
		self,
		socket: Negotiated<TSubstream>,
		proto_name: Self::Info,
	) -> Self::Future {
		unimplemented!()
	}
}

impl<TSubstream> OutboundUpgrade<TSubstream> for NotificationsOut
where TSubstream: AsyncRead + AsyncWrite + 'static,
{
	type Output = Vec<u8>;
	type Future = Box<dyn Future<Item = Self::Output, Error = Self::Error> + Send>;
	type Error = upgrade::ReadOneError;

	fn upgrade_outbound(
		self,
		socket: Negotiated<TSubstream>,
		proto_name: Self::Info,
	) -> Self::Future {
		unimplemented!()
	}
}
