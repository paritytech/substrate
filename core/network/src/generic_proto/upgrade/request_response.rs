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

use futures::prelude::*;
use libp2p::core::{Negotiated, UpgradeInfo, OutboundUpgrade, upgrade, upgrade::ProtocolName};
use std::{borrow::Cow, iter};
use tokio_io::{AsyncRead, AsyncWrite};

/// Upgrade that sends a message on the substream, then waits for an answer, then closes.
#[derive(Debug, Clone)]
pub struct RequestResponse {
	/// Protocol name to use when negotiating the substream.
	protocol_name: Cow<'static, [u8]>,
	/// Message of the request.
	message: Vec<u8>,
}

impl RequestResponse {
	/// Builds a new [`RequestResponse`].
	pub fn new(
		protocol_name: impl Into<Cow<'static, [u8]>>,
		message: impl Into<Vec<u8>>
	) -> RequestResponse {
		RequestResponse {
			protocol_name: protocol_name.into(),
			message: message.into(),
		}
	}
}

impl UpgradeInfo for RequestResponse {
	type Info = Cow<'static, [u8]>;
	type InfoIter = iter::Once<Self::Info>;

	fn protocol_info(&self) -> Self::InfoIter {
		iter::once(self.protocol_name.clone())
	}
}

impl<TSubstream> OutboundUpgrade<TSubstream> for RequestResponse
where TSubstream: AsyncRead + AsyncWrite + 'static,
{
	type Output = Vec<u8>;
	type Future = Box<dyn Future<Item = Self::Output, Error = Self::Error>>;
	type Error = upgrade::ReadOneError;

	fn upgrade_outbound(
		self,
		socket: Negotiated<TSubstream>,
		_: Self::Info,
	) -> Self::Future {
		// TODO: decide max size?
		Box::new(upgrade::request_response(socket, self.message, 2048, (), |r, _| Ok(r)))
	}
}
