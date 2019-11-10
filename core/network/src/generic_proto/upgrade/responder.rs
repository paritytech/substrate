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
use libp2p::core::{Negotiated, UpgradeInfo, InboundUpgrade, upgrade};
use std::{borrow::Cow, fmt, vec};
use tokio_io::{AsyncRead, AsyncWrite};

/// Upgrade that accepts incoming substreams, waits for a message, then sends back an answer, then
/// closes.
#[derive(Debug, Clone)]
pub struct Responder {
	/// Protocol that we support. To be used when negotiating the substream.
	protocol_names: Vec<Cow<'static, [u8]>>,
}

impl Default for Responder {
	fn default() -> Self {
		Responder {
			protocol_names: Vec::new(),
		}
	}
}

impl UpgradeInfo for Responder {
	type Info = Cow<'static, [u8]>;
	type InfoIter = vec::IntoIter<Self::Info>;

	fn protocol_info(&self) -> Self::InfoIter {
		self.protocol_names.clone().into_iter()
	}
}

impl<TSubstream> InboundUpgrade<TSubstream> for Responder
where TSubstream: AsyncRead + AsyncWrite + 'static,
{
	type Output = ResponderResponse<TSubstream>;
	type Future = Box<dyn Future<Item = Self::Output, Error = Self::Error> + Send>;
	type Error = upgrade::ReadOneError;

	fn upgrade_inbound(
		self,
		substream: Negotiated<TSubstream>,
		_: Self::Info,
	) -> Self::Future {
		// TODO: decide on max size
		Box::new(upgrade::read_respond(substream, 2048, (), |substream, message, ()| {
			Ok(ResponderResponse {
				substream,
				request_message: message,
			})
		}))
	}
}

/// Request received from a remote. Must be used to send back the answer.
pub struct ResponderResponse<TSubstream> {
	/// Substream after reading the message. Used to send back the response.
	substream: Negotiated<TSubstream>,
	/// Message that the remote sent for the request.
	request_message: Vec<u8>,
}

impl<TSubstream> fmt::Debug for ResponderResponse<TSubstream> {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		f.debug_struct("ResponderResponse")
			.field("request_message", &self.request_message)
			.finish()
	}
}
