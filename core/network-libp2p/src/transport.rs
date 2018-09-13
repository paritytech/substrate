// Copyright 2018 Parity Technologies (UK) Ltd.
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

use libp2p::{self, PeerId, Transport, mplex, secio, yamux};
use libp2p::core::{either, upgrade, transport::BoxedMuxed};
use libp2p::transport_timeout::TransportTimeout;
use std::time::Duration;
use std::usize;
use tokio_io::{AsyncRead, AsyncWrite};

/// Builds the transport that serves as a common ground for all connections.
pub fn build_transport(
	local_private_key: secio::SecioKeyPair
) -> BoxedMuxed<(PeerId, impl AsyncRead + AsyncWrite)> {
	let mut mplex_config = mplex::MplexConfig::new();
	mplex_config.max_buffer_len_behaviour(mplex::MaxBufferBehaviour::Block);
	mplex_config.max_buffer_len(usize::MAX);

	let base = libp2p::CommonTransport::new()
		.with_upgrade(secio::SecioConfig::new(local_private_key))
		.and_then(move |out, endpoint, client_addr| {
			let upgrade = upgrade::or(
				upgrade::map(mplex_config, either::EitherOutput::First),
				upgrade::map(yamux::Config::default(), either::EitherOutput::Second),
			);
			let key = out.remote_key;
			let upgrade = upgrade::map(upgrade, move |muxer| (key, muxer));
			upgrade::apply(out.stream, upgrade, endpoint, client_addr)
		})
		.into_connection_reuse()
		.map(|(key, substream), _| (key.into_peer_id(), substream));

	TransportTimeout::new(base, Duration::from_secs(20))
		.boxed_muxed()
}
