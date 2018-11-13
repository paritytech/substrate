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
use libp2p::core::{either, upgrade, transport::boxed::Boxed, muxing::StreamMuxerBox};
use libp2p::transport_timeout::TransportTimeout;
use std::time::Duration;
use std::usize;

/// Builds the transport that serves as a common ground for all connections.
pub fn build_transport(
	local_private_key: secio::SecioKeyPair
) -> Boxed<(PeerId, StreamMuxerBox)> {
	let mut mplex_config = mplex::MplexConfig::new();
	mplex_config.max_buffer_len_behaviour(mplex::MaxBufferBehaviour::Block);
	mplex_config.max_buffer_len(usize::MAX);

	let base = libp2p::CommonTransport::new()
		.with_upgrade(secio::SecioConfig::new(local_private_key))
		.and_then(move |out, endpoint| {
			let upgrade = upgrade::or(
				upgrade::map(yamux::Config::default(), either::EitherOutput::First),
				upgrade::map(mplex_config, either::EitherOutput::Second),
			);
			let peer_id = out.remote_key.into_peer_id();
			let upgrade = upgrade::map(upgrade, move |muxer| (peer_id, muxer));
			upgrade::apply(out.stream, upgrade, endpoint.into())
		})
		.map(|(id, muxer), _| (id, StreamMuxerBox::new(muxer)));

	TransportTimeout::new(base, Duration::from_secs(20))
		.boxed()
}
