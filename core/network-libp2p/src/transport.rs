// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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
use libp2p::{
	InboundUpgradeExt, OutboundUpgradeExt, PeerId, Transport,
	mplex, identity, secio, yamux, websocket, bandwidth
};
#[cfg(not(target_os = "unknown"))]
use libp2p::{tcp, dns};
use libp2p::core::{self, transport::boxed::Boxed, muxing::StreamMuxerBox};
use std::{io, sync::Arc, time::Duration, usize};

pub use self::bandwidth::BandwidthSinks;

/// Builds the transport that serves as a common ground for all connections.
///
/// Returns a `BandwidthSinks` object that allows querying the average bandwidth produced by all
/// the connections spawned with this transport.
pub fn build_transport(
	keypair: identity::Keypair
) -> (Boxed<(PeerId, StreamMuxerBox), io::Error>, Arc<bandwidth::BandwidthSinks>) {
	let mut mplex_config = mplex::MplexConfig::new();
	mplex_config.max_buffer_len_behaviour(mplex::MaxBufferBehaviour::Block);
	mplex_config.max_buffer_len(usize::MAX);

	#[cfg(not(target_os = "unknown"))]
	let transport = {
		let transport = tcp::TcpConfig::new();
		let transport = websocket::WsConfig::new(transport.clone()).or_transport(transport);
		dns::DnsConfig::new(transport)
	};
	#[cfg(target_os = "unknown")]
	let transport = websocket::BrowserWsConfig::new();

	let (transport, sinks) = bandwidth::BandwidthLogging::new(transport, Duration::from_secs(5));

	// TODO: rework the transport creation (https://github.com/libp2p/rust-libp2p/issues/783)
	let transport = transport
		.with_upgrade(secio::SecioConfig::new(keypair))
		.and_then(move |out, endpoint| {
			let peer_id = out.remote_key.into_peer_id();
			let peer_id2 = peer_id.clone();
			let upgrade = core::upgrade::SelectUpgrade::new(yamux::Config::default(), mplex_config)
				.map_inbound(move |muxer| (peer_id, muxer))
				.map_outbound(move |muxer| (peer_id2, muxer));

			core::upgrade::apply(out.stream, upgrade, endpoint)
				.map(|(id, muxer)| (id, core::muxing::StreamMuxerBox::new(muxer)))
		})
		.with_timeout(Duration::from_secs(20))
		.map_err(|err| io::Error::new(io::ErrorKind::Other, err))
		.boxed();

	(transport, sinks)
}
