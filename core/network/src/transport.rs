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
	mplex, identity, secio, yamux, bandwidth, wasm_ext
};
#[cfg(not(target_os = "unknown"))]
use libp2p::{tcp, dns, websocket, noise};
#[cfg(not(target_os = "unknown"))]
use libp2p::core::{upgrade, either::EitherError, either::EitherOutput};
use libp2p::core::{self, transport::boxed::Boxed, transport::OptionalTransport, muxing::StreamMuxerBox};
use std::{io, sync::Arc, time::Duration, usize};

pub use self::bandwidth::BandwidthSinks;

/// Builds the transport that serves as a common ground for all connections.
///
/// Returns a `BandwidthSinks` object that allows querying the average bandwidth produced by all
/// the connections spawned with this transport.
pub fn build_transport(
	keypair: identity::Keypair,
	wasm_external_transport: Option<wasm_ext::ExtTransport>
) -> (Boxed<(PeerId, StreamMuxerBox), io::Error>, Arc<bandwidth::BandwidthSinks>) {
	// Build configuration objects for encryption mechanisms.
	#[cfg(not(target_os = "unknown"))]
	let noise_config = {
		let noise_keypair = noise::Keypair::new().into_authentic(&keypair)
			// For more information about this panic, see in "On the Importance of Checking
			// Cryptographic Protocols for Faults" by Dan Boneh, Richard A. DeMillo,
			// and Richard J. Lipton.
			.expect("can only fail in case of a hardware bug; since this signing is performed only \
				once and at initialization, we're taking the bet that the inconvenience of a very \
				rare panic here is basically zero");
		noise::NoiseConfig::ix(noise_keypair)
	};
	let secio_config = secio::SecioConfig::new(keypair);

	// Build configuration objects for multiplexing mechanisms.
	let mut mplex_config = mplex::MplexConfig::new();
	mplex_config.max_buffer_len_behaviour(mplex::MaxBufferBehaviour::Block);
	mplex_config.max_buffer_len(usize::MAX);
	let yamux_config = yamux::Config::default();

	// Build the base layer of the transport.
	let transport = if let Some(t) = wasm_external_transport {
		OptionalTransport::some(t)
	} else {
		OptionalTransport::none()
	};
	#[cfg(not(target_os = "unknown"))]
	let transport = {
		let desktop_trans = tcp::TcpConfig::new();
		let desktop_trans = websocket::WsConfig::new(desktop_trans.clone())
			.or_transport(desktop_trans);
		transport.or_transport(dns::DnsConfig::new(desktop_trans))
	};
	let (transport, sinks) = bandwidth::BandwidthLogging::new(transport, Duration::from_secs(5));

	// Encryption

	// For non-WASM, we support both secio and noise.
	#[cfg(not(target_os = "unknown"))]
	let transport = transport.and_then(move |stream, endpoint| {
		let upgrade = core::upgrade::SelectUpgrade::new(noise_config, secio_config);
		core::upgrade::apply(stream, upgrade, endpoint)
			.and_then(|out| match out {
				// We negotiated noise
				EitherOutput::First((remote_id, out)) => {
					let remote_key = match remote_id {
						noise::RemoteIdentity::IdentityKey(key) => key,
						_ => return Err(upgrade::UpgradeError::Apply(EitherError::A(noise::NoiseError::InvalidKey)))
					};
					Ok((EitherOutput::First(out), remote_key.into_peer_id()))
				}
				// We negotiated secio
				EitherOutput::Second(out) =>
					Ok((EitherOutput::Second(out.stream), out.remote_key.into_peer_id()))
			})
	});

	// For WASM, we only support secio for now.
	#[cfg(target_os = "unknown")]
	let transport = transport.and_then(move |stream, endpoint| {
		core::upgrade::apply(stream, secio_config, endpoint)
			.and_then(|out| Ok((out.stream, out.remote_key.into_peer_id())))
	});

	// Multiplexing
	let transport = transport.and_then(move |(stream, peer_id), endpoint| {
			let peer_id2 = peer_id.clone();
			let upgrade = core::upgrade::SelectUpgrade::new(yamux_config, mplex_config)
				.map_inbound(move |muxer| (peer_id, muxer))
				.map_outbound(move |muxer| (peer_id2, muxer));

			core::upgrade::apply(stream, upgrade, endpoint)
				.map(|(id, muxer)| (id, core::muxing::StreamMuxerBox::new(muxer)))
		})

		.with_timeout(Duration::from_secs(20))
		.map_err(|err| io::Error::new(io::ErrorKind::Other, err))
		.boxed();

	(transport, sinks)
}
