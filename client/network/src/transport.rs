// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use libp2p::{
	InboundUpgradeExt, OutboundUpgradeExt, PeerId, Transport,
	core::{
		self, either::EitherOutput, muxing::StreamMuxerBox,
		transport::{boxed::Boxed, OptionalTransport}, upgrade
	},
	mplex, identity, bandwidth, wasm_ext, noise
};
#[cfg(not(target_os = "unknown"))]
use libp2p::{tcp, dns, websocket};
use std::{io, sync::Arc, time::Duration};

pub use self::bandwidth::BandwidthSinks;

/// Builds the transport that serves as a common ground for all connections.
///
/// If `memory_only` is true, then only communication within the same process are allowed. Only
/// addresses with the format `/memory/...` are allowed.
///
/// Returns a `BandwidthSinks` object that allows querying the average bandwidth produced by all
/// the connections spawned with this transport.
pub fn build_transport(
	keypair: identity::Keypair,
	memory_only: bool,
	wasm_external_transport: Option<wasm_ext::ExtTransport>,
	use_yamux_flow_control: bool
) -> (Boxed<(PeerId, StreamMuxerBox), io::Error>, Arc<BandwidthSinks>) {
	// Build the base layer of the transport.
	let transport = if let Some(t) = wasm_external_transport {
		OptionalTransport::some(t)
	} else {
		OptionalTransport::none()
	};
	#[cfg(not(target_os = "unknown"))]
	let transport = transport.or_transport(if !memory_only {
		let desktop_trans = tcp::TcpConfig::new();
		let desktop_trans = websocket::WsConfig::new(desktop_trans.clone())
			.or_transport(desktop_trans);
		OptionalTransport::some(if let Ok(dns) = dns::DnsConfig::new(desktop_trans.clone()) {
			dns.boxed()
		} else {
			desktop_trans.map_err(dns::DnsErr::Underlying).boxed()
		})
	} else {
		OptionalTransport::none()
	});

	let transport = transport.or_transport(if memory_only {
		OptionalTransport::some(libp2p::core::transport::MemoryTransport::default())
	} else {
		OptionalTransport::none()
	});

	let (transport, bandwidth) = bandwidth::BandwidthLogging::new(transport);

	let authentication_config = {
		// For more information about these two panics, see in "On the Importance of
		// Checking Cryptographic Protocols for Faults" by Dan Boneh, Richard A. DeMillo,
		// and Richard J. Lipton.
		let noise_keypair_legacy = noise::Keypair::<noise::X25519>::new().into_authentic(&keypair)
			.expect("can only fail in case of a hardware bug; since this signing is performed only \
				once and at initialization, we're taking the bet that the inconvenience of a very \
				rare panic here is basically zero");
		let noise_keypair_spec = noise::Keypair::<noise::X25519Spec>::new().into_authentic(&keypair)
			.expect("can only fail in case of a hardware bug; since this signing is performed only \
				once and at initialization, we're taking the bet that the inconvenience of a very \
				rare panic here is basically zero");

		// Legacy noise configurations for backward compatibility.
		let mut noise_legacy = noise::LegacyConfig::default();
		noise_legacy.send_legacy_handshake = true;
		noise_legacy.recv_legacy_handshake = true;

		let mut xx_config = noise::NoiseConfig::xx(noise_keypair_spec);
		xx_config.set_legacy_config(noise_legacy.clone());
		let mut ix_config = noise::NoiseConfig::ix(noise_keypair_legacy);
		ix_config.set_legacy_config(noise_legacy);

		let extract_peer_id = |result| match result {
			EitherOutput::First((peer_id, o)) => (peer_id, EitherOutput::First(o)),
			EitherOutput::Second((peer_id, o)) => (peer_id, EitherOutput::Second(o)),
		};

		core::upgrade::SelectUpgrade::new(xx_config.into_authenticated(), ix_config.into_authenticated())
			.map_inbound(extract_peer_id)
			.map_outbound(extract_peer_id)
	};

	let multiplexing_config = {
		let mut mplex_config = mplex::MplexConfig::new();
		mplex_config.max_buffer_len_behaviour(mplex::MaxBufferBehaviour::Block);
		mplex_config.max_buffer_len(usize::MAX);

		let mut yamux_config = libp2p::yamux::Config::default();

		if use_yamux_flow_control {
			// Enable proper flow-control: window updates are only sent when
			// buffered data has been consumed.
			yamux_config.set_window_update_mode(libp2p::yamux::WindowUpdateMode::OnRead);
		}

		core::upgrade::SelectUpgrade::new(yamux_config, mplex_config)
			.map_inbound(move |muxer| core::muxing::StreamMuxerBox::new(muxer))
			.map_outbound(move |muxer| core::muxing::StreamMuxerBox::new(muxer))
	};

	let transport = transport.upgrade(upgrade::Version::V1)
		.authenticate(authentication_config)
		.multiplex(multiplexing_config)
		.timeout(Duration::from_secs(20))
		.map_err(|err| io::Error::new(io::ErrorKind::Other, err))
		.boxed();

	(transport, bandwidth)
}
