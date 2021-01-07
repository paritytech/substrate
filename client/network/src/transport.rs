// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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
	PeerId, Transport,
	core::{
		self, either::EitherTransport, muxing::StreamMuxerBox,
		transport::{Boxed, OptionalTransport}, upgrade
	},
	mplex, identity, bandwidth, wasm_ext, noise
};
#[cfg(not(target_os = "unknown"))]
use libp2p::{tcp, dns, websocket};
use std::{sync::Arc, time::Duration};

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
) -> (Boxed<(PeerId, StreamMuxerBox)>, Arc<BandwidthSinks>) {
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
			EitherTransport::Left(dns)
		} else {
			EitherTransport::Right(desktop_trans.map_err(dns::DnsErr::Underlying))
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
		let noise_keypair = noise::Keypair::<noise::X25519Spec>::new().into_authentic(&keypair)
			.expect("can only fail in case of a hardware bug; since this signing is performed only \
				once and at initialization, we're taking the bet that the inconvenience of a very \
				rare panic here is basically zero");

		// Legacy noise configurations for backward compatibility.
		let mut noise_legacy = noise::LegacyConfig::default();
		noise_legacy.recv_legacy_handshake = true;

		let mut xx_config = noise::NoiseConfig::xx(noise_keypair);
		xx_config.set_legacy_config(noise_legacy.clone());
		xx_config.into_authenticated()
	};

	let multiplexing_config = {
		let mut mplex_config = mplex::MplexConfig::new();
		mplex_config.set_max_buffer_behaviour(mplex::MaxBufferBehaviour::Block);
		mplex_config.set_max_buffer_size(usize::MAX);

		let mut yamux_config = libp2p::yamux::YamuxConfig::default();
		// Enable proper flow-control: window updates are only sent when
		// buffered data has been consumed.
		yamux_config.set_window_update_mode(libp2p::yamux::WindowUpdateMode::on_read());

		core::upgrade::SelectUpgrade::new(yamux_config, mplex_config)
	};

	let transport = transport.upgrade(upgrade::Version::V1Lazy)
		.authenticate(authentication_config)
		.multiplex(multiplexing_config)
		.timeout(Duration::from_secs(20))
		.boxed();

	(transport, bandwidth)
}
