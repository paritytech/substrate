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

use futures::{future, prelude::*, try_ready};
use std::{io, iter};
use substrate_network_libp2p::{ServiceEvent, multiaddr};

/// Builds two services. The second one has the first one as its bootstrap node.
/// This is to be used only for testing, and a panic will happen if something goes wrong.
fn build_two_nodes() -> (substrate_network_libp2p::Service, substrate_network_libp2p::Service) {
	let service1 = {
		let config = substrate_network_libp2p::NetworkConfiguration {
			listen_addresses: vec![multiaddr![Ip4([127, 0, 0, 1]), Tcp(0u16)]],
			..substrate_network_libp2p::NetworkConfiguration ::default()
		};
		let proto = substrate_network_libp2p::RegisteredProtocol::new(*b"tst", &[1]);
		substrate_network_libp2p::start_service(config, iter::once(proto)).unwrap()
	};

	let service2 = {
		let mut bootnode = service1.listeners().next().unwrap().clone();
		bootnode.append(libp2p::multiaddr::Protocol::P2p(service1.peer_id().clone().into()));

		let config = substrate_network_libp2p::NetworkConfiguration {
			listen_addresses: vec![multiaddr![Ip4([127, 0, 0, 1]), Tcp(0u16)]],
			boot_nodes: vec![bootnode.to_string()],
			..substrate_network_libp2p::NetworkConfiguration::default()
		};
		let proto = substrate_network_libp2p::RegisteredProtocol::new(*b"tst", &[1]);
		substrate_network_libp2p::start_service(config, iter::once(proto)).unwrap()
	};

	(service1, service2)
}

#[test]
fn basic_two_nodes_connectivity() {
	let (mut service1, mut service2) = build_two_nodes();

	let fut1 = future::poll_fn(move || -> io::Result<_> {
		match try_ready!(service1.poll()) {
			Some(ServiceEvent::OpenedCustomProtocol { protocol, version, .. }) => {
				assert_eq!(protocol, *b"tst");
				assert_eq!(version, 1);
				Ok(Async::Ready(()))
			},
			_ => panic!(),
		}
	});

	let fut2 = future::poll_fn(move || -> io::Result<_> {
		match try_ready!(service2.poll()) {
			Some(ServiceEvent::OpenedCustomProtocol { protocol, version, .. }) => {
				assert_eq!(protocol, *b"tst");
				assert_eq!(version, 1);
				Ok(Async::Ready(()))
			},
			_ => panic!(),
		}
	});

	let combined = fut1.select(fut2).map_err(|(err, _)| err);
	tokio::runtime::Runtime::new().unwrap().block_on_all(combined).unwrap();
}
