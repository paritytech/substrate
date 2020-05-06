// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

use super::*;

use sc_network::{self, PeerId};
use sc_network::config::Role;
use substrate_test_runtime_client::runtime::Block;
use assert_matches::assert_matches;
use futures::{prelude::*, channel::mpsc};
use std::thread;

struct Status {
	pub peers: usize,
	pub is_syncing: bool,
	pub is_dev: bool,
	pub peer_id: PeerId,
}

impl Default for Status {
	fn default() -> Status {
		Status {
			peer_id: PeerId::random(),
			peers: 0,
			is_syncing: false,
			is_dev: false,
		}
	}
}

fn api<T: Into<Option<Status>>>(sync: T) -> System<Block> {
	let status = sync.into().unwrap_or_default();
	let should_have_peers = !status.is_dev;
	let (tx, rx) = mpsc::unbounded();
	thread::spawn(move || {
		futures::executor::block_on(rx.for_each(move |request| {
			match request {
				Request::Health(sender) => {
					let _ = sender.send(Health {
						peers: status.peers,
						is_syncing: status.is_syncing,
						should_have_peers,
					});
				},
				Request::LocalPeerId(sender) => {
					let _ = sender.send("QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV".to_string());
				},
				Request::LocalListenAddresses(sender) => {
					let _ = sender.send(vec![
						"/ip4/198.51.100.19/tcp/30333/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV".to_string(),
						"/ip4/127.0.0.1/tcp/30334/ws/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV".to_string(),
					]);
				},
				Request::Peers(sender) => {
					let mut peers = vec![];
					for _peer in 0..status.peers {
						peers.push(PeerInfo {
							peer_id: status.peer_id.to_base58(),
							roles: format!("{}", Role::Full),
							protocol_version: 1,
							best_hash: Default::default(),
							best_number: 1,
						});
					}
					let _ = sender.send(peers);
				}
				Request::NetworkState(sender) => {
					let _ = sender.send(serde_json::to_value(&sc_network::network_state::NetworkState {
						peer_id: String::new(),
						listened_addresses: Default::default(),
						external_addresses: Default::default(),
						connected_peers: Default::default(),
						not_connected_peers: Default::default(),
						average_download_per_sec: 0,
						average_upload_per_sec: 0,
						peerset: serde_json::Value::Null,
					}).unwrap());
				},
				Request::NetworkAddReservedPeer(peer, sender) => {
					let _ = match sc_network::config::parse_str_addr(&peer) {
						Ok(_) => sender.send(Ok(())),
						Err(s) => sender.send(Err(error::Error::MalformattedPeerArg(s.to_string()))),
					};
				},
				Request::NetworkRemoveReservedPeer(peer, sender) => {
					let _ = match peer.parse::<PeerId>() {
						Ok(_) => sender.send(Ok(())),
						Err(s) => sender.send(Err(error::Error::MalformattedPeerArg(s.to_string()))),
					};
				}
				Request::NodeRoles(sender) => {
					let _ = sender.send(vec![NodeRole::Authority]);
				}
			};

			future::ready(())
		}))
	});
	System::new(
		SystemInfo {
			impl_name: "testclient".into(),
			impl_version: "0.2.0".into(),
			chain_name: "testchain".into(),
			properties: Default::default(),
			chain_type: Default::default(),
		},
		tx,
		sc_rpc_api::DenyUnsafe::No
	)
}

fn wait_receiver<T>(rx: Receiver<T>) -> T {
	let mut runtime = tokio::runtime::current_thread::Runtime::new().unwrap();
	runtime.block_on(rx).unwrap()
}

#[test]
fn system_name_works() {
	assert_eq!(
		api(None).system_name().unwrap(),
		"testclient".to_owned(),
	);
}

#[test]
fn system_version_works() {
	assert_eq!(
		api(None).system_version().unwrap(),
		"0.2.0".to_owned(),
	);
}

#[test]
fn system_chain_works() {
	assert_eq!(
		api(None).system_chain().unwrap(),
		"testchain".to_owned(),
	);
}

#[test]
fn system_properties_works() {
	assert_eq!(
		api(None).system_properties().unwrap(),
		serde_json::map::Map::new(),
	);
}

#[test]
fn system_type_works() {
	assert_eq!(
		api(None).system_type().unwrap(),
		Default::default(),
	);
}

#[test]
fn system_health() {
	assert_matches!(
		wait_receiver(api(None).system_health()),
		Health {
			peers: 0,
			is_syncing: false,
			should_have_peers: true,
		}
	);

	assert_matches!(
		wait_receiver(api(Status {
			peer_id: PeerId::random(),
			peers: 5,
			is_syncing: true,
			is_dev: true,
		}).system_health()),
		Health {
			peers: 5,
			is_syncing: true,
			should_have_peers: false,
		}
	);

	assert_eq!(
		wait_receiver(api(Status {
			peer_id: PeerId::random(),
			peers: 5,
			is_syncing: false,
			is_dev: false,
		}).system_health()),
		Health {
			peers: 5,
			is_syncing: false,
			should_have_peers: true,
		}
	);

	assert_eq!(
		wait_receiver(api(Status {
			peer_id: PeerId::random(),
			peers: 0,
			is_syncing: false,
			is_dev: true,
		}).system_health()),
		Health {
			peers: 0,
			is_syncing: false,
			should_have_peers: false,
		}
	);
}

#[test]
fn system_local_peer_id_works() {
	assert_eq!(
		wait_receiver(api(None).system_local_peer_id()),
		"QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV".to_owned(),
	);
}

#[test]
fn system_local_listen_addresses_works() {
	assert_eq!(
		wait_receiver(api(None).system_local_listen_addresses()),
		vec![
			"/ip4/198.51.100.19/tcp/30333/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV".to_string(),
			"/ip4/127.0.0.1/tcp/30334/ws/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV".to_string(),
		]
	);
}

#[test]
fn system_peers() {
	let mut runtime = tokio::runtime::current_thread::Runtime::new().unwrap();

	let peer_id = PeerId::random();
	let req = api(Status {
		peer_id: peer_id.clone(),
		peers: 1,
		is_syncing: false,
		is_dev: true,
	}).system_peers();
	let res = runtime.block_on(req).unwrap();

	assert_eq!(
		res,
		vec![PeerInfo {
			peer_id: peer_id.to_base58(),
			roles: "FULL".into(),
			protocol_version: 1,
			best_hash: Default::default(),
			best_number: 1u64,
		}]
	);
}

#[test]
fn system_network_state() {
	let mut runtime = tokio::runtime::current_thread::Runtime::new().unwrap();
	let req = api(None).system_network_state();
	let res = runtime.block_on(req).unwrap();

	assert_eq!(
		serde_json::from_value::<sc_network::network_state::NetworkState>(res).unwrap(),
		sc_network::network_state::NetworkState {
			peer_id: String::new(),
			listened_addresses: Default::default(),
			external_addresses: Default::default(),
			connected_peers: Default::default(),
			not_connected_peers: Default::default(),
			average_download_per_sec: 0,
			average_upload_per_sec: 0,
			peerset: serde_json::Value::Null,
		}
	);
}

#[test]
fn system_node_roles() {
	assert_eq!(
		wait_receiver(api(None).system_node_roles()),
		vec![NodeRole::Authority]
	);
}

#[test]
fn system_network_add_reserved() {
	let good_peer_id = "/ip4/198.51.100.19/tcp/30333/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV";
	let bad_peer_id = "/ip4/198.51.100.19/tcp/30333";
	let mut runtime = tokio::runtime::current_thread::Runtime::new().unwrap();

	let good_fut = api(None).system_add_reserved_peer(good_peer_id.into());
	let bad_fut = api(None).system_add_reserved_peer(bad_peer_id.into());
	assert_eq!(runtime.block_on(good_fut), Ok(()));
	assert!(runtime.block_on(bad_fut).is_err());
}

#[test]
fn system_network_remove_reserved() {
	let good_peer_id = "QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV";
	let bad_peer_id = "/ip4/198.51.100.19/tcp/30333/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV";
	let mut runtime = tokio::runtime::current_thread::Runtime::new().unwrap();

	let good_fut = api(None).system_remove_reserved_peer(good_peer_id.into());
	let bad_fut = api(None).system_remove_reserved_peer(bad_peer_id.into());
	assert_eq!(runtime.block_on(good_fut), Ok(()));
	assert!(runtime.block_on(bad_fut).is_err());
}
