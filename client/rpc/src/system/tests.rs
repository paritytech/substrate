// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

use super::*;

use sc_network::{self, PeerId};
use sc_network::config::Role;
use substrate_test_runtime_client::runtime::Block;
use assert_matches::assert_matches;
use futures::prelude::*;
use sp_utils::mpsc::tracing_unbounded;
use std::{
	process::{Stdio, Command}, env, io::{BufReader, BufRead, Write},
	sync::{Arc, Mutex}, thread, time::Duration
};

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
	let (tx, rx) = tracing_unbounded("rpc_system_tests");
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
				Request::SyncState(sender) => {
					let _ = sender.send(SyncState {
						starting_block: 1,
						current_block: 2,
						highest_block: Some(3),
					});
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
fn system_sync_state() {
	assert_eq!(
		wait_receiver(api(None).system_sync_state()),
		SyncState {
			starting_block: 1,
			current_block: 2,
			highest_block: Some(3),
		}
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

#[test]
fn test_add_reset_log_filter() {
	const EXPECTED_BEFORE_ADD: &'static str = "EXPECTED_BEFORE_ADD";
	const EXPECTED_AFTER_ADD: &'static str = "EXPECTED_AFTER_ADD";

	// Enter log generation / filter reload
	if std::env::var("TEST_LOG_FILTER").is_ok() {
		sc_tracing::logging::LoggerBuilder::new("test_before_add=debug").init().unwrap();
		for line in std::io::stdin().lock().lines() {
			let line = line.expect("Failed to read bytes");
			if line.contains("add_reload") {
				api(None).system_add_log_filter("test_after_add".into()).expect("`system_add_log_filter` failed");
			} else if line.contains("reset") {
				api(None).system_reset_log_filter().expect("`system_reset_log_filter` failed");
			} else if line.contains("exit") {
				return;
			}
			log::debug!(target: "test_before_add", "{}", EXPECTED_BEFORE_ADD);
			log::debug!(target: "test_after_add", "{}", EXPECTED_AFTER_ADD);
		}
	}

	// Call this test again to enter the log generation / filter reload block
	let test_executable = env::current_exe().expect("Unable to get current executable!");
	let mut child_process = Command::new(test_executable)
		.env("TEST_LOG_FILTER", "1")
		.args(&["--nocapture", "test_add_reset_log_filter"])
		.stdin(Stdio::piped())
		.stderr(Stdio::piped())
		.spawn()
		.unwrap();

	let child_stderr = child_process.stderr.take().expect("Could not get child stderr");
	let mut child_out = BufReader::new(child_stderr);
	let mut child_in = child_process.stdin.take().expect("Could not get child stdin");

	let child_out_str = Arc::new(Mutex::new(String::new()));
	let shared = child_out_str.clone();

	let _handle = thread::spawn(move || {
		let mut line = String::new();
		while let Ok(_) = child_out.read_line(&mut line) {
			shared.lock().unwrap().push_str(&line);
			line.clear();
		}
	});

	// Initiate logs loop in child process
	child_in.write(b"\n").unwrap();
	thread::sleep(Duration::from_millis(100));
	let test1_str = child_out_str.lock().unwrap().clone();
	// Assert that only the first target is present
	assert!(test1_str.contains(EXPECTED_BEFORE_ADD));
	assert!(!test1_str.contains(EXPECTED_AFTER_ADD));
	child_out_str.lock().unwrap().clear();

	// Initiate add directive & reload in child process
	child_in.write(b"add_reload\n").unwrap();
	thread::sleep(Duration::from_millis(100));
	let test2_str = child_out_str.lock().unwrap().clone();
	// Assert that both targets are now present
	assert!(test2_str.contains(EXPECTED_BEFORE_ADD));
	assert!(test2_str.contains(EXPECTED_AFTER_ADD));
	child_out_str.lock().unwrap().clear();

	// Initiate logs filter reset in child process
	child_in.write(b"reset\n").unwrap();
	thread::sleep(Duration::from_millis(100));
	let test3_str = child_out_str.lock().unwrap().clone();
	// Assert that only the first target is present as it was initially
	assert!(test3_str.contains(EXPECTED_BEFORE_ADD));
	assert!(!test3_str.contains(EXPECTED_AFTER_ADD));

	// Return from child process
	child_in.write(b"exit\n").unwrap();
	assert!(child_process.wait().expect("Error waiting for child process").success());
}
