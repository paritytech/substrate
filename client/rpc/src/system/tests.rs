// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use super::{helpers::SyncState, *};
use assert_matches::assert_matches;
use futures::prelude::*;
use jsonrpsee::{
	core::{EmptyServerParams as EmptyParams, Error as RpcError},
	RpcModule,
};
use sc_network::{self, config::Role, PeerId};
use sc_rpc_api::system::helpers::PeerInfo;
use sc_utils::mpsc::tracing_unbounded;
use sp_core::H256;
use std::{
	env,
	io::{BufRead, BufReader, Write},
	process::{Command, Stdio},
	thread,
};
use substrate_test_runtime_client::runtime::Block;

struct Status {
	pub peers: usize,
	pub is_syncing: bool,
	pub is_dev: bool,
	pub peer_id: PeerId,
}

impl Default for Status {
	fn default() -> Status {
		Status { peer_id: PeerId::random(), peers: 0, is_syncing: false, is_dev: false }
	}
}

fn api<T: Into<Option<Status>>>(sync: T) -> RpcModule<System<Block>> {
	let status = sync.into().unwrap_or_default();
	let should_have_peers = !status.is_dev;
	let (tx, rx) = tracing_unbounded("rpc_system_tests", 10_000);
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
					let _ =
						sender.send("QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV".to_string());
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
				},
				Request::NetworkState(sender) => {
					let _ = sender.send(
						serde_json::to_value(&sc_network::network_state::NetworkState {
							peer_id: String::new(),
							listened_addresses: Default::default(),
							external_addresses: Default::default(),
							connected_peers: Default::default(),
							not_connected_peers: Default::default(),
							peerset: serde_json::Value::Null,
						})
						.unwrap(),
					);
				},
				Request::NetworkAddReservedPeer(peer, sender) => {
					let _ = match sc_network::config::parse_str_addr(&peer) {
						Ok(_) => sender.send(Ok(())),
						Err(s) =>
							sender.send(Err(error::Error::MalformattedPeerArg(s.to_string()))),
					};
				},
				Request::NetworkRemoveReservedPeer(peer, sender) => {
					let _ = match peer.parse::<PeerId>() {
						Ok(_) => sender.send(Ok(())),
						Err(s) =>
							sender.send(Err(error::Error::MalformattedPeerArg(s.to_string()))),
					};
				},
				Request::NetworkReservedPeers(sender) => {
					let _ = sender
						.send(vec!["QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV".to_string()]);
				},
				Request::NodeRoles(sender) => {
					let _ = sender.send(vec![NodeRole::Authority]);
				},
				Request::SyncState(sender) => {
					let _ = sender.send(SyncState {
						starting_block: 1,
						current_block: 2,
						highest_block: 3,
					});
				},
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
		sc_rpc_api::DenyUnsafe::No,
	)
	.into_rpc()
}

#[tokio::test]
async fn system_name_works() {
	assert_eq!(
		api(None).call::<_, String>("system_name", EmptyParams::new()).await.unwrap(),
		"testclient".to_string(),
	);
}

#[tokio::test]
async fn system_version_works() {
	assert_eq!(
		api(None).call::<_, String>("system_version", EmptyParams::new()).await.unwrap(),
		"0.2.0".to_string(),
	);
}

#[tokio::test]
async fn system_chain_works() {
	assert_eq!(
		api(None).call::<_, String>("system_chain", EmptyParams::new()).await.unwrap(),
		"testchain".to_string(),
	);
}

#[tokio::test]
async fn system_properties_works() {
	type Map = serde_json::map::Map<String, serde_json::Value>;

	assert_eq!(
		api(None).call::<_, Map>("system_properties", EmptyParams::new()).await.unwrap(),
		Map::new()
	);
}

#[tokio::test]
async fn system_type_works() {
	assert_eq!(
		api(None)
			.call::<_, String>("system_chainType", EmptyParams::new())
			.await
			.unwrap(),
		"Live".to_owned(),
	);
}

#[tokio::test]
async fn system_health() {
	assert_eq!(
		api(None).call::<_, Health>("system_health", EmptyParams::new()).await.unwrap(),
		Health { peers: 0, is_syncing: false, should_have_peers: true },
	);

	assert_eq!(
		api(Status { peer_id: PeerId::random(), peers: 5, is_syncing: true, is_dev: true })
			.call::<_, Health>("system_health", EmptyParams::new())
			.await
			.unwrap(),
		Health { peers: 5, is_syncing: true, should_have_peers: false },
	);

	assert_eq!(
		api(Status { peer_id: PeerId::random(), peers: 5, is_syncing: false, is_dev: false })
			.call::<_, Health>("system_health", EmptyParams::new())
			.await
			.unwrap(),
		Health { peers: 5, is_syncing: false, should_have_peers: true },
	);

	assert_eq!(
		api(Status { peer_id: PeerId::random(), peers: 0, is_syncing: false, is_dev: true })
			.call::<_, Health>("system_health", EmptyParams::new())
			.await
			.unwrap(),
		Health { peers: 0, is_syncing: false, should_have_peers: false },
	);
}

#[tokio::test]
async fn system_local_peer_id_works() {
	assert_eq!(
		api(None)
			.call::<_, String>("system_localPeerId", EmptyParams::new())
			.await
			.unwrap(),
		"QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV".to_owned()
	);
}

#[tokio::test]
async fn system_local_listen_addresses_works() {
	assert_eq!(
		api(None)
			.call::<_, Vec<String>>("system_localListenAddresses", EmptyParams::new())
			.await
			.unwrap(),
		vec![
			"/ip4/198.51.100.19/tcp/30333/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV",
			"/ip4/127.0.0.1/tcp/30334/ws/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV"
		]
	);
}

#[tokio::test]
async fn system_peers() {
	let peer_id = PeerId::random();
	let peer_info: Vec<PeerInfo<H256, u64>> =
		api(Status { peer_id, peers: 1, is_syncing: false, is_dev: true })
			.call("system_peers", EmptyParams::new())
			.await
			.unwrap();

	assert_eq!(
		peer_info,
		vec![PeerInfo {
			peer_id: peer_id.to_base58(),
			roles: "FULL".into(),
			best_hash: Default::default(),
			best_number: 1u64,
		}]
	);
}

#[tokio::test]
async fn system_network_state() {
	use sc_network::network_state::NetworkState;
	let network_state: NetworkState = api(None)
		.call("system_unstable_networkState", EmptyParams::new())
		.await
		.unwrap();
	assert_eq!(
		network_state,
		NetworkState {
			peer_id: String::new(),
			listened_addresses: Default::default(),
			external_addresses: Default::default(),
			connected_peers: Default::default(),
			not_connected_peers: Default::default(),
			peerset: serde_json::Value::Null,
		}
	);
}

#[tokio::test]
async fn system_node_roles() {
	let node_roles: Vec<NodeRole> =
		api(None).call("system_nodeRoles", EmptyParams::new()).await.unwrap();
	assert_eq!(node_roles, vec![NodeRole::Authority]);
}
#[tokio::test]
async fn system_sync_state() {
	let sync_state: SyncState<i32> =
		api(None).call("system_syncState", EmptyParams::new()).await.unwrap();
	assert_eq!(sync_state, SyncState { starting_block: 1, current_block: 2, highest_block: 3 });
}

#[tokio::test]
async fn system_network_add_reserved() {
	let good_peer_id =
		["/ip4/198.51.100.19/tcp/30333/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV"];
	let _good: () = api(None)
		.call("system_addReservedPeer", good_peer_id)
		.await
		.expect("good peer id works");

	let bad_peer_id = ["/ip4/198.51.100.19/tcp/30333"];
	assert_matches!(
		api(None).call::<_, ()>("system_addReservedPeer", bad_peer_id).await,
		Err(RpcError::Call(err)) if err.message().contains("Peer id is missing from the address")
	);
}

#[tokio::test]
async fn system_network_remove_reserved() {
	let _good_peer: () = api(None)
		.call("system_removeReservedPeer", ["QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV"])
		.await
		.expect("call with good peer id works");

	let bad_peer_id =
		["/ip4/198.51.100.19/tcp/30333/p2p/QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV"];

	assert_matches!(
		api(None).call::<_, String>("system_removeReservedPeer", bad_peer_id).await,
		Err(RpcError::Call(err)) if err.message().contains("base-58 decode error: provided string contained invalid character '/' at byte 0")
	);
}
#[tokio::test]
async fn system_network_reserved_peers() {
	let reserved_peers: Vec<String> =
		api(None).call("system_reservedPeers", EmptyParams::new()).await.unwrap();
	assert_eq!(reserved_peers, vec!["QmSk5HQbn6LhUwDiNMseVUjuRYhEtYj4aUZ6WfWoGURpdV".to_string()],);
}

#[test]
fn test_add_reset_log_filter() {
	const EXPECTED_BEFORE_ADD: &'static str = "EXPECTED_BEFORE_ADD";
	const EXPECTED_AFTER_ADD: &'static str = "EXPECTED_AFTER_ADD";
	const EXPECTED_WITH_TRACE: &'static str = "EXPECTED_WITH_TRACE";

	// Enter log generation / filter reload
	if std::env::var("TEST_LOG_FILTER").is_ok() {
		let mut builder = sc_tracing::logging::LoggerBuilder::new("test_before_add=debug");
		builder.with_log_reloading(true);
		builder.init().unwrap();

		for line in std::io::stdin().lock().lines() {
			let line = line.expect("Failed to read bytes");
			if line.contains("add_reload") {
				let filter = "test_after_add";
				let fut =
					async move { api(None).call::<_, ()>("system_addLogFilter", [filter]).await };
				futures::executor::block_on(fut).expect("`system_addLogFilter` failed");
			} else if line.contains("add_trace") {
				let filter = "test_before_add=trace";
				let fut =
					async move { api(None).call::<_, ()>("system_addLogFilter", [filter]).await };
				futures::executor::block_on(fut).expect("`system_addLogFilter (trace)` failed");
			} else if line.contains("reset") {
				let fut = async move {
					api(None).call::<_, ()>("system_resetLogFilter", EmptyParams::new()).await
				};
				futures::executor::block_on(fut).expect("`system_resetLogFilter` failed");
			} else if line.contains("exit") {
				return
			}
			log::trace!(target: "test_before_add", "{}", EXPECTED_WITH_TRACE);
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

	let mut read_line = || {
		let mut line = String::new();
		child_out.read_line(&mut line).expect("Reading a line");
		line
	};

	// Initiate logs loop in child process
	child_in.write_all(b"\n").unwrap();
	assert!(read_line().contains(EXPECTED_BEFORE_ADD));

	// Initiate add directive & reload in child process
	child_in.write_all(b"add_reload\n").unwrap();
	assert!(read_line().contains(EXPECTED_BEFORE_ADD));
	assert!(read_line().contains(EXPECTED_AFTER_ADD));

	// Check that increasing the max log level works
	child_in.write_all(b"add_trace\n").unwrap();
	assert!(read_line().contains(EXPECTED_WITH_TRACE));
	assert!(read_line().contains(EXPECTED_BEFORE_ADD));
	assert!(read_line().contains(EXPECTED_AFTER_ADD));

	// Initiate logs filter reset in child process
	child_in.write_all(b"reset\n").unwrap();
	assert!(read_line().contains(EXPECTED_BEFORE_ADD));

	// Return from child process
	child_in.write_all(b"exit\n").unwrap();
	assert!(child_process.wait().expect("Error waiting for child process").success());

	// Check for EOF
	assert_eq!(child_out.read_line(&mut String::new()).unwrap(), 0);
}
