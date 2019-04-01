// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

use network::{self, ProtocolStatus, PeerId, PeerInfo as NetworkPeerInfo};
use network::config::Roles;
use test_client::runtime::Block;
use assert_matches::assert_matches;
use futures::sync::mpsc;

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

impl network::SyncProvider<Block> for Status {
	fn status(&self) -> mpsc::UnboundedReceiver<ProtocolStatus<Block>> {
		let (_sink, stream) = mpsc::unbounded();
		stream
	}

	fn network_state(&self) -> network::NetworkState {
		network::NetworkState {
			peer_id: String::new(),
			listened_addresses: Default::default(),
			external_addresses: Default::default(),
			connected_peers: Default::default(),
			not_connected_peers: Default::default(),
			average_download_per_sec: 0,
			average_upload_per_sec: 0,
			peerset: serde_json::Value::Null,
		}
	}

	fn peers(&self) -> Vec<(PeerId, NetworkPeerInfo<Block>)> {
		let mut peers = vec![];
		for _peer in 0..self.peers {
			peers.push(
				(self.peer_id.clone(), NetworkPeerInfo {
					roles: Roles::FULL,
					protocol_version: 1,
					best_hash: Default::default(),
					best_number: 1
				})
			);
		}
		peers
	}

	fn is_major_syncing(&self) -> bool {
		self.is_syncing
	}
}


fn api<T: Into<Option<Status>>>(sync: T) -> System<Block> {
	let status = sync.into().unwrap_or_default();
	let should_have_peers = !status.is_dev;
	System::new(SystemInfo {
		impl_name: "testclient".into(),
		impl_version: "0.2.0".into(),
		chain_name: "testchain".into(),
		properties: Default::default(),
	}, Arc::new(status), should_have_peers)
}

#[test]
fn system_name_works() {
	assert_eq!(
		api(None).system_name().unwrap(),
		"testclient".to_owned()
	);
}

#[test]
fn system_version_works() {
	assert_eq!(
		api(None).system_version().unwrap(),
		"0.2.0".to_owned()
	);
}

#[test]
fn system_chain_works() {
	assert_eq!(
		api(None).system_chain().unwrap(),
		"testchain".to_owned()
	);
}

#[test]
fn system_properties_works() {
	assert_eq!(
		api(None).system_properties().unwrap(),
		serde_json::map::Map::new()
	);
}

#[test]
fn system_health() {
	assert_matches!(
		api(None).system_health().unwrap(),
		Health {
			peers: 0,
			is_syncing: false,
			should_have_peers: true,
		}
	);

	assert_matches!(
		api(Status {
			peer_id: PeerId::random(),
			peers: 5,
			is_syncing: true,
			is_dev: true,
		}).system_health().unwrap(),
		Health {
			peers: 5,
			is_syncing: true,
			should_have_peers: false,
		}
	);

	assert_eq!(
		api(Status {
			peer_id: PeerId::random(),
			peers: 5,
			is_syncing: false,
			is_dev: false,
		}).system_health().unwrap(),
		Health {
			peers: 5,
			is_syncing: false,
			should_have_peers: true,
		}
	);

	assert_eq!(
		api(Status {
			peer_id: PeerId::random(),
			peers: 0,
			is_syncing: false,
			is_dev: true,
		}).system_health().unwrap(),
		Health {
			peers: 0,
			is_syncing: false,
			should_have_peers: false,
		}
	);
}

#[test]
fn system_peers() {
	let peer_id = PeerId::random();
	assert_eq!(
		api(Status {
			peer_id: peer_id.clone(),
			peers: 1,
			is_syncing: false,
			is_dev: true,
		}).system_peers().unwrap(),
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
	assert_eq!(
		api(None).system_network_state().unwrap(),
		network::NetworkState {
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
