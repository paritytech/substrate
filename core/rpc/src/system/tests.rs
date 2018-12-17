// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

use network::{self, SyncState, SyncStatus, ProtocolStatus};
use test_client::runtime::Block;

#[derive(Default)]
struct Status {
	pub peers: usize,
	pub is_syncing: bool,
	pub is_dev: bool,
}

impl network::SyncProvider<Block> for Status {
	fn status(&self) -> ProtocolStatus<Block> {
		ProtocolStatus {
			sync: SyncStatus {
				state: if self.is_syncing { SyncState::Downloading } else { SyncState::Idle },
				best_seen_block: None,
			},
			num_peers: self.peers,
			num_active_peers: 0,
		}
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
		api(None).system_health().unwrap_err().kind(),
		error::ErrorKind::NotHealthy(Health {
			peers: 0,
			is_syncing: false,
		})
	);

	assert_matches!(
		api(Status {
			peers: 5,
			is_syncing: true,
			is_dev: true,
		}).system_health().unwrap_err().kind(),
		error::ErrorKind::NotHealthy(Health {
			peers: 5,
			is_syncing: true,
		})
	);

	assert_eq!(
		api(Status {
			peers: 5,
			is_syncing: false,
			is_dev: false,
		}).system_health().unwrap(),
		Health {
			peers: 5,
			is_syncing: false,
		}
	);

	assert_eq!(
		api(Status {
			peers: 0,
			is_syncing: false,
			is_dev: true,
		}).system_health().unwrap(),
		Health {
			peers: 0,
			is_syncing: false,
		}
	);
}
