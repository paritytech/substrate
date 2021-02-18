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

use crate::{new_worker_and_service, worker::{tests::{TestApi, TestNetwork}, Role}};

use std::sync::Arc;
use futures::{channel::mpsc::channel, executor::LocalPool, task::LocalSpawn};
use libp2p::core::{multiaddr::{Multiaddr, Protocol}, PeerId};

use sp_authority_discovery::AuthorityId;
use sp_core::crypto::key_types;
use sp_keystore::{CryptoStore, testing::KeyStore};

#[test]
fn get_addresses_and_authority_id() {
	let (_dht_event_tx, dht_event_rx) = channel(0);
	let network: Arc<TestNetwork> = Arc::new(Default::default());

	let mut pool = LocalPool::new();

	let key_store = KeyStore::new();

	let remote_authority_id: AuthorityId = pool.run_until(async {
		key_store
			.sr25519_generate_new(key_types::AUTHORITY_DISCOVERY, None)
			.await
			.unwrap()
			.into()
	});

	let remote_peer_id = PeerId::random();
	let remote_addr = "/ip6/2001:db8:0:0:0:0:0:2/tcp/30333".parse::<Multiaddr>()
		.unwrap()
		.with(Protocol::P2p(remote_peer_id.clone().into()));

	let test_api = Arc::new(TestApi {
		authorities: vec![],
	});

	let (mut worker, mut service) = new_worker_and_service(
		test_api,
		network.clone(),
		Box::pin(dht_event_rx),
		Role::PublishAndDiscover(key_store.into()),
		None,
	);
	worker.inject_addresses(remote_authority_id.clone(), vec![remote_addr.clone()]);

	pool.spawner().spawn_local_obj(Box::pin(worker.run()).into()).unwrap();

	pool.run_until(async {
		assert_eq!(
			Some(vec![remote_addr]),
			service.get_addresses_by_authority_id(remote_authority_id.clone()).await,
		);
		assert_eq!(
			Some(remote_authority_id),
			service.get_authority_id_by_peer_id(remote_peer_id).await,
		);
	});
}
