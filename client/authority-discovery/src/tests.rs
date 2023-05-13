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

use crate::{
	new_worker_and_service,
	worker::{
		tests::{TestApi, TestNetwork},
		Role,
	},
};

use futures::{channel::mpsc::channel, executor::LocalPool, task::LocalSpawn};
use libp2p::{
	core::multiaddr::{Multiaddr, Protocol},
	identity::ed25519,
	PeerId,
};
use std::{collections::HashSet, sync::Arc};

use sp_authority_discovery::AuthorityId;
use sp_core::crypto::key_types;
use sp_keystore::{testing::MemoryKeystore, Keystore};

#[test]
fn get_addresses_and_authority_id() {
	let (_dht_event_tx, dht_event_rx) = channel(0);
	let network: Arc<TestNetwork> = Arc::new(Default::default());

	let mut pool = LocalPool::new();

	let key_store = MemoryKeystore::new();

	let remote_authority_id: AuthorityId = pool.run_until(async {
		key_store
			.sr25519_generate_new(key_types::AUTHORITY_DISCOVERY, None)
			.unwrap()
			.into()
	});

	let remote_peer_id = PeerId::random();
	let remote_addr = "/ip6/2001:db8:0:0:0:0:0:2/tcp/30333"
		.parse::<Multiaddr>()
		.unwrap()
		.with(Protocol::P2p(remote_peer_id.into()));

	let test_api = Arc::new(TestApi { authorities: vec![] });

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
			Some(HashSet::from([remote_addr])),
			service.get_addresses_by_authority_id(remote_authority_id.clone()).await,
		);
		assert_eq!(
			Some(HashSet::from([remote_authority_id])),
			service.get_authority_ids_by_peer_id(remote_peer_id).await,
		);
	});
}

#[test]
fn cryptos_are_compatible() {
	use sp_core::crypto::Pair;

	let libp2p_keypair = ed25519::Keypair::generate();
	let libp2p_public = libp2p_keypair.public();

	let sp_core_secret =
		{ sp_core::ed25519::Pair::from_seed_slice(&libp2p_keypair.secret().as_ref()).unwrap() };
	let sp_core_public = sp_core_secret.public();

	let message = b"we are more powerful than not to be better";

	let libp2p_signature = libp2p_keypair.sign(message);
	let sp_core_signature = sp_core_secret.sign(message); // no error expected...

	assert!(sp_core::ed25519::Pair::verify(
		&sp_core::ed25519::Signature::from_slice(&libp2p_signature).unwrap(),
		message,
		&sp_core_public
	));
	assert!(libp2p_public.verify(message, sp_core_signature.as_ref()));
}
