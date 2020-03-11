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

use std::{iter::FromIterator, sync::{Arc, Mutex}};

use futures::channel::mpsc::channel;
use futures::executor::block_on;
use futures::future::poll_fn;
use libp2p::{kad, PeerId};

use sp_api::{ApiExt, ApiErrorExt, Core, RuntimeVersion, StorageProof, ProvideRuntimeApi, ApiRef};
use sp_core::{testing::KeyStore, ExecutionContext, NativeOrEncoded};
use sp_runtime::traits::{Zero, Block as BlockT, NumberFor};
use substrate_test_runtime_client::runtime::Block;

use super::*;

#[test]
fn interval_at_with_start_now() {
	let start = Instant::now();

	let mut interval = interval_at(
		std::time::Instant::now(),
		std::time::Duration::from_secs(10),
	);

	futures::executor::block_on(async {
		interval.next().await;
	});

	assert!(
		Instant::now().saturating_duration_since(start) < Duration::from_secs(1),
		"Expected low resolution instant interval to fire within less than a second.",
	);
}

#[test]
fn interval_at_is_queuing_ticks() {
	let start = Instant::now();

	let interval = interval_at(start, std::time::Duration::from_millis(100));

	// Let's wait for 200ms, thus 3 elements should be queued up (1st at 0ms, 2nd at 100ms, 3rd
	// at 200ms).
	std::thread::sleep(Duration::from_millis(200));

	futures::executor::block_on(async {
		interval.take(3).collect::<Vec<()>>().await;
	});

	// Make sure we did not wait for more than 300 ms, which would imply that `at_interval` is
	// not queuing ticks.
	assert!(
		Instant::now().saturating_duration_since(start) < Duration::from_millis(300),
		"Expect interval to /queue/ events when not polled for a while.",
	);
}

#[test]
fn interval_at_with_initial_delay() {
	let start = Instant::now();

	let mut interval = interval_at(
		std::time::Instant::now() + Duration::from_millis(100),
		std::time::Duration::from_secs(10),
	);

	futures::executor::block_on(async {
		interval.next().await;
	});

	assert!(
		Instant::now().saturating_duration_since(start) > Duration::from_millis(100),
		"Expected interval with initial delay not to fire right away.",
	);
}

#[derive(Clone)]
struct TestApi {
	authorities: Vec<AuthorityId>,
}

impl ProvideRuntimeApi<Block> for TestApi {
	type Api = RuntimeApi;

	fn runtime_api<'a>(&'a self) -> ApiRef<'a, Self::Api> {
		RuntimeApi {
			authorities: self.authorities.clone(),
		}
		.into()
	}
}

/// Blockchain database header backend. Does not perform any validation.
impl<Block: BlockT> HeaderBackend<Block> for TestApi {
	fn header(
		&self,
		_id: BlockId<Block>,
	) -> std::result::Result<Option<Block::Header>, sp_blockchain::Error> {
		Ok(None)
	}

	fn info(&self) -> sc_client_api::blockchain::Info<Block> {
		sc_client_api::blockchain::Info {
			best_hash: Default::default(),
			best_number: Zero::zero(),
			finalized_hash: Default::default(),
			finalized_number: Zero::zero(),
			genesis_hash: Default::default(),
		}
	}

	fn status(
		&self,
		_id: BlockId<Block>,
	) -> std::result::Result<sc_client_api::blockchain::BlockStatus, sp_blockchain::Error> {
		Ok(sc_client_api::blockchain::BlockStatus::Unknown)
	}

	fn number(
		&self,
		_hash: Block::Hash,
	) -> std::result::Result<Option<NumberFor<Block>>, sp_blockchain::Error> {
		Ok(None)
	}

	fn hash(
		&self,
		_number: NumberFor<Block>,
	) -> std::result::Result<Option<Block::Hash>, sp_blockchain::Error> {
		Ok(None)
	}
}

struct RuntimeApi {
	authorities: Vec<AuthorityId>,
}

impl Core<Block> for RuntimeApi {
	fn Core_version_runtime_api_impl(
		&self,
		_: &BlockId<Block>,
		_: ExecutionContext,
		_: Option<()>,
		_: Vec<u8>,
	) -> std::result::Result<NativeOrEncoded<RuntimeVersion>, sp_blockchain::Error> {
		unimplemented!("Not required for testing!")
	}

	fn Core_execute_block_runtime_api_impl(
		&self,
		_: &BlockId<Block>,
		_: ExecutionContext,
		_: Option<Block>,
		_: Vec<u8>,
	) -> std::result::Result<NativeOrEncoded<()>, sp_blockchain::Error> {
		unimplemented!("Not required for testing!")
	}

	fn Core_initialize_block_runtime_api_impl(
		&self,
		_: &BlockId<Block>,
		_: ExecutionContext,
		_: Option<&<Block as BlockT>::Header>,
		_: Vec<u8>,
	) -> std::result::Result<NativeOrEncoded<()>, sp_blockchain::Error> {
		unimplemented!("Not required for testing!")
	}
}

impl ApiErrorExt for RuntimeApi {
	type Error = sp_blockchain::Error;
}

impl ApiExt<Block> for RuntimeApi {
	type StateBackend = <
		substrate_test_runtime_client::Backend as sc_client_api::backend::Backend<Block>
	>::State;

	fn map_api_result<F: FnOnce(&Self) -> std::result::Result<R, E>, R, E>(
		&self,
		_: F
	) -> std::result::Result<R, E> {
		unimplemented!("Not required for testing!")
	}

	fn runtime_version_at(
		&self,
		_: &BlockId<Block>,
	) -> std::result::Result<RuntimeVersion, Self::Error> {
		unimplemented!("Not required for testing!")
	}

	fn record_proof(&mut self) {
		unimplemented!("Not required for testing!")
	}

	fn extract_proof(&mut self) -> Option<StorageProof> {
		unimplemented!("Not required for testing!")
	}

	fn into_storage_changes(
		&self,
		_: &Self::StateBackend,
		_: Option<&sp_api::ChangesTrieState<sp_api::HashFor<Block>, sp_api::NumberFor<Block>>>,
		_: <Block as sp_api::BlockT>::Hash,
	) -> std::result::Result<sp_api::StorageChanges<Self::StateBackend, Block>, String>
		where Self: Sized
	{
		unimplemented!("Not required for testing!")
	}
}

impl AuthorityDiscoveryApi<Block> for RuntimeApi {
	fn AuthorityDiscoveryApi_authorities_runtime_api_impl(
		&self,
		_: &BlockId<Block>,
		_: ExecutionContext,
		_: Option<()>,
		_: Vec<u8>,
	) -> std::result::Result<NativeOrEncoded<Vec<AuthorityId>>, sp_blockchain::Error> {
		return Ok(NativeOrEncoded::Native(self.authorities.clone()));
	}
}

#[derive(Default)]
struct TestNetwork {
	// Whenever functions on `TestNetwork` are called, the function arguments are added to the
	// vectors below.
	pub put_value_call: Arc<Mutex<Vec<(kad::record::Key, Vec<u8>)>>>,
	pub get_value_call: Arc<Mutex<Vec<kad::record::Key>>>,
	pub set_priority_group_call: Arc<Mutex<Vec<(String, HashSet<Multiaddr>)>>>,
}

impl NetworkProvider for TestNetwork {
	fn set_priority_group(
		&self,
		group_id: String,
		peers: HashSet<Multiaddr>,
	) -> std::result::Result<(), String> {
		self.set_priority_group_call
			.lock()
			.unwrap()
			.push((group_id, peers));
		Ok(())
	}
	fn put_value(&self, key: kad::record::Key, value: Vec<u8>) {
		self.put_value_call.lock().unwrap().push((key, value));
	}
	fn get_value(&self, key: &kad::record::Key) {
		self.get_value_call.lock().unwrap().push(key.clone());
	}
}

impl NetworkStateInfo for TestNetwork {
	fn local_peer_id(&self) -> PeerId {
		PeerId::random()
	}

	fn external_addresses(&self) -> Vec<Multiaddr> {
		vec![]
	}
}

#[test]
fn publish_ext_addresses_puts_record_on_dht() {
	let (_dht_event_tx, dht_event_rx) = channel(1000);
	let network: Arc<TestNetwork> = Arc::new(Default::default());
	let key_store = KeyStore::new();
	let public = key_store
		.write()
		.sr25519_generate_new(key_types::AUTHORITY_DISCOVERY, None)
		.unwrap();
	let test_api = Arc::new(TestApi {
		authorities: vec![public.into()],
	});

	let mut authority_discovery = AuthorityDiscovery::new(
		test_api,
		network.clone(),
		vec![],
		key_store,
		dht_event_rx.boxed(),
	);

	authority_discovery.publish_ext_addresses().unwrap();

	// Expect authority discovery to put a new record onto the dht.
	assert_eq!(network.put_value_call.lock().unwrap().len(), 1);
}

#[test]
fn request_addresses_of_others_triggers_dht_get_query() {
	let _ = ::env_logger::try_init();
	let (_dht_event_tx, dht_event_rx) = channel(1000);

	// Generate authority keys
	let authority_1_key_pair = AuthorityPair::from_seed_slice(&[1; 32]).unwrap();
	let authority_2_key_pair = AuthorityPair::from_seed_slice(&[2; 32]).unwrap();

	let test_api = Arc::new(TestApi {
		authorities: vec![authority_1_key_pair.public(), authority_2_key_pair.public()],
	});

	let network: Arc<TestNetwork> = Arc::new(Default::default());
	let key_store = KeyStore::new();

	let mut authority_discovery = AuthorityDiscovery::new(
		test_api,
		network.clone(),
		vec![],
		key_store,
		dht_event_rx.boxed(),
	);

	authority_discovery.request_addresses_of_others().unwrap();

	// Expect authority discovery to request new records from the dht.
	assert_eq!(network.get_value_call.lock().unwrap().len(), 2);
}

#[test]
fn handle_dht_events_with_value_found_should_call_set_priority_group() {
	let _ = ::env_logger::try_init();
	// Create authority discovery.

	let (mut dht_event_tx, dht_event_rx) = channel(1000);
	let key_pair = AuthorityPair::from_seed_slice(&[1; 32]).unwrap();
	let test_api = Arc::new(TestApi {
		authorities: vec![key_pair.public()],
	});
	let network: Arc<TestNetwork> = Arc::new(Default::default());
	let key_store = KeyStore::new();

	let mut authority_discovery = AuthorityDiscovery::new(
		test_api,
		network.clone(),
		vec![],
		key_store,
		dht_event_rx.boxed(),
	);

	// Create sample dht event.

	let authority_id_1 = hash_authority_id(key_pair.public().as_ref()).unwrap();
	let address_1: Multiaddr = "/ip6/2001:db8::".parse().unwrap();

	let mut serialized_addresses = vec![];
	schema::AuthorityAddresses {
		addresses: vec![address_1.to_vec()],
	}
	.encode(&mut serialized_addresses)
	.unwrap();

	let signature = key_pair.sign(serialized_addresses.as_ref()).encode();
	let mut signed_addresses = vec![];
	schema::SignedAuthorityAddresses {
		addresses: serialized_addresses,
		signature: signature,
	}
	.encode(&mut signed_addresses)
	.unwrap();

	let dht_event = sc_network::DhtEvent::ValueFound(vec![(authority_id_1, signed_addresses)]);
	dht_event_tx.try_send(dht_event).unwrap();

	// Make authority discovery handle the event.
	let f = |cx: &mut Context<'_>| -> Poll<()> {
		authority_discovery.handle_dht_events(cx).unwrap();

		// Expect authority discovery to set the priority set.
		assert_eq!(network.set_priority_group_call.lock().unwrap().len(), 1);

		assert_eq!(
			network.set_priority_group_call.lock().unwrap()[0],
			(
				"authorities".to_string(),
				HashSet::from_iter(vec![address_1.clone()].into_iter())
			)
		);

		Poll::Ready(())
	};

	let _ = block_on(poll_fn(f));
}
