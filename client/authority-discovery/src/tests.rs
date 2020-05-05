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
use futures::executor::{block_on, LocalPool};
use futures::future::{poll_fn, FutureExt};
use futures::sink::SinkExt;
use futures::task::LocalSpawn;
use futures::poll;
use libp2p::{kad, PeerId};

use sp_api::{ProvideRuntimeApi, ApiRef};
use sp_core::testing::KeyStore;
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
		}.into()
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
			number_leaves: Default::default(),
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

sp_api::mock_impl_runtime_apis! {
	impl AuthorityDiscoveryApi<Block> for RuntimeApi {
		type Error = sp_blockchain::Error;

		fn authorities(&self) -> Vec<AuthorityId> {
			self.authorities.clone()
		}
	}
}

struct TestNetwork {
	peer_id: PeerId,
	// Whenever functions on `TestNetwork` are called, the function arguments are added to the
	// vectors below.
	pub put_value_call: Arc<Mutex<Vec<(kad::record::Key, Vec<u8>)>>>,
	pub get_value_call: Arc<Mutex<Vec<kad::record::Key>>>,
	pub set_priority_group_call: Arc<Mutex<Vec<(String, HashSet<Multiaddr>)>>>,
}

impl Default for TestNetwork {
	fn default() -> Self {
		TestNetwork {
			peer_id: PeerId::random(),
			put_value_call: Default::default(),
			get_value_call: Default::default(),
			set_priority_group_call: Default::default(),
		}
	}
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
		self.peer_id.clone()
	}

	fn external_addresses(&self) -> Vec<Multiaddr> {
		vec!["/ip6/2001:db8::".parse().unwrap()]
	}
}

#[test]
fn new_registers_metrics() {
	let (_dht_event_tx, dht_event_rx) = channel(1000);
	let network: Arc<TestNetwork> = Arc::new(Default::default());
	let key_store = KeyStore::new();
	let test_api = Arc::new(TestApi {
		authorities: vec![],
	});

	let registry = prometheus_endpoint::Registry::new();

	AuthorityDiscovery::new(
		test_api,
		network.clone(),
		vec![],
		dht_event_rx.boxed(),
		Role::Authority(key_store),
		Some(registry.clone()),
	);

	assert!(registry.gather().len() > 0);
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
		dht_event_rx.boxed(),
		Role::Authority(key_store),
		None,
	);

	authority_discovery.request_addresses_of_others().unwrap();

	// Expect authority discovery to request new records from the dht.
	assert_eq!(network.get_value_call.lock().unwrap().len(), 2);
}

#[test]
fn publish_discover_cycle() {
	let _ = ::env_logger::try_init();

	// Node A publishing its address.

	let (_dht_event_tx, dht_event_rx) = channel(1000);

	let network: Arc<TestNetwork> = Arc::new(Default::default());
	let node_a_multiaddr = {
		let peer_id = network.local_peer_id();
		let address = network.external_addresses().pop().unwrap();

		address.with(libp2p::core::multiaddr::Protocol::P2p(
			peer_id.into(),
		))
	};

	let key_store = KeyStore::new();
	let node_a_public = key_store
		.write()
		.sr25519_generate_new(key_types::AUTHORITY_DISCOVERY, None)
		.unwrap();
	let test_api = Arc::new(TestApi {
		authorities: vec![node_a_public.into()],
	});

	let mut authority_discovery = AuthorityDiscovery::new(
		test_api,
		network.clone(),
		vec![],
		dht_event_rx.boxed(),
		Role::Authority(key_store),
		None,
	);

	authority_discovery.publish_ext_addresses().unwrap();

	// Expect authority discovery to put a new record onto the dht.
	assert_eq!(network.put_value_call.lock().unwrap().len(), 1);

	let dht_event = {
		let (key, value) = network.put_value_call.lock().unwrap().pop().unwrap();
		sc_network::DhtEvent::ValueFound(vec![(key, value)])
	};

	// Node B discovering node A's address.

	let (mut dht_event_tx, dht_event_rx) = channel(1000);
	let test_api = Arc::new(TestApi {
		// Make sure node B identifies node A as an authority.
		authorities: vec![node_a_public.into()],
	});
	let network: Arc<TestNetwork> = Arc::new(Default::default());
	let key_store = KeyStore::new();

	let mut authority_discovery = AuthorityDiscovery::new(
		test_api,
		network.clone(),
		vec![],
		dht_event_rx.boxed(),
		Role::Authority(key_store),
		None,
	);

	dht_event_tx.try_send(dht_event).unwrap();

	let f = |cx: &mut Context<'_>| -> Poll<()> {
		// Make authority discovery handle the event.
		if let Poll::Ready(e) = authority_discovery.handle_dht_events(cx) {
			panic!("Unexpected error: {:?}", e);
		}

		// Expect authority discovery to set the priority set.
		assert_eq!(network.set_priority_group_call.lock().unwrap().len(), 1);

		assert_eq!(
			network.set_priority_group_call.lock().unwrap()[0],
			(
				"authorities".to_string(),
				HashSet::from_iter(vec![node_a_multiaddr.clone()].into_iter())
			)
		);

		Poll::Ready(())
	};

	let _ = block_on(poll_fn(f));
}

#[test]
fn terminate_when_event_stream_terminates() {
	let (dht_event_tx, dht_event_rx) = channel(1000);
	let network: Arc<TestNetwork> = Arc::new(Default::default());
	let key_store = KeyStore::new();
	let test_api = Arc::new(TestApi {
		authorities: vec![],
	});

	let mut authority_discovery = AuthorityDiscovery::new(
		test_api,
		network.clone(),
		vec![],
		dht_event_rx.boxed(),
		Role::Authority(key_store),
		None,
	);

	block_on(async {
		assert_eq!(Poll::Pending, poll!(&mut authority_discovery));

		// Simulate termination of the network through dropping the sender side of the dht event
		// channel.
		drop(dht_event_tx);

		assert_eq!(
			Poll::Ready(()), poll!(&mut authority_discovery),
			"Expect the authority discovery module to terminate once the sending side of the dht \
			event channel is terminated.",
		);
	});
}

#[test]
fn dont_stop_polling_when_error_is_returned() {
	#[derive(PartialEq, Debug)]
	enum Event {
		Processed,
		End,
	};

	let (mut dht_event_tx, dht_event_rx) = channel(1000);
	let (mut discovery_update_tx, mut discovery_update_rx) = channel(1000);
	let network: Arc<TestNetwork> = Arc::new(Default::default());
	let key_store = KeyStore::new();
	let test_api = Arc::new(TestApi {
		authorities: vec![],
	});
	let mut pool = LocalPool::new();

	let mut authority_discovery = AuthorityDiscovery::new(
		test_api,
		network.clone(),
		vec![],
		dht_event_rx.boxed(),
		Role::Authority(key_store),
		None,
	);

	// Spawn the authority discovery to make sure it is polled independently.
	//
	// As this is a local pool, only one future at a time will have the CPU and
	// can make progress until the future returns `Pending`.
	pool.spawner().spawn_local_obj(
		futures::future::poll_fn(move |ctx| {
			match std::pin::Pin::new(&mut authority_discovery).poll(ctx) {
				Poll::Ready(()) => {},
				Poll::Pending => {
					discovery_update_tx.send(Event::Processed).now_or_never();
					return Poll::Pending;
				},
			}
			let _ = discovery_update_tx.send(Event::End).now_or_never().unwrap();
			Poll::Ready(())
		}).boxed_local().into(),
	).expect("Spawns authority discovery");

	pool.run_until(
		// The future that drives the event stream
		async {
			// Send an event that should generate an error
			let _ = dht_event_tx.send(DhtEvent::ValueFound(Default::default())).now_or_never();
			// Send the same event again to make sure that the event stream needs to be polled twice
			// to be woken up again.
			let _ = dht_event_tx.send(DhtEvent::ValueFound(Default::default())).now_or_never();

			// Now we call `await` and give the control to the authority discovery future.
			assert_eq!(Some(Event::Processed), discovery_update_rx.next().await);

			// Drop the event rx to stop the authority discovery. If it was polled correctly, it
			// should end properly.
			drop(dht_event_tx);

			assert!(
				discovery_update_rx.collect::<Vec<Event>>()
					.await
					.into_iter()
					.any(|evt| evt == Event::End),
				"The authority discovery should have ended",
			);
		}
	);
}
