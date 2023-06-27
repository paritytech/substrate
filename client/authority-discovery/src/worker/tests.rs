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

use std::{
	collections::HashSet,
	sync::{Arc, Mutex},
	task::Poll,
};

use futures::{
	channel::mpsc::{self, channel},
	executor::{block_on, LocalPool},
	future::FutureExt,
	sink::SinkExt,
	task::LocalSpawn,
};
use libp2p::{
	core::multiaddr,
	identity::{Keypair, SigningError},
	kad::record::Key as KademliaKey,
	PeerId,
};
use prometheus_endpoint::prometheus::default_registry;

use sc_client_api::HeaderBackend;
use sc_network::Signature;
use sp_api::{ApiRef, ProvideRuntimeApi};
use sp_keystore::{testing::MemoryKeystore, Keystore};
use sp_runtime::traits::{Block as BlockT, NumberFor, Zero};
use substrate_test_runtime_client::runtime::Block;

use super::*;

#[derive(Clone)]
pub(crate) struct TestApi {
	pub(crate) authorities: Vec<AuthorityId>,
}

impl ProvideRuntimeApi<Block> for TestApi {
	type Api = RuntimeApi;

	fn runtime_api(&self) -> ApiRef<'_, Self::Api> {
		RuntimeApi { authorities: self.authorities.clone() }.into()
	}
}

/// Blockchain database header backend. Does not perform any validation.
impl<Block: BlockT> HeaderBackend<Block> for TestApi {
	fn header(
		&self,
		_hash: Block::Hash,
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
			finalized_state: None,
			block_gap: None,
		}
	}

	fn status(
		&self,
		_hash: Block::Hash,
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

pub(crate) struct RuntimeApi {
	authorities: Vec<AuthorityId>,
}

sp_api::mock_impl_runtime_apis! {
	impl AuthorityDiscoveryApi<Block> for RuntimeApi {
		fn authorities(&self) -> Vec<AuthorityId> {
			self.authorities.clone()
		}
	}
}

#[derive(Debug)]
pub enum TestNetworkEvent {
	GetCalled(KademliaKey),
	PutCalled(KademliaKey, Vec<u8>),
}

pub struct TestNetwork {
	peer_id: PeerId,
	identity: Keypair,
	external_addresses: Vec<Multiaddr>,
	// Whenever functions on `TestNetwork` are called, the function arguments are added to the
	// vectors below.
	pub put_value_call: Arc<Mutex<Vec<(KademliaKey, Vec<u8>)>>>,
	pub get_value_call: Arc<Mutex<Vec<KademliaKey>>>,
	event_sender: mpsc::UnboundedSender<TestNetworkEvent>,
	event_receiver: Option<mpsc::UnboundedReceiver<TestNetworkEvent>>,
}

impl TestNetwork {
	fn get_event_receiver(&mut self) -> Option<mpsc::UnboundedReceiver<TestNetworkEvent>> {
		self.event_receiver.take()
	}
}

impl Default for TestNetwork {
	fn default() -> Self {
		let (tx, rx) = mpsc::unbounded();
		let identity = Keypair::generate_ed25519();
		TestNetwork {
			peer_id: identity.public().to_peer_id(),
			identity,
			external_addresses: vec!["/ip6/2001:db8::/tcp/30333".parse().unwrap()],
			put_value_call: Default::default(),
			get_value_call: Default::default(),
			event_sender: tx,
			event_receiver: Some(rx),
		}
	}
}

impl NetworkSigner for TestNetwork {
	fn sign_with_local_identity(
		&self,
		msg: impl AsRef<[u8]>,
	) -> std::result::Result<Signature, SigningError> {
		Signature::sign_message(msg, &self.identity)
	}
}

impl NetworkDHTProvider for TestNetwork {
	fn put_value(&self, key: KademliaKey, value: Vec<u8>) {
		self.put_value_call.lock().unwrap().push((key.clone(), value.clone()));
		self.event_sender
			.clone()
			.unbounded_send(TestNetworkEvent::PutCalled(key, value))
			.unwrap();
	}
	fn get_value(&self, key: &KademliaKey) {
		self.get_value_call.lock().unwrap().push(key.clone());
		self.event_sender
			.clone()
			.unbounded_send(TestNetworkEvent::GetCalled(key.clone()))
			.unwrap();
	}
}

impl NetworkStateInfo for TestNetwork {
	fn local_peer_id(&self) -> PeerId {
		self.peer_id
	}

	fn external_addresses(&self) -> Vec<Multiaddr> {
		self.external_addresses.clone()
	}

	fn listen_addresses(&self) -> Vec<Multiaddr> {
		self.external_addresses.clone()
	}
}

struct TestSigner<'a> {
	keypair: &'a Keypair,
}

impl<'a> NetworkSigner for TestSigner<'a> {
	fn sign_with_local_identity(
		&self,
		msg: impl AsRef<[u8]>,
	) -> std::result::Result<Signature, SigningError> {
		Signature::sign_message(msg, self.keypair)
	}
}

fn build_dht_event<Signer: NetworkSigner>(
	addresses: Vec<Multiaddr>,
	public_key: AuthorityId,
	key_store: &MemoryKeystore,
	network: Option<&Signer>,
) -> Vec<(KademliaKey, Vec<u8>)> {
	let serialized_record =
		serialize_authority_record(serialize_addresses(addresses.into_iter())).unwrap();

	let peer_signature = network.map(|n| sign_record_with_peer_id(&serialized_record, n).unwrap());
	let kv_pairs = sign_record_with_authority_ids(
		serialized_record,
		peer_signature,
		key_store,
		vec![public_key.into()],
	)
	.unwrap();
	// There is always a single item in it, because we signed it with a single key
	kv_pairs
}

#[test]
fn new_registers_metrics() {
	let (_dht_event_tx, dht_event_rx) = mpsc::channel(1000);
	let network: Arc<TestNetwork> = Arc::new(Default::default());
	let key_store = MemoryKeystore::new();
	let test_api = Arc::new(TestApi { authorities: vec![] });

	let registry = prometheus_endpoint::Registry::new();

	let (_to_worker, from_service) = mpsc::channel(0);
	Worker::new(
		from_service,
		test_api,
		network.clone(),
		Box::pin(dht_event_rx),
		Role::PublishAndDiscover(key_store.into()),
		Some(registry.clone()),
		Default::default(),
	);

	assert!(registry.gather().len() > 0);
}

#[test]
fn triggers_dht_get_query() {
	sp_tracing::try_init_simple();
	let (_dht_event_tx, dht_event_rx) = channel(1000);

	// Generate authority keys
	let authority_1_key_pair = AuthorityPair::from_seed_slice(&[1; 32]).unwrap();
	let authority_2_key_pair = AuthorityPair::from_seed_slice(&[2; 32]).unwrap();
	let authorities = vec![authority_1_key_pair.public(), authority_2_key_pair.public()];

	let test_api = Arc::new(TestApi { authorities: authorities.clone() });

	let network = Arc::new(TestNetwork::default());
	let key_store = MemoryKeystore::new();

	let (_to_worker, from_service) = mpsc::channel(0);
	let mut worker = Worker::new(
		from_service,
		test_api,
		network.clone(),
		Box::pin(dht_event_rx),
		Role::PublishAndDiscover(key_store.into()),
		None,
		Default::default(),
	);

	futures::executor::block_on(async {
		worker.refill_pending_lookups_queue().await.unwrap();
		worker.start_new_lookups();
		assert_eq!(network.get_value_call.lock().unwrap().len(), authorities.len());
	})
}

#[test]
fn publish_discover_cycle() {
	sp_tracing::try_init_simple();

	let mut pool = LocalPool::new();

	// Node A publishing its address.

	let (_dht_event_tx, dht_event_rx) = channel(1000);

	let network: Arc<TestNetwork> = Arc::new(Default::default());

	let key_store = MemoryKeystore::new();

	let _ = pool.spawner().spawn_local_obj(
		async move {
			let node_a_public =
				key_store.sr25519_generate_new(key_types::AUTHORITY_DISCOVERY, None).unwrap();
			let test_api = Arc::new(TestApi { authorities: vec![node_a_public.into()] });

			let (_to_worker, from_service) = mpsc::channel(0);
			let mut worker = Worker::new(
				from_service,
				test_api,
				network.clone(),
				Box::pin(dht_event_rx),
				Role::PublishAndDiscover(key_store.into()),
				None,
				Default::default(),
			);

			worker.publish_ext_addresses(false).await.unwrap();

			// Expect authority discovery to put a new record onto the dht.
			assert_eq!(network.put_value_call.lock().unwrap().len(), 1);

			let dht_event = {
				let (key, value) = network.put_value_call.lock().unwrap().pop().unwrap();
				DhtEvent::ValueFound(vec![(key, value)])
			};

			// Node B discovering node A's address.

			let (mut dht_event_tx, dht_event_rx) = channel(1000);
			let test_api = Arc::new(TestApi {
				// Make sure node B identifies node A as an authority.
				authorities: vec![node_a_public.into()],
			});
			let network: Arc<TestNetwork> = Arc::new(Default::default());
			let key_store = MemoryKeystore::new();

			let (_to_worker, from_service) = mpsc::channel(0);
			let mut worker = Worker::new(
				from_service,
				test_api,
				network.clone(),
				Box::pin(dht_event_rx),
				Role::PublishAndDiscover(key_store.into()),
				None,
				Default::default(),
			);

			dht_event_tx.try_send(dht_event.clone()).unwrap();

			worker.refill_pending_lookups_queue().await.unwrap();
			worker.start_new_lookups();

			// Make authority discovery handle the event.
			worker.handle_dht_event(dht_event).await;
		}
		.boxed_local()
		.into(),
	);

	pool.run();
}

/// Don't terminate when sender side of service channel is dropped. Terminate when network event
/// stream terminates.
#[test]
fn terminate_when_event_stream_terminates() {
	let (dht_event_tx, dht_event_rx) = channel(1000);
	let network: Arc<TestNetwork> = Arc::new(Default::default());
	let key_store = MemoryKeystore::new();
	let test_api = Arc::new(TestApi { authorities: vec![] });

	let (to_worker, from_service) = mpsc::channel(0);
	let worker = Worker::new(
		from_service,
		test_api,
		network.clone(),
		Box::pin(dht_event_rx),
		Role::PublishAndDiscover(key_store.into()),
		None,
		Default::default(),
	)
	.run();
	futures::pin_mut!(worker);

	block_on(async {
		assert_eq!(Poll::Pending, futures::poll!(&mut worker));

		// Drop sender side of service channel.
		drop(to_worker);
		assert_eq!(
			Poll::Pending,
			futures::poll!(&mut worker),
			"Expect the authority discovery module not to terminate once the \
			sender side of the service channel is closed.",
		);

		// Simulate termination of the network through dropping the sender side
		// of the dht event channel.
		drop(dht_event_tx);

		assert_eq!(
			Poll::Ready(()),
			futures::poll!(&mut worker),
			"Expect the authority discovery module to terminate once the \
			 sending side of the dht event channel is closed.",
		);
	});
}

#[test]
fn dont_stop_polling_dht_event_stream_after_bogus_event() {
	let remote_multiaddr = {
		let peer_id = PeerId::random();
		let address: Multiaddr = "/ip6/2001:db8:0:0:0:0:0:1/tcp/30333".parse().unwrap();

		address.with(multiaddr::Protocol::P2p(peer_id.into()))
	};
	let remote_key_store = MemoryKeystore::new();
	let remote_public_key: AuthorityId = remote_key_store
		.sr25519_generate_new(key_types::AUTHORITY_DISCOVERY, None)
		.unwrap()
		.into();

	let (mut dht_event_tx, dht_event_rx) = channel(1);
	let (network, mut network_events) = {
		let mut n = TestNetwork::default();
		let r = n.get_event_receiver().unwrap();
		(Arc::new(n), r)
	};

	let key_store = MemoryKeystore::new();
	let test_api = Arc::new(TestApi { authorities: vec![remote_public_key.clone()] });
	let mut pool = LocalPool::new();

	let (mut to_worker, from_service) = mpsc::channel(1);
	let mut worker = Worker::new(
		from_service,
		test_api,
		network.clone(),
		Box::pin(dht_event_rx),
		Role::PublishAndDiscover(Arc::new(key_store)),
		None,
		Default::default(),
	);

	// Spawn the authority discovery to make sure it is polled independently.
	//
	// As this is a local pool, only one future at a time will have the CPU and
	// can make progress until the future returns `Pending`.
	let _ = pool.spawner().spawn_local_obj(
		async move {
			// Refilling `pending_lookups` only happens every X minutes. Fast
			// forward by calling `refill_pending_lookups_queue` directly.
			worker.refill_pending_lookups_queue().await.unwrap();
			worker.run().await
		}
		.boxed_local()
		.into(),
	);

	pool.run_until(async {
		// Assert worker to trigger a lookup for the one and only authority.
		assert!(matches!(network_events.next().await, Some(TestNetworkEvent::GetCalled(_))));

		// Send an event that should generate an error
		dht_event_tx
			.send(DhtEvent::ValueFound(Default::default()))
			.await
			.expect("Channel has capacity of 1.");

		// Make previously triggered lookup succeed.
		let dht_event = {
			let kv_pairs = build_dht_event::<TestNetwork>(
				vec![remote_multiaddr.clone()],
				remote_public_key.clone(),
				&remote_key_store,
				None,
			);
			DhtEvent::ValueFound(kv_pairs)
		};
		dht_event_tx.send(dht_event).await.expect("Channel has capacity of 1.");

		// Expect authority discovery to function normally, now knowing the
		// address for the remote node.
		let (sender, addresses) = futures::channel::oneshot::channel();
		to_worker
			.send(ServicetoWorkerMsg::GetAddressesByAuthorityId(remote_public_key, sender))
			.await
			.expect("Channel has capacity of 1.");
		assert_eq!(Some(HashSet::from([remote_multiaddr])), addresses.await.unwrap());
	});
}

struct DhtValueFoundTester {
	pub remote_key_store: MemoryKeystore,
	pub remote_authority_public: sp_core::sr25519::Public,
	pub remote_node_key: Keypair,
	pub local_worker: Option<
		Worker<
			TestApi,
			TestNetwork,
			sp_runtime::generic::Block<
				sp_runtime::generic::Header<u64, sp_runtime::traits::BlakeTwo256>,
				substrate_test_runtime_client::runtime::Extrinsic,
			>,
			std::pin::Pin<Box<futures::channel::mpsc::Receiver<DhtEvent>>>,
		>,
	>,
}

impl DhtValueFoundTester {
	fn new() -> Self {
		let remote_key_store = MemoryKeystore::new();
		let remote_authority_public = remote_key_store
			.sr25519_generate_new(key_types::AUTHORITY_DISCOVERY, None)
			.unwrap();

		let remote_node_key = Keypair::generate_ed25519();
		Self { remote_key_store, remote_authority_public, remote_node_key, local_worker: None }
	}

	fn multiaddr_with_peer_id(&self, idx: u16) -> Multiaddr {
		let peer_id = self.remote_node_key.public().to_peer_id();
		let address: Multiaddr =
			format!("/ip6/2001:db8:0:0:0:0:0:{:x}/tcp/30333", idx).parse().unwrap();

		address.with(multiaddr::Protocol::P2p(peer_id.into()))
	}

	fn process_value_found(
		&mut self,
		strict_record_validation: bool,
		values: Vec<(KademliaKey, Vec<u8>)>,
	) -> Option<&HashSet<Multiaddr>> {
		let (_dht_event_tx, dht_event_rx) = channel(1);
		let local_test_api =
			Arc::new(TestApi { authorities: vec![self.remote_authority_public.into()] });
		let local_network: Arc<TestNetwork> = Arc::new(Default::default());
		let local_key_store = MemoryKeystore::new();

		let (_to_worker, from_service) = mpsc::channel(0);
		let mut local_worker = Worker::new(
			from_service,
			local_test_api,
			local_network.clone(),
			Box::pin(dht_event_rx),
			Role::PublishAndDiscover(Arc::new(local_key_store)),
			None,
			WorkerConfig { strict_record_validation, ..Default::default() },
		);

		block_on(local_worker.refill_pending_lookups_queue()).unwrap();
		local_worker.start_new_lookups();

		drop(local_worker.handle_dht_value_found_event(values));

		self.local_worker = Some(local_worker);

		self.local_worker
			.as_ref()
			.map(|w| {
				w.addr_cache.get_addresses_by_authority_id(&self.remote_authority_public.into())
			})
			.unwrap()
	}
}

#[test]
fn limit_number_of_addresses_added_to_cache_per_authority() {
	let mut tester = DhtValueFoundTester::new();
	assert!(MAX_ADDRESSES_PER_AUTHORITY < 100);
	let addresses = (1..100).map(|i| tester.multiaddr_with_peer_id(i)).collect();
	let kv_pairs = build_dht_event::<TestNetwork>(
		addresses,
		tester.remote_authority_public.into(),
		&tester.remote_key_store,
		None,
	);

	let cached_remote_addresses = tester.process_value_found(false, kv_pairs);
	assert_eq!(MAX_ADDRESSES_PER_AUTHORITY, cached_remote_addresses.unwrap().len());
}

#[test]
fn strict_accept_address_with_peer_signature() {
	let mut tester = DhtValueFoundTester::new();
	let addr = tester.multiaddr_with_peer_id(1);
	let kv_pairs = build_dht_event(
		vec![addr.clone()],
		tester.remote_authority_public.into(),
		&tester.remote_key_store,
		Some(&TestSigner { keypair: &tester.remote_node_key }),
	);

	let cached_remote_addresses = tester.process_value_found(true, kv_pairs);

	assert_eq!(
		Some(&HashSet::from([addr])),
		cached_remote_addresses,
		"Expect worker to only cache `Multiaddr`s with `PeerId`s.",
	);
}

#[test]
fn reject_address_with_rogue_peer_signature() {
	let mut tester = DhtValueFoundTester::new();
	let rogue_remote_node_key = Keypair::generate_ed25519();
	let kv_pairs = build_dht_event(
		vec![tester.multiaddr_with_peer_id(1)],
		tester.remote_authority_public.into(),
		&tester.remote_key_store,
		Some(&TestSigner { keypair: &rogue_remote_node_key }),
	);

	let cached_remote_addresses = tester.process_value_found(false, kv_pairs);

	assert!(
		cached_remote_addresses.is_none(),
		"Expected worker to ignore record signed by a different key.",
	);
}

#[test]
fn reject_address_with_invalid_peer_signature() {
	let mut tester = DhtValueFoundTester::new();
	let mut kv_pairs = build_dht_event(
		vec![tester.multiaddr_with_peer_id(1)],
		tester.remote_authority_public.into(),
		&tester.remote_key_store,
		Some(&TestSigner { keypair: &tester.remote_node_key }),
	);
	// tamper with the signature
	let mut record = schema::SignedAuthorityRecord::decode(kv_pairs[0].1.as_slice()).unwrap();
	record.peer_signature.as_mut().map(|p| p.signature[1] = !p.signature[1]);
	record.encode(&mut kv_pairs[0].1).unwrap();

	let cached_remote_addresses = tester.process_value_found(false, kv_pairs);

	assert!(
		cached_remote_addresses.is_none(),
		"Expected worker to ignore record with tampered signature.",
	);
}

#[test]
fn reject_address_without_peer_signature() {
	let mut tester = DhtValueFoundTester::new();
	let kv_pairs = build_dht_event::<TestNetwork>(
		vec![tester.multiaddr_with_peer_id(1)],
		tester.remote_authority_public.into(),
		&tester.remote_key_store,
		None,
	);

	let cached_remote_addresses = tester.process_value_found(true, kv_pairs);

	assert!(cached_remote_addresses.is_none(), "Expected worker to ignore unsigned record.",);
}

#[test]
fn do_not_cache_addresses_without_peer_id() {
	let mut tester = DhtValueFoundTester::new();
	let multiaddr_with_peer_id = tester.multiaddr_with_peer_id(1);
	let multiaddr_without_peer_id: Multiaddr =
		"/ip6/2001:db8:0:0:0:0:0:2/tcp/30333".parse().unwrap();
	let kv_pairs = build_dht_event::<TestNetwork>(
		vec![multiaddr_with_peer_id.clone(), multiaddr_without_peer_id],
		tester.remote_authority_public.into(),
		&tester.remote_key_store,
		None,
	);

	let cached_remote_addresses = tester.process_value_found(false, kv_pairs);

	assert_eq!(
		Some(&HashSet::from([multiaddr_with_peer_id])),
		cached_remote_addresses,
		"Expect worker to only cache `Multiaddr`s with `PeerId`s.",
	);
}

#[test]
fn addresses_to_publish_adds_p2p() {
	let (_dht_event_tx, dht_event_rx) = channel(1000);
	let network: Arc<TestNetwork> = Arc::new(Default::default());

	assert!(!matches!(
		network.external_addresses().pop().unwrap().pop().unwrap(),
		multiaddr::Protocol::P2p(_)
	));

	let (_to_worker, from_service) = mpsc::channel(0);
	let worker = Worker::new(
		from_service,
		Arc::new(TestApi { authorities: vec![] }),
		network.clone(),
		Box::pin(dht_event_rx),
		Role::PublishAndDiscover(MemoryKeystore::new().into()),
		Some(prometheus_endpoint::Registry::new()),
		Default::default(),
	);

	assert!(
		matches!(
			worker.addresses_to_publish().next().unwrap().pop().unwrap(),
			multiaddr::Protocol::P2p(_)
		),
		"Expect `addresses_to_publish` to append `p2p` protocol component.",
	);
}

/// Ensure [`Worker::addresses_to_publish`] does not add an additional `p2p` protocol component in
/// case one already exists.
#[test]
fn addresses_to_publish_respects_existing_p2p_protocol() {
	let (_dht_event_tx, dht_event_rx) = channel(1000);
	let network: Arc<TestNetwork> = Arc::new(TestNetwork {
		external_addresses: vec![
			"/ip6/2001:db8::/tcp/30333/p2p/QmcgpsyWgH8Y8ajJz1Cu72KnS5uo2Aa2LpzU7kinSupNKC"
				.parse()
				.unwrap(),
		],
		..Default::default()
	});

	let (_to_worker, from_service) = mpsc::channel(0);
	let worker = Worker::new(
		from_service,
		Arc::new(TestApi { authorities: vec![] }),
		network.clone(),
		Box::pin(dht_event_rx),
		Role::PublishAndDiscover(MemoryKeystore::new().into()),
		Some(prometheus_endpoint::Registry::new()),
		Default::default(),
	);

	assert_eq!(
		network.external_addresses,
		worker.addresses_to_publish().collect::<Vec<_>>(),
		"Expected Multiaddr from `TestNetwork` to not be altered.",
	);
}

#[test]
fn lookup_throttling() {
	let remote_multiaddr = {
		let peer_id = PeerId::random();
		let address: Multiaddr = "/ip6/2001:db8:0:0:0:0:0:1/tcp/30333".parse().unwrap();

		address.with(multiaddr::Protocol::P2p(peer_id.into()))
	};
	let remote_key_store = MemoryKeystore::new();
	let remote_public_keys: Vec<AuthorityId> = (0..20)
		.map(|_| {
			remote_key_store
				.sr25519_generate_new(key_types::AUTHORITY_DISCOVERY, None)
				.unwrap()
				.into()
		})
		.collect();
	let remote_hash_to_key = remote_public_keys
		.iter()
		.map(|k| (hash_authority_id(k.as_ref()), k.clone()))
		.collect::<HashMap<_, _>>();

	let (mut dht_event_tx, dht_event_rx) = channel(1);
	let (_to_worker, from_service) = mpsc::channel(0);
	let mut network = TestNetwork::default();
	let mut receiver = network.get_event_receiver().unwrap();
	let network = Arc::new(network);
	let mut worker = Worker::new(
		from_service,
		Arc::new(TestApi { authorities: remote_public_keys.clone() }),
		network.clone(),
		dht_event_rx.boxed(),
		Role::Discover,
		Some(default_registry().clone()),
		Default::default(),
	);

	let mut pool = LocalPool::new();
	let metrics = worker.metrics.clone().unwrap();

	let _ = pool.spawner().spawn_local_obj(
		async move {
			// Refilling `pending_lookups` only happens every X minutes. Fast
			// forward by calling `refill_pending_lookups_queue` directly.
			worker.refill_pending_lookups_queue().await.unwrap();
			worker.run().await
		}
		.boxed_local()
		.into(),
	);

	pool.run_until(
		async {
			// Assert worker to trigger MAX_IN_FLIGHT_LOOKUPS lookups.
			for _ in 0..MAX_IN_FLIGHT_LOOKUPS {
				assert!(matches!(receiver.next().await, Some(TestNetworkEvent::GetCalled(_))));
			}
			assert_eq!(
				metrics.requests_pending.get(),
				(remote_public_keys.len() - MAX_IN_FLIGHT_LOOKUPS) as u64
			);
			assert_eq!(network.get_value_call.lock().unwrap().len(), MAX_IN_FLIGHT_LOOKUPS);

			// Make first lookup succeed.
			let remote_hash = network.get_value_call.lock().unwrap().pop().unwrap();
			let remote_key: AuthorityId = remote_hash_to_key.get(&remote_hash).unwrap().clone();
			let dht_event = {
				let kv_pairs = build_dht_event::<TestNetwork>(
					vec![remote_multiaddr.clone()],
					remote_key,
					&remote_key_store,
					None,
				);
				DhtEvent::ValueFound(kv_pairs)
			};
			dht_event_tx.send(dht_event).await.expect("Channel has capacity of 1.");

			// Assert worker to trigger another lookup.
			assert!(matches!(receiver.next().await, Some(TestNetworkEvent::GetCalled(_))));
			assert_eq!(
				metrics.requests_pending.get(),
				(remote_public_keys.len() - MAX_IN_FLIGHT_LOOKUPS - 1) as u64
			);
			assert_eq!(network.get_value_call.lock().unwrap().len(), MAX_IN_FLIGHT_LOOKUPS);

			// Make second one fail.
			let remote_hash = network.get_value_call.lock().unwrap().pop().unwrap();
			let dht_event = DhtEvent::ValueNotFound(remote_hash);
			dht_event_tx.send(dht_event).await.expect("Channel has capacity of 1.");

			// Assert worker to trigger another lookup.
			assert!(matches!(receiver.next().await, Some(TestNetworkEvent::GetCalled(_))));
			assert_eq!(
				metrics.requests_pending.get(),
				(remote_public_keys.len() - MAX_IN_FLIGHT_LOOKUPS - 2) as u64
			);
			assert_eq!(network.get_value_call.lock().unwrap().len(), MAX_IN_FLIGHT_LOOKUPS);
		}
		.boxed_local(),
	);
}
