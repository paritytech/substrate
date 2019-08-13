// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! BABE testsuite

// FIXME #2532: need to allow deprecated until refactor is done
// https://github.com/paritytech/substrate/issues/2532
#![allow(deprecated)]
use super::*;

use babe_primitives::AuthorityPair;
use client::{LongestChain, block_builder::BlockBuilder};
use consensus_common::NoNetwork as DummyOracle;
use network::test::*;
use network::test::{Block as TestBlock, PeersClient};
use sr_primitives::{generic::DigestItem, traits::{Block as BlockT, DigestFor}};
use network::config::ProtocolConfig;
use tokio::runtime::current_thread;
use keyring::sr25519::Keyring;
use client::BlockchainEvents;
use test_client;
use log::debug;
use std::{time::Duration, borrow::Borrow, cell::RefCell};

type Item = DigestItem<Hash>;

type Error = client::error::Error;

type TestClient = client::Client<
	test_client::Backend,
	test_client::Executor,
	TestBlock,
	test_client::runtime::RuntimeApi,
>;

struct DummyFactory(Arc<TestClient>);
struct DummyProposer(u64, Arc<TestClient>);

impl Environment<TestBlock> for DummyFactory {
	type Proposer = DummyProposer;
	type Error = Error;

	fn init(&mut self, parent_header: &<TestBlock as BlockT>::Header)
		-> Result<DummyProposer, Error>
	{
		Ok(DummyProposer(parent_header.number + 1, self.0.clone()))
	}
}

impl Proposer<TestBlock> for DummyProposer {
	type Error = Error;
	type Create = future::Ready<Result<TestBlock, Error>>;

	fn propose(
		&mut self,
		_: InherentData,
		digests: DigestFor<TestBlock>,
		_: Duration,
	) -> Self::Create {
		future::ready(self.1.new_block(digests).unwrap().bake().map_err(|e| e.into()))
	}
}

type Mutator = Arc<dyn for<'r> Fn(&'r mut TestHeader) + Send + Sync>;

thread_local! {
	static MUTATOR: RefCell<Mutator> = RefCell::new(Arc::new(|_|()));
}

pub struct BabeTestNet {
	peers: Vec<Peer<(), DummySpecialization>>,
}

type TestHeader = <TestBlock as BlockT>::Header;
type TestExtrinsic = <TestBlock as BlockT>::Extrinsic;

pub struct TestVerifier {
	inner: BabeVerifier<
		test_client::Backend,
		test_client::Executor,
		TestBlock,
		test_client::runtime::RuntimeApi,
		PeersFullClient,
		(),
	>,
	mutator: Mutator,
}

impl Verifier<TestBlock> for TestVerifier {
	/// Verify the given data and return the BlockImportParams and an optional
	/// new set of validators to import. If not, err with an Error-Message
	/// presented to the User in the logs.
	fn verify(
		&mut self,
		origin: BlockOrigin,
		mut header: TestHeader,
		justification: Option<Justification>,
		body: Option<Vec<TestExtrinsic>>,
	) -> Result<(BlockImportParams<TestBlock>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		let cb: &(dyn Fn(&mut TestHeader) + Send + Sync) = self.mutator.borrow();
		cb(&mut header);
		Ok(self.inner.verify(origin, header, justification, body).expect("verification failed!"))
	}
}

impl TestNetFactory for BabeTestNet {
	type Specialization = DummySpecialization;
	type Verifier = TestVerifier;
	type PeerData = ();

	/// Create new test network with peers and given config.
	fn from_config(_config: &ProtocolConfig) -> Self {
		debug!(target: "babe", "Creating test network from config");
		BabeTestNet {
			peers: Vec::new(),
		}
	}

	/// KLUDGE: this function gets the mutator from thread-local storage.
	fn make_verifier(&self, client: PeersClient, _cfg: &ProtocolConfig)
		-> Self::Verifier
	{
		let client = client.as_full().expect("only full clients are used in test");
		trace!(target: "babe", "Creating a verifier");
		let config = Config::get_or_compute(&*client)
			.expect("slot duration available");
		let inherent_data_providers = InherentDataProviders::new();
		register_babe_inherent_data_provider(
			&inherent_data_providers,
			config.get()
		).expect("Registers babe inherent data provider");
		trace!(target: "babe", "Provider registered");

		TestVerifier {
			inner: BabeVerifier {
				client: client.clone(),
				api: client,
				inherent_data_providers,
				config,
				time_source: Default::default(),
				transaction_pool : Default::default(),
			},
			mutator: MUTATOR.with(|s| s.borrow().clone()),
		}
	}

	fn peer(&mut self, i: usize) -> &mut Peer<Self::PeerData, DummySpecialization> {
		trace!(target: "babe", "Retreiving a peer");
		&mut self.peers[i]
	}

	fn peers(&self) -> &Vec<Peer<Self::PeerData, DummySpecialization>> {
		trace!(target: "babe", "Retreiving peers");
		&self.peers
	}

	fn mut_peers<F: FnOnce(&mut Vec<Peer<Self::PeerData, DummySpecialization>>)>(
		&mut self,
		closure: F,
	) {
		closure(&mut self.peers);
	}
}

#[test]
#[should_panic]
fn rejects_empty_block() {
	env_logger::try_init().unwrap();
	let mut net = BabeTestNet::new(3);
	let block_builder = |builder: BlockBuilder<_, _>| {
		builder.bake().unwrap()
	};
	net.mut_peers(|peer| {
		peer[0].generate_blocks(1, BlockOrigin::NetworkInitialSync, block_builder);
	})
}

fn run_one_test() {
	let _ = env_logger::try_init();
	let net = BabeTestNet::new(3);

	let peers = &[
		(0, "//Alice"),
		(1, "//Bob"),
		(2, "//Charlie"),
	];

	let net = Arc::new(Mutex::new(net));
	let mut import_notifications = Vec::new();
	let mut runtime = current_thread::Runtime::new().unwrap();
	let mut keystore_paths = Vec::new();
	for (peer_id, seed) in peers {
		let keystore_path = tempfile::tempdir().expect("Creates keystore path");
		let keystore = keystore::Store::open(keystore_path.path(), None).expect("Creates keystore");
		keystore.write().insert_ephemeral_from_seed::<AuthorityPair>(seed).expect("Generates authority key");
		keystore_paths.push(keystore_path);

		let client = net.lock().peer(*peer_id).client().as_full().unwrap();
		let environ = DummyFactory(client.clone());
		import_notifications.push(
			client.import_notification_stream()
				.take_while(|n| future::ready(!(n.origin != BlockOrigin::Own && n.header.number() < &5)))
				.for_each(move |_| future::ready(()))
		);

		let config = Config::get_or_compute(&*client).expect("slot duration available");

		let inherent_data_providers = InherentDataProviders::new();
		register_babe_inherent_data_provider(
			&inherent_data_providers, config.get()
		).expect("Registers babe inherent data provider");

		#[allow(deprecated)]
		let select_chain = LongestChain::new(client.backend().clone());

		runtime.spawn(start_babe(BabeParams {
			config,
			block_import: client.clone(),
			select_chain,
			client,
			env: environ,
			sync_oracle: DummyOracle,
			inherent_data_providers,
			force_authoring: false,
			time_source: Default::default(),
			keystore,
		}).expect("Starts babe"));
	}

	runtime.spawn(futures01::future::poll_fn(move || {
		net.lock().poll();
		Ok::<_, ()>(futures01::Async::NotReady::<()>)
	}));

	runtime.block_on(future::join_all(import_notifications)
		.map(|_| Ok::<(), ()>(())).compat()).unwrap();
}

#[test]
fn authoring_blocks() { run_one_test() }

#[test]
#[should_panic]
fn rejects_missing_inherent_digest() {
	MUTATOR.with(|s| *s.borrow_mut() = Arc::new(move |header: &mut TestHeader| {
		let v = std::mem::replace(&mut header.digest_mut().logs, vec![]);
		header.digest_mut().logs = v.into_iter()
			.filter(|v| v.as_babe_pre_digest().is_none())
			.collect()
	}));
	run_one_test()
}

#[test]
#[should_panic]
fn rejects_missing_seals() {
	MUTATOR.with(|s| *s.borrow_mut() = Arc::new(move |header: &mut TestHeader| {
		let v = std::mem::replace(&mut header.digest_mut().logs, vec![]);
		header.digest_mut().logs = v.into_iter()
			.filter(|v| v.as_babe_seal().is_none())
			.collect()
	}));
	run_one_test()
}

// TODO: this test assumes that the test runtime will trigger epoch changes
// which isn't the case since it doesn't include the session module.
#[test]
#[should_panic]
#[ignore]
fn rejects_missing_consensus_digests() {
	MUTATOR.with(|s| *s.borrow_mut() = Arc::new(move |header: &mut TestHeader| {
		let v = std::mem::replace(&mut header.digest_mut().logs, vec![]);
		header.digest_mut().logs = v.into_iter()
			.filter(|v| v.as_babe_epoch().is_none())
			.collect()
	}));
	run_one_test()
}

#[test]
fn wrong_consensus_engine_id_rejected() {
	let _ = env_logger::try_init();
	let sig = AuthorityPair::generate().0.sign(b"");
	let bad_seal: Item = DigestItem::Seal([0; 4], sig.to_vec());
	assert!(bad_seal.as_babe_pre_digest().is_none());
	assert!(bad_seal.as_babe_seal().is_none())
}

#[test]
fn malformed_pre_digest_rejected() {
	let _ = env_logger::try_init();
	let bad_seal: Item = DigestItem::Seal(BABE_ENGINE_ID, [0; 64].to_vec());
	assert!(bad_seal.as_babe_pre_digest().is_none());
}

#[test]
fn sig_is_not_pre_digest() {
	let _ = env_logger::try_init();
	let sig = AuthorityPair::generate().0.sign(b"");
	let bad_seal: Item = DigestItem::Seal(BABE_ENGINE_ID, sig.to_vec());
	assert!(bad_seal.as_babe_pre_digest().is_none());
	assert!(bad_seal.as_babe_seal().is_some())
}

#[test]
fn can_author_block() {
	let _ = env_logger::try_init();
	let keystore_path = tempfile::tempdir().expect("Creates keystore path");
	let keystore = keystore::Store::open(keystore_path.path(), None).expect("Creates keystore");
	let pair = keystore.write().insert_ephemeral_from_seed::<AuthorityPair>("//Alice")
		.expect("Generates authority pair");

	let mut i = 0;
	let mut epoch = Epoch {
		start_slot: 0,
		authorities: vec![(pair.public(), 1)],
		randomness: [0; 32],
		epoch_index: 1,
		duration: 100,
		secondary_slots: true,
	};

	let parent_weight = 0;

	// with secondary slots enabled it should never be empty
	match claim_slot(i, parent_weight, &epoch, (3, 10), &keystore) {
		None => i += 1,
		Some(s) => debug!(target: "babe", "Authored block {:?}", s.0),
	}

	// otherwise with only vrf-based primary slots we might need to try a couple
	// of times.
	epoch.secondary_slots = false;
	loop {
		match claim_slot(i, parent_weight, &epoch, (3, 10), &keystore) {
			None => i += 1,
			Some(s) => {
				debug!(target: "babe", "Authored block {:?}", s.0);
				break;
			}
		}
	}
}

#[test]
fn authorities_call_works() {
	let _ = env_logger::try_init();
	let client = test_client::new();

	assert_eq!(client.info().chain.best_number, 0);
	assert_eq!(epoch(&client, &BlockId::Number(0)).unwrap().authorities, vec![
		(Keyring::Alice.public().into(), 1),
		(Keyring::Bob.public().into(), 1),
		(Keyring::Charlie.public().into(), 1),
	]);
}
