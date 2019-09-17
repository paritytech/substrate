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
use client::block_builder::BlockBuilder;
use consensus_common::NoNetwork as DummyOracle;
use consensus_common::import_queue::{
	BoxBlockImport, BoxJustificationImport, BoxFinalityProofImport,
};
use network::test::*;
use network::test::{Block as TestBlock, PeersClient};
use network::config::BoxFinalityProofRequestBuilder;
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
	peers: Vec<Peer<Option<PeerData>, DummySpecialization>>,
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

pub struct PeerData {
	link: BabeLink<TestBlock>,
	inherent_data_providers: InherentDataProviders,
	block_import: Mutex<Option<BoxBlockImport<TestBlock>>>,
}

impl TestNetFactory for BabeTestNet {
	type Specialization = DummySpecialization;
	type Verifier = TestVerifier;
	type PeerData = Option<PeerData>;

	/// Create new test network with peers and given config.
	fn from_config(_config: &ProtocolConfig) -> Self {
		debug!(target: "babe", "Creating test network from config");
		BabeTestNet {
			peers: Vec::new(),
		}
	}

	fn make_block_import(&self, client: PeersClient)
		-> (
			BoxBlockImport<Block>,
			Option<BoxJustificationImport<Block>>,
			Option<BoxFinalityProofImport<Block>>,
			Option<BoxFinalityProofRequestBuilder<Block>>,
			Option<PeerData>,
		)
	{
		let client = client.as_full().expect("only full clients are tested");
		let inherent_data_providers = InherentDataProviders::new();

		let config = Config::get_or_compute(&*client).expect("config available");
		let (block_import, link) = crate::block_import(
			config,
			client.clone(),
			client.clone(),
			client.clone(),
		).expect("can initialize block-import");

		let data_block_import = Mutex::new(Some(Box::new(block_import.clone()) as BoxBlockImport<_>));
		(
			Box::new(block_import),
			None,
			None,
			None,
			Some(PeerData { link, inherent_data_providers, block_import: data_block_import }),
		)
	}

	/// KLUDGE: this function gets the mutator from thread-local storage.
	fn make_verifier(
		&self,
		client: PeersClient,
		_cfg: &ProtocolConfig,
		maybe_link: &Option<PeerData>,
	)
		-> Self::Verifier
	{
		let client = client.as_full().expect("only full clients are used in test");
		trace!(target: "babe", "Creating a verifier");

		// ensure block import and verifier are linked correctly.
		let data = maybe_link.as_ref().expect("babe link always provided to verifier instantiation");

		TestVerifier {
			inner: BabeVerifier {
				client: client.clone(),
				api: client,
				inherent_data_providers: data.inherent_data_providers.clone(),
				config: data.link.config.clone(),
				epoch_changes: data.link.epoch_changes.clone(),
				time_source: data.link.time_source.clone(),
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
		let mut net = net.lock();
		let peer = net.peer(*peer_id);
		let client = peer.client().as_full().expect("Only full clients are used in tests").clone();
		let select_chain = peer.select_chain().expect("Full client has select_chain");

		let keystore_path = tempfile::tempdir().expect("Creates keystore path");
		let keystore = keystore::Store::open(keystore_path.path(), None).expect("Creates keystore");
		keystore.write().insert_ephemeral_from_seed::<AuthorityPair>(seed).expect("Generates authority key");
		keystore_paths.push(keystore_path);

		let mut got_own = false;
		let mut got_other = false;

		let environ = DummyFactory(client.clone());
		import_notifications.push(
			// run each future until we get one of our own blocks with number higher than 5
			// that was produced locally.
			client.import_notification_stream()
				.take_while(move |n| future::ready(n.header.number() < &5 || {
					if n.origin == BlockOrigin::Own {
						got_own = true;
					} else {
						got_other = true;
					}

					println!("got_own={} got_other={}", got_own, got_other);

					// continue until we have at least one block of our own
					// and one of another peer.
					!(got_own && got_other)
				}))
				.for_each(|_| future::ready(()) )
		);

		let data = peer.data.as_ref().expect("babe link set up during initialization");

		runtime.spawn(start_babe(BabeParams {
			block_import: data.block_import.lock().take().expect("import set up during init"),
			select_chain,
			client,
			env: environ,
			sync_oracle: DummyOracle,
			inherent_data_providers: data.inherent_data_providers.clone(),
			force_authoring: false,
			babe_link: data.link.clone(),
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
fn authoring_blocks() {
	env_logger::try_init().unwrap();
	run_one_test()
}

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
			.filter(|v| v.as_next_epoch_descriptor().is_none())
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
	let epoch = Epoch {
		start_slot: 0,
		authorities: vec![(pair.public(), 1)],
		randomness: [0; 32],
		epoch_index: 1,
		duration: 100,
	};

	let mut config = crate::BabeConfiguration {
		slot_duration: 1000,
		epoch_length: 100,
		c: (3, 10),
		genesis_authorities: Vec::new(),
		randomness: [0; 32],
		secondary_slots: true,
	};

	// with secondary slots enabled it should never be empty
	match claim_slot(i, &epoch, &config, &keystore) {
		None => i += 1,
		Some(s) => debug!(target: "babe", "Authored block {:?}", s.0),
	}

	// otherwise with only vrf-based primary slots we might need to try a couple
	// of times.
	config.secondary_slots = false;
	loop {
		match claim_slot(i, &epoch, &config, &keystore) {
			None => i += 1,
			Some(s) => {
				debug!(target: "babe", "Authored block {:?}", s.0);
				break;
			}
		}
	}
}

// #[test]
// fn authorities_call_works() {
// 	let _ = env_logger::try_init();
// 	let client = test_client::new();

// 	assert_eq!(client.info().chain.best_number, 0);
// 	assert_eq!(epoch(&client, &BlockId::Number(0)).unwrap().into_regular().unwrap().authorities, vec![
// 		(Keyring::Alice.public().into(), 1),
// 		(Keyring::Bob.public().into(), 1),
// 		(Keyring::Charlie.public().into(), 1),
// 	]);
// }
