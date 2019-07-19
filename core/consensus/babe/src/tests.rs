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

use client::LongestChain;
use consensus_common::NoNetwork as DummyOracle;
use network::test::*;
use network::test::{Block as TestBlock, PeersClient};
use runtime_primitives::traits::{Block as BlockT, DigestFor};
use network::config::ProtocolConfig;
use tokio::runtime::current_thread;
use keyring::sr25519::Keyring;
use super::generic::DigestItem;
use client::BlockchainEvents;
use test_client;
use futures::Async;
use log::debug;
use std::time::Duration;
type Item = generic::DigestItem<Hash>;

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

	fn init(&self, parent_header: &<TestBlock as BlockT>::Header)
		-> Result<DummyProposer, Error>
	{
		Ok(DummyProposer(parent_header.number + 1, self.0.clone()))
	}
}

impl Proposer<TestBlock> for DummyProposer {
	type Error = Error;
	type Create = Result<TestBlock, Error>;

	fn propose(&self, _: InherentData, digests: DigestFor<TestBlock>, _: Duration) -> Result<TestBlock, Error> {
		self.1.new_block(digests).unwrap().bake().map_err(|e| e.into())
	}
}

pub struct BabeTestNet {
	peers: Vec<Peer<(), DummySpecialization>>,
}

fn make_importer() -> BoxBlockImport<Block> {
	drop(env_logger::try_init());
	let client = Arc::new(test_client::new());
	let verifier = self.make_verifier(PeersClient::Full(client.clone()), config);
	let (block_import, _justification_import, _finality_proof_import, _finality_proof_request_builder, _data)
		= self.make_block_import(PeersClient::Full(client.clone()));
	let block_import = BlockImportAdapter(Arc::new(Mutex::new(block_import)));
	Box::new(BabeBlockImport::new(client, SharedEpochChanges::new(), block_import))
}

impl TestNetFactory for BabeTestNet {
	type Specialization = DummySpecialization;
	type Verifier = BabeVerifier<PeersFullClient>;
	type PeerData = ();

	/// Create new test network with peers and given config.
	fn from_config(_config: &ProtocolConfig) -> Self {
		debug!(target: "babe", "Creating test network from config");
		BabeTestNet {
			peers: Vec::new(),
		}
	}

	fn make_verifier(&self, client: PeersClient, _cfg: &ProtocolConfig)
		-> Arc<Self::Verifier>
	{
		let api = client.as_full().expect("only full clients are used in test");
		trace!(target: "babe", "Creating a verifier");
		let config = Config::get_or_compute(&*api)
			.expect("slot duration available");
		let inherent_data_providers = InherentDataProviders::new();
		register_babe_inherent_data_provider(
			&inherent_data_providers,
			config.get()
		).expect("Registers babe inherent data provider");
		trace!(target: "babe", "Provider registered");

		Arc::new(BabeVerifier {
			api,
			inherent_data_providers,
			config,
			time_source: Default::default(),
		})
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
fn can_serialize_block() {
	drop(env_logger::try_init());
	assert!(BabePreDigest::decode(&mut &b""[..]).is_none());
}

#[test]
fn authoring_blocks() {
	drop(env_logger::try_init());
	debug!(target: "babe", "checkpoint 1");
	let net = BabeTestNet::new(3);
	debug!(target: "babe", "checkpoint 2");

	debug!(target: "babe", "checkpoint 3");

	let peers = &[
		(0, Keyring::Alice),
		(1, Keyring::Bob),
		(2, Keyring::Charlie),
	];

	let net = Arc::new(Mutex::new(net));
	let mut import_notifications = Vec::new();
	debug!(target: "babe", "checkpoint 4");
	let mut runtime = current_thread::Runtime::new().unwrap();
	for (peer_id, key) in peers {
		let client = net.lock().peer(*peer_id).client().as_full().unwrap();
		let environ = Arc::new(DummyFactory(client.clone()));
		import_notifications.push(
			client.import_notification_stream()
				.map(|v| Ok::<_, ()>(v)).compat()
				.take_while(|n| Ok(!(n.origin != BlockOrigin::Own && n.header.number() < &5)))
				.for_each(move |_| Ok(()))
		);

		let config = Config::get_or_compute(&*client)
			.expect("slot duration available");

		let inherent_data_providers = InherentDataProviders::new();
		register_babe_inherent_data_provider(
			&inherent_data_providers, config.get()
		).expect("Registers babe inherent data provider");


		#[allow(deprecated)]
		let select_chain = LongestChain::new(client.backend().clone());

		runtime.spawn(start_babe(BabeParams {
			config,
			local_key: Arc::new(key.clone().into()),
			block_import: client.clone(),
			select_chain,
			client,
			env: environ.clone(),
			sync_oracle: DummyOracle,
			inherent_data_providers,
			force_authoring: false,
			time_source: Default::default(),
		}).expect("Starts babe"));
	}
	debug!(target: "babe", "checkpoint 5");

	// wait for all finalized on each.
	let wait_for = ::futures::future::join_all(import_notifications)
		.map(drop)
		.map_err(drop);

	let drive_to_completion = futures::future::poll_fn(|| { net.lock().poll(); Ok(Async::NotReady) });
	let _ = runtime.block_on(wait_for.select(drive_to_completion).map_err(drop)).unwrap();
}

#[test]
fn wrong_consensus_engine_id_rejected() {
	drop(env_logger::try_init());
	let sig = sr25519::Pair::generate().0.sign(b"");
	let bad_seal: Item = DigestItem::Seal([0; 4], sig.0.to_vec());
	assert!(bad_seal.as_babe_pre_digest().is_none());
	assert!(bad_seal.as_babe_seal().is_none())
}

#[test]
fn malformed_pre_digest_rejected() {
	drop(env_logger::try_init());
	let bad_seal: Item = DigestItem::Seal(BABE_ENGINE_ID, [0; 64].to_vec());
	assert!(bad_seal.as_babe_pre_digest().is_none());
}

#[test]
fn sig_is_not_pre_digest() {
	drop(env_logger::try_init());
	let sig = sr25519::Pair::generate().0.sign(b"");
	let bad_seal: Item = DigestItem::Seal(BABE_ENGINE_ID, sig.0.to_vec());
	assert!(bad_seal.as_babe_pre_digest().is_none());
	assert!(bad_seal.as_babe_seal().is_some())
}

#[test]
fn can_author_block() {
	drop(env_logger::try_init());
	let randomness = &[];
	let (pair, _) = sr25519::Pair::generate();
	let mut i = 0;
	let epoch = Epoch {
		authorities: vec![(pair.public(), 0)],
		randomness: [0; 32],
		epoch_index: 1,
		duration: 100,
	};
	loop {
		match claim_slot(randomness, i, 0, epoch.clone(), &pair, u64::MAX / 10) {
			None => i += 1,
			Some(s) => {
				debug!(target: "babe", "Authored block {:?}", s);
				break
			}
		}
	}
}

#[test]
fn authorities_call_works() {
	drop(env_logger::try_init());
	let client = test_client::new();

	assert_eq!(client.info().chain.best_number, 0);
	assert_eq!(epoch(&client, &BlockId::Number(0)).unwrap().authorities, vec![
		(Keyring::Alice.into(), 0),
		(Keyring::Bob.into(), 0),
		(Keyring::Charlie.into(), 0),
	]);
}
