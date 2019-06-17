// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Tests and test helpers for GRANDPA.

use super::*;
use network::test::{Block, DummySpecialization, Hash, TestNetFactory, Peer, PeersClient};
use network::test::{PassThroughVerifier};
use network::config::{ProtocolConfig, Roles};
use network::consensus_gossip as network_gossip;
use parking_lot::Mutex;
use tokio::runtime::current_thread;
use keyring::ed25519::{Keyring as AuthorityKeyring};
use client::{
	error::Result,
	runtime_api::{Core, RuntimeVersion, ApiExt},
	LongestChain,
};
use test_client::{self, runtime::BlockNumber};
use consensus_common::{BlockOrigin, ForkChoiceStrategy, ImportedAux, ImportBlock, ImportResult};
use consensus_common::import_queue::{SharedBlockImport, SharedJustificationImport, SharedFinalityProofImport,
	SharedFinalityProofRequestBuilder,
};
use std::collections::{HashMap, HashSet};
use std::result;
use parity_codec::Decode;
use runtime_primitives::traits::{ApiRef, ProvideRuntimeApi, Header as HeaderT};
use runtime_primitives::generic::BlockId;
use substrate_primitives::{NativeOrEncoded, ExecutionContext};
use fg_primitives::AuthorityId;

use authorities::AuthoritySet;
use finality_proof::{FinalityProofProvider, AuthoritySetForFinalityProver, AuthoritySetForFinalityChecker};
use communication::GRANDPA_ENGINE_ID;
use consensus_changes::ConsensusChanges;

type PeerData =
	Mutex<
		Option<
			LinkHalf<
				test_client::Backend,
				test_client::Executor,
				Block,
				test_client::runtime::RuntimeApi,
				LongestChain<test_client::Backend, Block>
			>
		>
	>;
type GrandpaPeer = Peer<PeerData, DummySpecialization>;

struct GrandpaTestNet {
	peers: Vec<Arc<GrandpaPeer>>,
	test_config: TestApi,
	started: bool,
}

impl GrandpaTestNet {
	fn new(test_config: TestApi, n_peers: usize) -> Self {
		let mut net = GrandpaTestNet {
			peers: Vec::with_capacity(n_peers),
			started: false,
			test_config,
		};
		let config = Self::default_config();
		for _ in 0..n_peers {
			net.add_full_peer(&config);
		}
		net
	}
}

impl TestNetFactory for GrandpaTestNet {
	type Specialization = DummySpecialization;
	type Verifier = PassThroughVerifier;
	type PeerData = PeerData;

	/// Create new test network with peers and given config.
	fn from_config(_config: &ProtocolConfig) -> Self {
		GrandpaTestNet {
			peers: Vec::new(),
			test_config: Default::default(),
			started: false,
		}
	}

	fn default_config() -> ProtocolConfig {
		// the authority role ensures gossip hits all nodes here.
		ProtocolConfig {
			roles: Roles::AUTHORITY,
		}
	}

	fn make_verifier(&self, _client: PeersClient, _cfg: &ProtocolConfig)
		-> Arc<Self::Verifier>
	{
		Arc::new(PassThroughVerifier(false)) // use non-instant finality.
	}

	fn make_block_import(&self, client: PeersClient)
		-> (
			SharedBlockImport<Block>,
			Option<SharedJustificationImport<Block>>,
			Option<SharedFinalityProofImport<Block>>,
			Option<SharedFinalityProofRequestBuilder<Block>>,
			PeerData,
		)
	{
		match client {
			PeersClient::Full(ref client) => {
				#[allow(deprecated)]
				let select_chain = LongestChain::new(
					client.backend().clone()
				);
				let (import, link) = block_import(
					client.clone(),
					Arc::new(self.test_config.clone()),
					select_chain,
				).expect("Could not create block import for fresh peer.");
				let shared_import = Arc::new(import);
				(shared_import.clone(), Some(shared_import), None, None, Mutex::new(Some(link)))
			},
			PeersClient::Light(ref client) => {
				use crate::light_import::tests::light_block_import_without_justifications;

				let authorities_provider = Arc::new(self.test_config.clone());
				// forbid direct finalization using justification that cames with the block
				// => light clients will try to fetch finality proofs
				let import = light_block_import_without_justifications(
					client.clone(),
					authorities_provider,
					Arc::new(self.test_config.clone())
				).expect("Could not create block import for fresh peer.");
				let finality_proof_req_builder = import.0.create_finality_proof_request_builder();
				let shared_import = Arc::new(import);
				(shared_import.clone(), None, Some(shared_import), Some(finality_proof_req_builder), Mutex::new(None))
			},
		}
	}

	fn make_finality_proof_provider(
		&self,
		client: PeersClient
	) -> Option<Arc<dyn network::FinalityProofProvider<Block>>> {
		match client {
			PeersClient::Full(ref client) => {
				let authorities_provider = Arc::new(self.test_config.clone());
				Some(Arc::new(FinalityProofProvider::new(client.clone(), authorities_provider)))
			},
			PeersClient::Light(_) => None,
		}
	}

	fn uses_tokio(&self) -> bool {
		true
	}

	fn peer(&self, i: usize) -> &GrandpaPeer {
		&self.peers[i]
	}

	fn peers(&self) -> &Vec<Arc<GrandpaPeer>> {
		&self.peers
	}

	fn mut_peers<F: FnOnce(&mut Vec<Arc<GrandpaPeer>>)>(&mut self, closure: F) {
		closure(&mut self.peers);
	}

	fn started(&self) -> bool {
		self.started
	}

	fn set_started(&mut self, new: bool) {
		self.started = new;
	}
}

#[derive(Clone)]
struct MessageRouting {
	inner: Arc<Mutex<GrandpaTestNet>>,
	peer_id: usize,
}

impl MessageRouting {
	fn new(inner: Arc<Mutex<GrandpaTestNet>>, peer_id: usize,) -> Self {
		MessageRouting {
			inner,
			peer_id,
		}
	}
}

impl Network<Block> for MessageRouting {
	type In = Box<dyn Stream<Item=network_gossip::TopicNotification, Error=()> + Send>;

	/// Get a stream of messages for a specific gossip topic.
	fn messages_for(&self, topic: Hash) -> Self::In {
		let inner = self.inner.lock();
		let peer = inner.peer(self.peer_id);

		let messages = peer.consensus_gossip_messages_for(
			GRANDPA_ENGINE_ID,
			topic,
		);

		let messages = messages.map_err(
			move |_| panic!("Messages for topic {} dropped too early", topic)
		);

		Box::new(messages)
	}

	fn register_validator(&self, v: Arc<dyn network_gossip::Validator<Block>>) {
		let inner = self.inner.lock();
		let peer = inner.peer(self.peer_id);
		peer.with_gossip(move |gossip, context| {
			gossip.register_validator(context, GRANDPA_ENGINE_ID, v);
		});
	}

	fn gossip_message(&self, topic: Hash, data: Vec<u8>, force: bool) {
		let inner = self.inner.lock();
		inner.peer(self.peer_id).gossip_message(
			topic,
			GRANDPA_ENGINE_ID,
			data,
			force,
		);
	}

	fn send_message(&self, who: Vec<network::PeerId>, data: Vec<u8>) {
		let inner = self.inner.lock();
		let peer = inner.peer(self.peer_id);

		peer.with_gossip(move |gossip, ctx| for who in &who {
			gossip.send_message(
				ctx,
				who,
				network_gossip::ConsensusMessage {
					engine_id: GRANDPA_ENGINE_ID,
					data: data.clone(),
				}
			)
		})
	}

	fn register_gossip_message(&self, _topic: Hash, _data: Vec<u8>) {
		// NOTE: only required to restore previous state on startup
		//       not required for tests currently
	}

	fn report(&self, _who: network::PeerId, _cost_benefit: i32) {

	}

	fn announce(&self, _block: Hash) {

	}
}

#[derive(Clone)]
struct Exit;

impl Future for Exit {
	type Item = ();
	type Error = ();

	fn poll(&mut self) -> Poll<(), ()> {
		Ok(Async::NotReady)
	}
}

#[derive(Default, Clone)]
pub(crate) struct TestApi {
	genesis_authorities: Vec<(AuthorityId, u64)>,
	scheduled_changes: Arc<Mutex<HashMap<Hash, ScheduledChange<BlockNumber>>>>,
	forced_changes: Arc<Mutex<HashMap<Hash, (BlockNumber, ScheduledChange<BlockNumber>)>>>,
}

impl TestApi {
	pub fn new(genesis_authorities: Vec<(AuthorityId, u64)>) -> Self {
		TestApi {
			genesis_authorities,
			scheduled_changes: Arc::new(Mutex::new(HashMap::new())),
			forced_changes: Arc::new(Mutex::new(HashMap::new())),
		}
	}
}

pub(crate) struct RuntimeApi {
	inner: TestApi,
}

impl ProvideRuntimeApi for TestApi {
	type Api = RuntimeApi;

	fn runtime_api<'a>(&'a self) -> ApiRef<'a, Self::Api> {
		RuntimeApi { inner: self.clone() }.into()
	}
}

impl Core<Block> for RuntimeApi {
	fn Core_version_runtime_api_impl(
		&self,
		_: &BlockId<Block>,
		_: ExecutionContext,
		_: Option<()>,
		_: Vec<u8>,
	) -> Result<NativeOrEncoded<RuntimeVersion>> {
		unimplemented!("Not required for testing!")
	}

	fn Core_execute_block_runtime_api_impl(
		&self,
		_: &BlockId<Block>,
		_: ExecutionContext,
		_: Option<(Block)>,
		_: Vec<u8>,
	) -> Result<NativeOrEncoded<()>> {
		unimplemented!("Not required for testing!")
	}

	fn Core_initialize_block_runtime_api_impl(
		&self,
		_: &BlockId<Block>,
		_: ExecutionContext,
		_: Option<&<Block as BlockT>::Header>,
		_: Vec<u8>,
	) -> Result<NativeOrEncoded<()>> {
		unimplemented!("Not required for testing!")
	}
}

impl ApiExt<Block> for RuntimeApi {
	fn map_api_result<F: FnOnce(&Self) -> result::Result<R, E>, R, E>(
		&self,
		_: F
	) -> result::Result<R, E> {
		unimplemented!("Not required for testing!")
	}

	fn runtime_version_at(&self, _: &BlockId<Block>) -> Result<RuntimeVersion> {
		unimplemented!("Not required for testing!")
	}

	fn record_proof(&mut self) {
		unimplemented!("Not required for testing!")
	}

	fn extract_proof(&mut self) -> Option<Vec<Vec<u8>>> {
		unimplemented!("Not required for testing!")
	}
}

impl GrandpaApi<Block> for RuntimeApi {
	fn GrandpaApi_grandpa_authorities_runtime_api_impl(
		&self,
		_: &BlockId<Block>,
		_: ExecutionContext,
		_: Option<()>,
		_: Vec<u8>,
	) -> Result<NativeOrEncoded<Vec<(substrate_primitives::ed25519::Public, u64)>>> {
		Ok(self.inner.genesis_authorities.clone()).map(NativeOrEncoded::Native)
	}

	fn GrandpaApi_grandpa_pending_change_runtime_api_impl(
		&self,
		at: &BlockId<Block>,
		_: ExecutionContext,
		_: Option<(&DigestFor<Block>)>,
		_: Vec<u8>,
	) -> Result<NativeOrEncoded<Option<ScheduledChange<NumberFor<Block>>>>> {
		let parent_hash = match at {
			&BlockId::Hash(at) => at,
			_ => panic!("not requested by block hash!!"),
		};

		// we take only scheduled changes at given block number where there are no
		// extrinsics.
		Ok(self.inner.scheduled_changes.lock().get(&parent_hash).map(|c| c.clone())).map(NativeOrEncoded::Native)
	}

	fn GrandpaApi_grandpa_forced_change_runtime_api_impl(
		&self,
		at: &BlockId<Block>,
		_: ExecutionContext,
		_: Option<(&DigestFor<Block>)>,
		_: Vec<u8>,
	)
		-> Result<NativeOrEncoded<Option<(NumberFor<Block>, ScheduledChange<NumberFor<Block>>)>>> {
		let parent_hash = match at {
			&BlockId::Hash(at) => at,
			_ => panic!("not requested by block hash!!"),
		};

		// we take only scheduled changes at given block number where there are no
		// extrinsics.
		Ok(self.inner.forced_changes.lock().get(&parent_hash).map(|c| c.clone())).map(NativeOrEncoded::Native)
	}
}

impl AuthoritySetForFinalityProver<Block> for TestApi {
	fn authorities(&self, block: &BlockId<Block>) -> Result<Vec<(AuthorityId, u64)>> {
		let runtime_api = RuntimeApi { inner: self.clone() };
		runtime_api.GrandpaApi_grandpa_authorities_runtime_api_impl(block, ExecutionContext::Syncing, None, Vec::new())
			.map(|v| match v {
				NativeOrEncoded::Native(value) => value,
				_ => unreachable!("only providing native values"),
			})
	}

	fn prove_authorities(&self, block: &BlockId<Block>) -> Result<Vec<Vec<u8>>> {
		self.authorities(block).map(|auth| vec![auth.encode()])
	}
}

impl AuthoritySetForFinalityChecker<Block> for TestApi {
	fn check_authorities_proof(
		&self,
		_hash: <Block as BlockT>::Hash,
		_header: <Block as BlockT>::Header,
		proof: Vec<Vec<u8>>,
	) -> Result<Vec<(AuthorityId, u64)>> {
		Decode::decode(&mut &proof[0][..])
			.ok_or_else(|| unreachable!("incorrect value is passed as GRANDPA authorities proof"))
	}
}

const TEST_GOSSIP_DURATION: Duration = Duration::from_millis(500);
const TEST_ROUTING_INTERVAL: Duration = Duration::from_millis(50);

fn make_ids(keys: &[AuthorityKeyring]) -> Vec<(substrate_primitives::ed25519::Public, u64)> {
	keys.iter()
		.map(|key| AuthorityId::from_raw(key.to_raw_public()))
		.map(|id| (id, 1))
		.collect()
}

// run the voters to completion. provide a closure to be invoked after
// the voters are spawned but before blocking on them.
fn run_to_completion_with<F>(
	blocks: u64,
	net: Arc<Mutex<GrandpaTestNet>>,
	peers: &[AuthorityKeyring],
	with: F,
) -> u64 where
	F: FnOnce(current_thread::Handle) -> Option<Box<dyn Future<Item=(), Error=()>>>
{
	use parking_lot::RwLock;

	let mut wait_for = Vec::new();
	let mut runtime = current_thread::Runtime::new().unwrap();

	let highest_finalized = Arc::new(RwLock::new(0));

	if let Some(f) = (with)(runtime.handle()) {
		wait_for.push(f);
	};

	for (peer_id, key) in peers.iter().enumerate() {
		let highest_finalized = highest_finalized.clone();
		let (client, link) = {
			let net = net.lock();
			// temporary needed for some reason
			let link = net.peers[peer_id].data.lock().take().expect("link initialized at startup; qed");
			(
				net.peers[peer_id].client().clone(),
				link,
			)
		};

		wait_for.push(
			Box::new(
				client.finality_notification_stream()
					.take_while(move |n| {
						let mut highest_finalized = highest_finalized.write();
						if *n.header.number() > *highest_finalized {
							*highest_finalized = *n.header.number();
						}
						Ok(n.header.number() < &blocks)
					})
					.collect()
					.map(|_| ())
			)
		);

		fn assert_send<T: Send>(_: &T) { }

		let grandpa_params = GrandpaParams {
			config: Config {
				gossip_duration: TEST_GOSSIP_DURATION,
				justification_period: 32,
				local_key: Some(Arc::new(key.clone().into())),
				name: Some(format!("peer#{}", peer_id)),
			},
			link: link,
			network: MessageRouting::new(net.clone(), peer_id),
			inherent_data_providers: InherentDataProviders::new(),
			on_exit: Exit,
			telemetry_on_connect: None,
		};
		let voter = run_grandpa_voter(grandpa_params).expect("all in order with client and network");

		assert_send(&voter);

		runtime.spawn(voter);
	}

	// wait for all finalized on each.
	let wait_for = ::futures::future::join_all(wait_for)
		.map(|_| ())
		.map_err(|_| ());

	let drive_to_completion = ::tokio::timer::Interval::new_interval(TEST_ROUTING_INTERVAL)
		.for_each(move |_| {
			net.lock().send_import_notifications();
			net.lock().send_finality_notifications();
			net.lock().sync_without_disconnects();
			Ok(())
		})
		.map(|_| ())
		.map_err(|_| ());

	let _ = runtime.block_on(wait_for.select(drive_to_completion).map_err(|_| ())).unwrap();

	let highest_finalized = *highest_finalized.read();
	highest_finalized
}

fn run_to_completion(blocks: u64, net: Arc<Mutex<GrandpaTestNet>>, peers: &[AuthorityKeyring]) -> u64 {
	run_to_completion_with(blocks, net, peers, |_| None)
}

#[test]
fn finalize_3_voters_no_observers() {
	let _ = env_logger::try_init();
	let peers = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob, AuthorityKeyring::Charlie];
	let voters = make_ids(peers);

	let mut net = GrandpaTestNet::new(TestApi::new(voters), 3);
	net.peer(0).push_blocks(20, false);
	net.sync();

	for i in 0..3 {
		assert_eq!(net.peer(i).client().info().chain.best_number, 20,
			"Peer #{} failed to sync", i);
	}

	let net = Arc::new(Mutex::new(net));
	run_to_completion(20, net.clone(), peers);

	// normally there's no justification for finalized blocks
	assert!(net.lock().peer(0).client().justification(&BlockId::Number(20)).unwrap().is_none(),
		"Extra justification for block#1");
}

#[test]
fn finalize_3_voters_1_full_observer() {
	let peers = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob, AuthorityKeyring::Charlie];
	let voters = make_ids(peers);

	let mut net = GrandpaTestNet::new(TestApi::new(voters), 4);
	net.peer(0).push_blocks(20, false);
	net.sync();

	let net = Arc::new(Mutex::new(net));
	let mut finality_notifications = Vec::new();

	let mut runtime = current_thread::Runtime::new().unwrap();
	let all_peers = peers.iter()
		.cloned()
		.map(|key| Some(Arc::new(key.into())))
		.chain(::std::iter::once(None));

	for (peer_id, local_key) in all_peers.enumerate() {
		let (client, link) = {
			let net = net.lock();
			let link = net.peers[peer_id].data.lock().take().expect("link initialized at startup; qed");
			(
				net.peers[peer_id].client().clone(),
				link,
			)
		};
		finality_notifications.push(
			client.finality_notification_stream()
				.take_while(|n| Ok(n.header.number() < &20))
				.for_each(move |_| Ok(()))
		);

		let grandpa_params = GrandpaParams {
			config: Config {
				gossip_duration: TEST_GOSSIP_DURATION,
				justification_period: 32,
				local_key,
				name: Some(format!("peer#{}", peer_id)),
			},
			link: link,
			network: MessageRouting::new(net.clone(), peer_id),
			inherent_data_providers: InherentDataProviders::new(),
			on_exit: Exit,
			telemetry_on_connect: None,
		};
		let voter = run_grandpa_voter(grandpa_params).expect("all in order with client and network");

		runtime.spawn(voter);
	}

	// wait for all finalized on each.
	let wait_for = ::futures::future::join_all(finality_notifications)
		.map(|_| ())
		.map_err(|_| ());

	let drive_to_completion = ::tokio::timer::Interval::new_interval(TEST_ROUTING_INTERVAL)
		.for_each(move |_| { net.lock().sync_without_disconnects(); Ok(()) })
		.map(|_| ())
		.map_err(|_| ());

	let _ = runtime.block_on(wait_for.select(drive_to_completion).map_err(|_| ())).unwrap();
}

#[test]
fn transition_3_voters_twice_1_full_observer() {
	let _ = env_logger::try_init();
	let peers_a = &[
		AuthorityKeyring::Alice,
		AuthorityKeyring::Bob,
		AuthorityKeyring::Charlie,
	];

	let peers_b = &[
		AuthorityKeyring::Dave,
		AuthorityKeyring::Eve,
		AuthorityKeyring::Ferdie,
	];

	let peers_c = &[
		AuthorityKeyring::Alice,
		AuthorityKeyring::Eve,
		AuthorityKeyring::Two,
	];

	let observer = &[AuthorityKeyring::One];

	let genesis_voters = make_ids(peers_a);

	let api = TestApi::new(genesis_voters);
	let transitions = api.scheduled_changes.clone();
	let net = Arc::new(Mutex::new(GrandpaTestNet::new(api, 8)));

	let mut runtime = current_thread::Runtime::new().unwrap();

	net.lock().peer(0).push_blocks(1, false);
	net.lock().sync();

	for (i, peer) in net.lock().peers().iter().enumerate() {
		let full_client = peer.client().as_full().expect("only full clients are used in test");
		assert_eq!(full_client.info().chain.best_number, 1,
					"Peer #{} failed to sync", i);

		let set: AuthoritySet<Hash, BlockNumber> = crate::aux_schema::load_authorities(
			#[allow(deprecated)]
			&**full_client.backend()
		).unwrap();

		assert_eq!(set.current(), (0, make_ids(peers_a).as_slice()));
		assert_eq!(set.pending_changes().count(), 0);
	}

	{
		let net = net.clone();
		let client = net.lock().peers[0].client().clone();
		let transitions = transitions.clone();
		let add_transition = move |parent_hash, change| {
			transitions.lock().insert(parent_hash, change);
		};
		let peers_c = peers_c.clone();

		// wait for blocks to be finalized before generating new ones
		let block_production = client.finality_notification_stream()
			.take_while(|n| Ok(n.header.number() < &30))
			.for_each(move |n| {
				match n.header.number() {
					1 => {
						// first 14 blocks.
						net.lock().peer(0).push_blocks(13, false);
					},
					14 => {
						// generate transition at block 15, applied at 20.
						net.lock().peer(0).generate_blocks(1, BlockOrigin::File, |builder| {
							let block = builder.bake().unwrap();
							add_transition(*block.header.parent_hash(), ScheduledChange {
								next_authorities: make_ids(peers_b),
								delay: 4,
							});

							block
						});
						net.lock().peer(0).push_blocks(5, false);
					},
					20 => {
						// at block 21 we do another transition, but this time instant.
						// add more until we have 30.
						net.lock().peer(0).generate_blocks(1, BlockOrigin::File, |builder| {
							let block = builder.bake().unwrap();
							add_transition(*block.header.parent_hash(), ScheduledChange {
								next_authorities: make_ids(&peers_c),
								delay: 0,
							});

							block
						});
						net.lock().peer(0).push_blocks(9, false);
					},
					_ => {},
				}

				Ok(())
			});

		runtime.spawn(block_production);
	}

	let mut finality_notifications = Vec::new();
	let all_peers = peers_a.iter()
		.chain(peers_b)
		.chain(peers_c)
		.chain(observer)
		.cloned()
		.collect::<HashSet<_>>() // deduplicate
		.into_iter()
		.map(|key| Some(Arc::new(key.into())))
		.enumerate();

	for (peer_id, local_key) in all_peers {
		let (client, link) = {
			let net = net.lock();
			let link = net.peers[peer_id].data.lock().take().expect("link initialized at startup; qed");
			(
				net.peers[peer_id].client().clone(),
				link,
			)
		};

		finality_notifications.push(
			client.finality_notification_stream()
				.take_while(|n| Ok(n.header.number() < &30))
				.for_each(move |_| Ok(()))
				.map(move |()| {
					let full_client = client.as_full().expect("only full clients are used in test");
					let set: AuthoritySet<Hash, BlockNumber> = crate::aux_schema::load_authorities(
						#[allow(deprecated)]
						&**full_client.backend()
					).unwrap();

					assert_eq!(set.current(), (2, make_ids(peers_c).as_slice()));
					assert_eq!(set.pending_changes().count(), 0);
				})
		);
		let grandpa_params = GrandpaParams {
			config: Config {
				gossip_duration: TEST_GOSSIP_DURATION,
				justification_period: 32,
				local_key,
				name: Some(format!("peer#{}", peer_id)),
			},
			link: link,
			network: MessageRouting::new(net.clone(), peer_id),
			inherent_data_providers: InherentDataProviders::new(),
			on_exit: Exit,
			telemetry_on_connect: None,
		};
		let voter = run_grandpa_voter(grandpa_params).expect("all in order with client and network");

		runtime.spawn(voter);
	}

	// wait for all finalized on each.
	let wait_for = ::futures::future::join_all(finality_notifications)
		.map(|_| ())
		.map_err(|_| ());

	let drive_to_completion = ::tokio::timer::Interval::new_interval(TEST_ROUTING_INTERVAL)
		.for_each(move |_| {
			net.lock().send_import_notifications();
			net.lock().send_finality_notifications();
			net.lock().sync_without_disconnects();
			Ok(())
		})
		.map(|_| ())
		.map_err(|_| ());

	let _ = runtime.block_on(wait_for.select(drive_to_completion).map_err(|_| ())).unwrap();
}

#[test]
fn justification_is_emitted_when_consensus_data_changes() {
	let peers = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob, AuthorityKeyring::Charlie];
	let mut net = GrandpaTestNet::new(TestApi::new(make_ids(peers)), 3);

	// import block#1 WITH consensus data change
	let new_authorities = vec![substrate_primitives::sr25519::Public::from_raw([42; 32])];
	net.peer(0).push_authorities_change_block(new_authorities);
	net.sync();
	let net = Arc::new(Mutex::new(net));
	run_to_completion(1, net.clone(), peers);

	// ... and check that there's justification for block#1
	assert!(net.lock().peer(0).client().justification(&BlockId::Number(1)).unwrap().is_some(),
		"Missing justification for block#1");
}

#[test]
fn justification_is_generated_periodically() {
	let peers = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob, AuthorityKeyring::Charlie];
	let voters = make_ids(peers);

	let mut net = GrandpaTestNet::new(TestApi::new(voters), 3);
	net.peer(0).push_blocks(32, false);
	net.sync();

	let net = Arc::new(Mutex::new(net));
	run_to_completion(32, net.clone(), peers);

	// when block#32 (justification_period) is finalized, justification
	// is required => generated
	for i in 0..3 {
		assert!(net.lock().peer(i).client().justification(&BlockId::Number(32)).unwrap().is_some());
	}
}

#[test]
fn consensus_changes_works() {
	let mut changes = ConsensusChanges::<H256, u64>::empty();

	// pending changes are not finalized
	changes.note_change((10, H256::from_low_u64_be(1)));
	assert_eq!(changes.finalize((5, H256::from_low_u64_be(5)), |_| Ok(None)).unwrap(), (false, false));

	// no change is selected from competing pending changes
	changes.note_change((1, H256::from_low_u64_be(1)));
	changes.note_change((1, H256::from_low_u64_be(101)));
	assert_eq!(changes.finalize((10, H256::from_low_u64_be(10)), |_| Ok(Some(H256::from_low_u64_be(1001)))).unwrap(), (true, false));

	// change is selected from competing pending changes
	changes.note_change((1, H256::from_low_u64_be(1)));
	changes.note_change((1, H256::from_low_u64_be(101)));
	assert_eq!(changes.finalize((10, H256::from_low_u64_be(10)), |_| Ok(Some(H256::from_low_u64_be(1)))).unwrap(), (true, true));
}

#[test]
fn sync_justifications_on_change_blocks() {
	let peers_a = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob, AuthorityKeyring::Charlie];
	let peers_b = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob];
	let voters = make_ids(peers_b);

	// 4 peers, 3 of them are authorities and participate in grandpa
	let api = TestApi::new(voters);
	let transitions = api.scheduled_changes.clone();
	let mut net = GrandpaTestNet::new(api, 4);

	// add 20 blocks
	net.peer(0).push_blocks(20, false);

	// at block 21 we do add a transition which is instant
	net.peer(0).generate_blocks(1, BlockOrigin::File, |builder| {
		let block = builder.bake().unwrap();
		transitions.lock().insert(*block.header.parent_hash(), ScheduledChange {
			next_authorities: make_ids(peers_b),
			delay: 0,
		});
		block
	});

	// add more blocks on top of it (until we have 25)
	net.peer(0).push_blocks(4, false);
	net.sync();

	for i in 0..4 {
		assert_eq!(net.peer(i).client().info().chain.best_number, 25,
			"Peer #{} failed to sync", i);
	}

	let net = Arc::new(Mutex::new(net));
	run_to_completion(25, net.clone(), peers_a);

	// the first 3 peers are grandpa voters and therefore have already finalized
	// block 21 and stored a justification
	for i in 0..3 {
		assert!(net.lock().peer(i).client().justification(&BlockId::Number(21)).unwrap().is_some());
	}

	// the last peer should get the justification by syncing from other peers
	while net.lock().peer(3).client().justification(&BlockId::Number(21)).unwrap().is_none() {
		net.lock().sync_without_disconnects();
	}
}

#[test]
fn finalizes_multiple_pending_changes_in_order() {
	let _ = env_logger::try_init();

	let peers_a = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob, AuthorityKeyring::Charlie];
	let peers_b = &[AuthorityKeyring::Dave, AuthorityKeyring::Eve, AuthorityKeyring::Ferdie];
	let peers_c = &[AuthorityKeyring::Dave, AuthorityKeyring::Alice, AuthorityKeyring::Bob];

	let all_peers = &[
		AuthorityKeyring::Alice, AuthorityKeyring::Bob, AuthorityKeyring::Charlie,
		AuthorityKeyring::Dave, AuthorityKeyring::Eve, AuthorityKeyring::Ferdie,
	];
	let genesis_voters = make_ids(peers_a);

	// 6 peers, 3 of them are authorities and participate in grandpa from genesis
	let api = TestApi::new(genesis_voters);
	let transitions = api.scheduled_changes.clone();
	let mut net = GrandpaTestNet::new(api, 6);

	// add 20 blocks
	net.peer(0).push_blocks(20, false);

	// at block 21 we do add a transition which is instant
	net.peer(0).generate_blocks(1, BlockOrigin::File, |builder| {
		let block = builder.bake().unwrap();
		transitions.lock().insert(*block.header.parent_hash(), ScheduledChange {
			next_authorities: make_ids(peers_b),
			delay: 0,
		});
		block
	});

	// add more blocks on top of it (until we have 25)
	net.peer(0).push_blocks(4, false);

	// at block 26 we add another which is enacted at block 30
	net.peer(0).generate_blocks(1, BlockOrigin::File, |builder| {
		let block = builder.bake().unwrap();
		transitions.lock().insert(*block.header.parent_hash(), ScheduledChange {
			next_authorities: make_ids(peers_c),
			delay: 4,
		});
		block
	});

	// add more blocks on top of it (until we have 30)
	net.peer(0).push_blocks(4, false);

	net.sync();

	// all peers imported both change blocks
	for i in 0..6 {
		assert_eq!(net.peer(i).client().info().chain.best_number, 30,
			"Peer #{} failed to sync", i);
	}

	let net = Arc::new(Mutex::new(net));
	run_to_completion(30, net.clone(), all_peers);
}

#[test]
fn doesnt_vote_on_the_tip_of_the_chain() {
	let peers_a = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob, AuthorityKeyring::Charlie];
	let voters = make_ids(peers_a);
	let api = TestApi::new(voters);
	let mut net = GrandpaTestNet::new(api, 3);

	// add 100 blocks
	net.peer(0).push_blocks(100, false);
	net.sync();

	for i in 0..3 {
		assert_eq!(net.peer(i).client().info().chain.best_number, 100,
			"Peer #{} failed to sync", i);
	}

	let net = Arc::new(Mutex::new(net));
	let highest = run_to_completion(75, net.clone(), peers_a);

	// the highest block to be finalized will be 3/4 deep in the unfinalized chain
	assert_eq!(highest, 75);
}

#[test]
fn force_change_to_new_set() {
	// two of these guys are offline.
	let genesis_authorities = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob, AuthorityKeyring::Charlie, AuthorityKeyring::One, AuthorityKeyring::Two];
	let peers_a = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob, AuthorityKeyring::Charlie];
	let api = TestApi::new(make_ids(genesis_authorities));

	let voters = make_ids(peers_a);
	let normal_transitions = api.scheduled_changes.clone();
	let forced_transitions = api.forced_changes.clone();
	let net = GrandpaTestNet::new(api, 3);
	let net = Arc::new(Mutex::new(net));

	let runner_net = net.clone();
	let add_blocks = move |_| {
		net.lock().peer(0).push_blocks(1, false);

		{
			// add a forced transition at block 12.
			let parent_hash = net.lock().peer(0).client().info().chain.best_hash;
			forced_transitions.lock().insert(parent_hash, (0, ScheduledChange {
				next_authorities: voters.clone(),
				delay: 10,
			}));

			// add a normal transition too to ensure that forced changes take priority.
			normal_transitions.lock().insert(parent_hash, ScheduledChange {
				next_authorities: make_ids(genesis_authorities),
				delay: 5,
			});
		}

		net.lock().peer(0).push_blocks(25, false);
		net.lock().sync();

		for (i, peer) in net.lock().peers().iter().enumerate() {
			assert_eq!(peer.client().info().chain.best_number, 26,
					"Peer #{} failed to sync", i);

			let full_client = peer.client().as_full().expect("only full clients are used in test");
			let set: AuthoritySet<Hash, BlockNumber> = crate::aux_schema::load_authorities(
				#[allow(deprecated)]
				&**full_client.backend()
			).unwrap();

			assert_eq!(set.current(), (1, voters.as_slice()));
			assert_eq!(set.pending_changes().count(), 0);
		}

		None
	};

	// it will only finalize if the forced transition happens.
	// we add_blocks after the voters are spawned because otherwise
	// the link-halfs have the wrong AuthoritySet
	run_to_completion_with(25, runner_net, peers_a, add_blocks);
}

#[test]
fn allows_reimporting_change_blocks() {
	let peers_a = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob, AuthorityKeyring::Charlie];
	let peers_b = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob];
	let voters = make_ids(peers_a);
	let api = TestApi::new(voters);
	let net = GrandpaTestNet::new(api.clone(), 3);

	let client = net.peer(0).client().clone();
	let (block_import, ..) = net.make_block_import(client.clone());

	let full_client = client.as_full().unwrap();
	let builder = full_client.new_block_at(&BlockId::Number(0), Default::default()).unwrap();
	let block = builder.bake().unwrap();
	api.scheduled_changes.lock().insert(*block.header.parent_hash(), ScheduledChange {
		next_authorities: make_ids(peers_b),
		delay: 0,
	});

	let block = || {
		let block = block.clone();
		ImportBlock {
			origin: BlockOrigin::File,
			header: block.header,
			justification: None,
			post_digests: Vec::new(),
			body: Some(block.extrinsics),
			finalized: false,
			auxiliary: Vec::new(),
			fork_choice: ForkChoiceStrategy::LongestChain,
		}
	};

	assert_eq!(
		block_import.import_block(block(), HashMap::new()).unwrap(),
		ImportResult::Imported(ImportedAux {
			needs_justification: true,
			clear_justification_requests: false,
			bad_justification: false,
			needs_finality_proof: false,
		}),
	);

	assert_eq!(
		block_import.import_block(block(), HashMap::new()).unwrap(),
		ImportResult::AlreadyInChain
	);
}

#[test]
fn test_bad_justification() {
	let peers_a = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob, AuthorityKeyring::Charlie];
	let peers_b = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob];
	let voters = make_ids(peers_a);
	let api = TestApi::new(voters);
	let net = GrandpaTestNet::new(api.clone(), 3);

	let client = net.peer(0).client().clone();
	let (block_import, ..) = net.make_block_import(client.clone());

	let full_client = client.as_full().expect("only full clients are used in test");
	let builder = full_client.new_block_at(&BlockId::Number(0), Default::default()).unwrap();
	let block = builder.bake().unwrap();
	api.scheduled_changes.lock().insert(*block.header.parent_hash(), ScheduledChange {
		next_authorities: make_ids(peers_b),
		delay: 0,
	});

	let block = || {
		let block = block.clone();
		ImportBlock {
			origin: BlockOrigin::File,
			header: block.header,
			justification: Some(Vec::new()),
			post_digests: Vec::new(),
			body: Some(block.extrinsics),
			finalized: false,
			auxiliary: Vec::new(),
			fork_choice: ForkChoiceStrategy::LongestChain,
		}
	};

	assert_eq!(
		block_import.import_block(block(), HashMap::new()).unwrap(),
		ImportResult::Imported(ImportedAux {
			needs_justification: true,
			clear_justification_requests: false,
			bad_justification: true,
			..Default::default()
		}),
	);

	assert_eq!(
		block_import.import_block(block(), HashMap::new()).unwrap(),
		ImportResult::AlreadyInChain
	);
}

#[test]
fn voter_persists_its_votes() {
	use std::iter::FromIterator;
	use std::sync::atomic::{AtomicUsize, Ordering};
	use futures::future;
	use futures::sync::mpsc;

	let _ = env_logger::try_init();

	// we have two authorities but we'll only be running the voter for alice
	// we are going to be listening for the prevotes it casts
	let peers = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob];
	let voters = make_ids(peers);

	// alice has a chain with 20 blocks
	let mut net = GrandpaTestNet::new(TestApi::new(voters.clone()), 2);
	net.peer(0).push_blocks(20, false);
	net.sync();

	assert_eq!(net.peer(0).client().info().chain.best_number, 20,
			   "Peer #{} failed to sync", 0);

	let mut runtime = current_thread::Runtime::new().unwrap();

	let client = net.peer(0).client().clone();
	let net = Arc::new(Mutex::new(net));

	let (voter_tx, voter_rx) = mpsc::unbounded::<()>();

	// startup a grandpa voter for alice but also listen for messages on a
	// channel. whenever a message is received the voter is restarted. when the
	// sender is dropped the voter is stopped.
	{
		let net = net.clone();

		let voter = future::loop_fn(voter_rx, move |rx| {
			let (_block_import, _, _, _, link) = net.lock().make_block_import(client.clone());
			let link = link.lock().take().unwrap();

			let grandpa_params = GrandpaParams {
				config: Config {
					gossip_duration: TEST_GOSSIP_DURATION,
					justification_period: 32,
					local_key: Some(Arc::new(peers[0].clone().into())),
					name: Some(format!("peer#{}", 0)),
				},
				link: link,
				network: MessageRouting::new(net.clone(), 0),
				inherent_data_providers: InherentDataProviders::new(),
				on_exit: Exit,
				telemetry_on_connect: None,
			};
			let mut voter = run_grandpa_voter(grandpa_params).expect("all in order with client and network");

			let voter = future::poll_fn(move || {
				// we need to keep the block_import alive since it owns the
				// sender for the voter commands channel, if that gets dropped
				// then the voter will stop
				let _block_import = _block_import.clone();
				voter.poll()
			});

			voter.select2(rx.into_future()).then(|res| match res {
				Ok(future::Either::A(x)) => {
					panic!("voter stopped unexpectedly: {:?}", x);
				},
				Ok(future::Either::B(((Some(()), rx), _))) => {
					Ok(future::Loop::Continue(rx))
				},
				Ok(future::Either::B(((None, _), _))) => {
					Ok(future::Loop::Break(()))
				},
				Err(future::Either::A(err)) => {
					panic!("unexpected error: {:?}", err);
				},
				Err(future::Either::B(..)) => {
					// voter_rx dropped, stop the voter.
					Ok(future::Loop::Break(()))
				},
			})
		});

		runtime.spawn(voter);
	}

	let (exit_tx, exit_rx) = futures::sync::oneshot::channel::<()>();

	// create the communication layer for bob, but don't start any
	// voter. instead we'll listen for the prevote that alice casts
	// and cast our own manually
	{
		let config = Config {
			gossip_duration: TEST_GOSSIP_DURATION,
			justification_period: 32,
			local_key: Some(Arc::new(peers[1].clone().into())),
			name: Some(format!("peer#{}", 1)),
		};
		let routing = MessageRouting::new(net.clone(), 1);
		let (network, routing_work) = communication::NetworkBridge::new(
			routing,
			config.clone(),
			None,
			Exit,
		);
		runtime.block_on(routing_work).unwrap();

		let (round_rx, round_tx) = network.round_communication(
			communication::Round(1),
			communication::SetId(0),
			Arc::new(VoterSet::from_iter(voters)),
			Some(config.local_key.unwrap()),
			HasVoted::No,
		);

		let round_tx = Arc::new(Mutex::new(round_tx));
		let exit_tx = Arc::new(Mutex::new(Some(exit_tx)));

		let net = net.clone();
		let state = AtomicUsize::new(0);

		runtime.spawn(round_rx.for_each(move |signed| {
			if state.compare_and_swap(0, 1, Ordering::SeqCst) == 0 {
				// the first message we receive should be a prevote from alice.
				let prevote = match signed.message {
					grandpa::Message::Prevote(prevote) => prevote,
					_ => panic!("voter should prevote."),
				};

				// its chain has 20 blocks and the voter targets 3/4 of the
				// unfinalized chain, so the vote should be for block 15
				assert!(prevote.target_number == 15);

				// we push 20 more blocks to alice's chain
				net.lock().peer(0).push_blocks(20, false);
				net.lock().sync();

				assert_eq!(net.lock().peer(0).client().info().chain.best_number, 40,
						   "Peer #{} failed to sync", 0);

				#[allow(deprecated)]
				let block_30_hash =
					net.lock().peer(0).client().as_full().unwrap().backend().blockchain().hash(30).unwrap().unwrap();

				// we restart alice's voter
				voter_tx.unbounded_send(()).unwrap();

				// and we push our own prevote for block 30
				let prevote = grandpa::Prevote {
					target_number: 30,
					target_hash: block_30_hash,
				};

				round_tx.lock().start_send(grandpa::Message::Prevote(prevote)).unwrap();

			} else if state.compare_and_swap(1, 2, Ordering::SeqCst) == 1 {
				// the next message we receive should be our own prevote
				let prevote = match signed.message {
					grandpa::Message::Prevote(prevote) => prevote,
					_ => panic!("We should receive our own prevote."),
				};

				// targeting block 30
				assert!(prevote.target_number == 30);

				// after alice restarts it should send its previous prevote
				// therefore we won't ever receive it again since it will be a
				// known message on the gossip layer

			} else if state.compare_and_swap(2, 3, Ordering::SeqCst) == 2 {
				// we then receive a precommit from alice for block 15
				// even though we casted a prevote for block 30
				let precommit = match signed.message {
					grandpa::Message::Precommit(precommit) => precommit,
					_ => panic!("voter should precommit."),
				};

				assert!(precommit.target_number == 15);

				// signal exit
				exit_tx.clone().lock().take().unwrap().send(()).unwrap();
			}

			Ok(())
		}).map_err(|_| ()));
	}

	let net = net.clone();
	let drive_to_completion = ::tokio::timer::Interval::new_interval(TEST_ROUTING_INTERVAL)
		.for_each(move |_| {
			net.lock().send_import_notifications();
			net.lock().send_finality_notifications();
			net.lock().sync_without_disconnects();
			Ok(())
		})
		.map(|_| ())
		.map_err(|_| ());

	let exit = exit_rx.into_future().map(|_| ()).map_err(|_| ());

	runtime.block_on(drive_to_completion.select(exit).map(|_| ()).map_err(|_| ())).unwrap();
}

#[test]
fn finalize_3_voters_1_light_observer() {
	let _ = env_logger::try_init();
	let authorities = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob, AuthorityKeyring::Charlie];
	let voters = make_ids(authorities);

	let mut net = GrandpaTestNet::new(TestApi::new(voters), 4);
	net.peer(0).push_blocks(20, false);
	net.sync();

	for i in 0..4 {
		assert_eq!(net.peer(i).client().info().chain.best_number, 20,
			"Peer #{} failed to sync", i);
	}

	let net = Arc::new(Mutex::new(net));
	let link = net.lock().peer(3).data.lock().take().expect("link initialized on startup; qed");

	let finality_notifications = net.lock().peer(3).client().finality_notification_stream()
		.take_while(|n| Ok(n.header.number() < &20))
		.collect();

	run_to_completion_with(20, net.clone(), authorities, |executor| {
		executor.spawn(
			run_grandpa_observer(
				Config {
					gossip_duration: TEST_GOSSIP_DURATION,
					justification_period: 32,
					local_key: None,
					name: Some("observer".to_string()),
				},
				link,
				MessageRouting::new(net.clone(), 3),
				Exit,
			).unwrap()
		).unwrap();

		Some(Box::new(finality_notifications.map(|_| ())))
	});
}

#[test]
fn finality_proof_is_fetched_by_light_client_when_consensus_data_changes() {
	let _ = ::env_logger::try_init();

	let peers = &[AuthorityKeyring::Alice];
	let mut net = GrandpaTestNet::new(TestApi::new(make_ids(peers)), 1);
	net.add_light_peer(&GrandpaTestNet::default_config());

	// import block#1 WITH consensus data change. Light client ignores justification
	// && instead fetches finality proof for block #1
	net.peer(0).push_authorities_change_block(vec![substrate_primitives::sr25519::Public::from_raw([42; 32])]);
	let net = Arc::new(Mutex::new(net));
	run_to_completion(1, net.clone(), peers);
	net.lock().sync_without_disconnects();

	// check that the block#1 is finalized on light client
	while net.lock().peer(1).client().info().chain.finalized_number != 1 {
		net.lock().tick_peer(1);
		net.lock().sync_without_disconnects();
	}
}

#[test]
fn empty_finality_proof_is_returned_to_light_client_when_authority_set_is_different() {
	// for debug: to ensure that without forced change light client will sync finality proof
	const FORCE_CHANGE: bool = true;

	let _ = ::env_logger::try_init();

	// two of these guys are offline.
	let genesis_authorities = if FORCE_CHANGE {
		vec![
			AuthorityKeyring::Alice,
			AuthorityKeyring::Bob,
			AuthorityKeyring::Charlie,
			AuthorityKeyring::One,
			AuthorityKeyring::Two,
		]
	} else {
		vec![
			AuthorityKeyring::Alice,
			AuthorityKeyring::Bob,
			AuthorityKeyring::Charlie,
		]
	};
	let peers_a = &[AuthorityKeyring::Alice, AuthorityKeyring::Bob, AuthorityKeyring::Charlie];
	let api = TestApi::new(make_ids(&genesis_authorities));

	let voters = make_ids(peers_a);
	let forced_transitions = api.forced_changes.clone();
	let net = GrandpaTestNet::new(api, 3);
	let net = Arc::new(Mutex::new(net));

	let runner_net = net.clone();
	let add_blocks = move |_| {
		net.lock().peer(0).push_blocks(1, false); // best is #1

		// add a forced transition at block 5.
		if FORCE_CHANGE {
			let parent_hash = net.lock().peer(0).client().info().chain.best_hash;
			forced_transitions.lock().insert(parent_hash, (0, ScheduledChange {
				next_authorities: voters.clone(),
				delay: 3,
			}));
		}

		// ensure block#10 enacts authorities set change => justification is generated
		// normally it will reach light client, but because of the forced change, it will not
		net.lock().peer(0).push_blocks(8, false); // best is #9
		net.lock().peer(0).push_authorities_change_block(
			vec![substrate_primitives::sr25519::Public::from_raw([42; 32])]
		); // #10
		net.lock().peer(0).push_blocks(1, false); // best is #11
		net.lock().sync_without_disconnects();

		None
	};

	// finalize block #11 on full clients
	run_to_completion_with(11, runner_net.clone(), peers_a, add_blocks);
	// request finalization by light client
	runner_net.lock().add_light_peer(&GrandpaTestNet::default_config());
	runner_net.lock().sync_without_disconnects();

	// check block, finalized on light client
	assert_eq!(
		runner_net.lock().peer(3).client().info().chain.finalized_number,
		if FORCE_CHANGE { 0 } else { 10 },
	);
}
