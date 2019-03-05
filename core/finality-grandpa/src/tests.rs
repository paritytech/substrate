// Copyright 2018 Parity Technologies (UK) Ltd.
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
use parking_lot::Mutex;
use tokio::runtime::current_thread;
use keyring::Keyring;
use client::{
	BlockchainEvents, error::Result,
	blockchain::Backend as BlockchainBackend,
	runtime_api::{Core, RuntimeVersion, ApiExt},
};
use test_client::{self, runtime::BlockNumber};
use consensus_common::{BlockOrigin, ForkChoiceStrategy, ImportedAux, ImportBlock, ImportResult};
use consensus_common::import_queue::{SharedBlockImport, SharedJustificationImport};
use std::collections::{HashMap, HashSet};
use std::result;
use runtime_primitives::traits::{ApiRef, ProvideRuntimeApi};
use runtime_primitives::generic::BlockId;
use runtime_primitives::ExecutionContext;
use substrate_primitives::NativeOrEncoded;

use authorities::AuthoritySet;
use consensus_changes::ConsensusChanges;

type PeerData =
	Mutex<
		Option<
			LinkHalf<
				test_client::Backend,
				test_client::Executor,
				Block,
				test_client::runtime::RuntimeApi,
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
			net.add_peer(&config);
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

	fn make_verifier(&self, _client: Arc<PeersClient>, _cfg: &ProtocolConfig)
		-> Arc<Self::Verifier>
	{
		Arc::new(PassThroughVerifier(false)) // use non-instant finality.
	}

	fn make_block_import(&self, client: Arc<PeersClient>)
		-> (SharedBlockImport<Block>, Option<SharedJustificationImport<Block>>, PeerData)
	{
		let (import, link) = block_import(
			client,
			Arc::new(self.test_config.clone())
		).expect("Could not create block import for fresh peer.");
		let shared_import = Arc::new(import);
		(shared_import.clone(), Some(shared_import), Mutex::new(Some(link)))
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
	validator: Arc<GossipValidator<Block>>,
}

impl MessageRouting {
	fn new(inner: Arc<Mutex<GrandpaTestNet>>, peer_id: usize,) -> Self {
		let validator = Arc::new(GossipValidator::new());
		let v = validator.clone();
		{
			let inner = inner.lock();
			let peer = inner.peer(peer_id);
			peer.with_gossip(move |gossip, _| {
				gossip.register_validator(GRANDPA_ENGINE_ID, v);
			});
		}
		MessageRouting {
			inner,
			peer_id,
			validator,
		}
	}

	fn drop_messages(&self, topic: Hash) {
		let inner = self.inner.lock();
		let peer = inner.peer(self.peer_id);
		peer.consensus_gossip_collect_garbage_for_topic(topic);
	}
}

fn make_topic(round: u64, set_id: u64) -> Hash {
	message_topic::<Block>(round, set_id)
}

fn make_commit_topic(set_id: u64) -> Hash {
	commit_topic::<Block>(set_id)
}

impl Network<Block> for MessageRouting {
	type In = Box<Stream<Item=Vec<u8>,Error=()> + Send>;

	fn messages_for(&self, round: u64, set_id: u64) -> Self::In {
		self.validator.note_round(round, set_id);
		let inner = self.inner.lock();
		let peer = inner.peer(self.peer_id);
		let messages = peer.consensus_gossip_messages_for(
			GRANDPA_ENGINE_ID,
			make_topic(round, set_id),
		);

		let messages = messages.map_err(
			move |_| panic!("Messages for round {} dropped too early", round)
		);

		Box::new(messages)
	}

	fn send_message(&self, round: u64, set_id: u64, message: Vec<u8>) {
		let inner = self.inner.lock();
		inner.peer(self.peer_id).gossip_message(make_topic(round, set_id), GRANDPA_ENGINE_ID, message);
	}

	fn drop_round_messages(&self, round: u64, set_id: u64) {
		self.validator.drop_round(round, set_id);
		let topic = make_topic(round, set_id);
		self.drop_messages(topic);
	}

	fn drop_set_messages(&self, set_id: u64) {
		self.validator.drop_set(set_id);
		let topic = make_commit_topic(set_id);
		self.drop_messages(topic);
	}

	fn commit_messages(&self, set_id: u64) -> Self::In {
		self.validator.note_set(set_id);
		let inner = self.inner.lock();
		let peer = inner.peer(self.peer_id);
        let messages = peer.consensus_gossip_messages_for(
			GRANDPA_ENGINE_ID,
			make_commit_topic(set_id),
		);

		let messages = messages.map_err(
			move |_| panic!("Commit messages for set {} dropped too early", set_id)
		);

		Box::new(messages)
	}

	fn send_commit(&self, _round: u64, set_id: u64, message: Vec<u8>) {
		let inner = self.inner.lock();
		inner.peer(self.peer_id).gossip_message(make_commit_topic(set_id), GRANDPA_ENGINE_ID, message);
	}

	fn announce(&self, _round: u64, _set_id: u64, _block: H256) {

	}
}

#[derive(Default, Clone)]
struct TestApi {
	genesis_authorities: Vec<(Ed25519AuthorityId, u64)>,
	scheduled_changes: Arc<Mutex<HashMap<Hash, ScheduledChange<BlockNumber>>>>,
	forced_changes: Arc<Mutex<HashMap<Hash, (BlockNumber, ScheduledChange<BlockNumber>)>>>,
}

impl TestApi {
	fn new(genesis_authorities: Vec<(Ed25519AuthorityId, u64)>) -> Self {
		TestApi {
			genesis_authorities,
			scheduled_changes: Arc::new(Mutex::new(HashMap::new())),
			forced_changes: Arc::new(Mutex::new(HashMap::new())),
		}
	}
}

struct RuntimeApi {
	inner: TestApi,
}

impl ProvideRuntimeApi for TestApi {
	type Api = RuntimeApi;

	fn runtime_api<'a>(&'a self) -> ApiRef<'a, Self::Api> {
		RuntimeApi { inner: self.clone() }.into()
	}
}

impl Core<Block> for RuntimeApi {
	fn version_runtime_api_impl(
		&self,
		_: &BlockId<Block>,
		_: ExecutionContext,
		_: Option<()>,
		_: Vec<u8>,
	) -> Result<NativeOrEncoded<RuntimeVersion>> {
		unimplemented!("Not required for testing!")
	}

	fn authorities_runtime_api_impl(
		&self,
		_: &BlockId<Block>,
		_: ExecutionContext,
		_: Option<()>,
		_: Vec<u8>,
	) -> Result<NativeOrEncoded<Vec<Ed25519AuthorityId>>> {
		unimplemented!("Not required for testing!")
	}

	fn execute_block_runtime_api_impl(
		&self,
		_: &BlockId<Block>,
		_: ExecutionContext,
		_: Option<(Block)>,
		_: Vec<u8>,
	) -> Result<NativeOrEncoded<()>> {
		unimplemented!("Not required for testing!")
	}

	fn initialise_block_runtime_api_impl(
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
}

impl GrandpaApi<Block> for RuntimeApi {
	fn grandpa_authorities_runtime_api_impl(
		&self,
		at: &BlockId<Block>,
		_: ExecutionContext,
		_: Option<()>,
		_: Vec<u8>,
	) -> Result<NativeOrEncoded<Vec<(Ed25519AuthorityId, u64)>>> {
		if at == &BlockId::Number(0) {
			Ok(self.inner.genesis_authorities.clone()).map(NativeOrEncoded::Native)
		} else {
			panic!("should generally only request genesis authorities")
		}
	}

	fn grandpa_pending_change_runtime_api_impl(
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

	fn grandpa_forced_change_runtime_api_impl(
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

const TEST_GOSSIP_DURATION: Duration = Duration::from_millis(500);
const TEST_ROUTING_INTERVAL: Duration = Duration::from_millis(50);

fn make_ids(keys: &[Keyring]) -> Vec<(Ed25519AuthorityId, u64)> {
	keys.iter()
		.map(|key| Ed25519AuthorityId(key.to_raw_public()))
		.map(|id| (id, 1))
		.collect()
}

// run the voters to completion. provide a closure to be invoked after
// the voters are spawned but before blocking on them.
fn run_to_completion_with<F: FnOnce()>(
	blocks: u64,
	net: Arc<Mutex<GrandpaTestNet>>,
	peers: &[Keyring],
	before_waiting: F,
) -> u64 {
	use parking_lot::RwLock;

	let mut finality_notifications = Vec::new();
	let mut runtime = current_thread::Runtime::new().unwrap();

	let highest_finalized = Arc::new(RwLock::new(0));

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
		finality_notifications.push(
			client.finality_notification_stream()
				.take_while(move |n| {
					let mut highest_finalized = highest_finalized.write();
					if *n.header.number() > *highest_finalized {
						*highest_finalized = *n.header.number();
					}
					Ok(n.header.number() < &blocks)
				})
				.for_each(|_| Ok(()))
		);
		fn assert_send<T: Send>(_: &T) { }

		let voter = run_grandpa(
			Config {
				gossip_duration: TEST_GOSSIP_DURATION,
				justification_period: 32,
				local_key: Some(Arc::new(key.clone().into())),
				name: Some(format!("peer#{}", peer_id)),
			},
			link,
			MessageRouting::new(net.clone(), peer_id),
			InherentDataProviders::new(),
			futures::empty(),
		).expect("all in order with client and network");

		assert_send(&voter);

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
			net.lock().route_fast();
			Ok(())
		})
		.map(|_| ())
		.map_err(|_| ());

	(before_waiting)();

	runtime.block_on(wait_for.select(drive_to_completion).map_err(|_| ())).unwrap();

	let highest_finalized = *highest_finalized.read();

	highest_finalized
}

fn run_to_completion(blocks: u64, net: Arc<Mutex<GrandpaTestNet>>, peers: &[Keyring]) -> u64 {
	run_to_completion_with(blocks, net, peers, || {})
}

#[test]
fn finalize_3_voters_no_observers() {
	let _ = env_logger::try_init();
	let peers = &[Keyring::Alice, Keyring::Bob, Keyring::Charlie];
	let voters = make_ids(peers);

	let mut net = GrandpaTestNet::new(TestApi::new(voters), 3);
	net.peer(0).push_blocks(20, false);
	net.sync();

	for i in 0..3 {
		assert_eq!(net.peer(i).client().info().unwrap().chain.best_number, 20,
			"Peer #{} failed to sync", i);
	}

	let net = Arc::new(Mutex::new(net));
	run_to_completion(20, net.clone(), peers);

	// normally there's no justification for finalized blocks
	assert!(net.lock().peer(0).client().backend().blockchain().justification(BlockId::Number(20)).unwrap().is_none(),
		"Extra justification for block#1");
}

#[test]
fn finalize_3_voters_1_observer() {
	let peers = &[Keyring::Alice, Keyring::Bob, Keyring::Charlie];
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
		let voter = run_grandpa(
			Config {
				gossip_duration: TEST_GOSSIP_DURATION,
				justification_period: 32,
				local_key,
				name: Some(format!("peer#{}", peer_id)),
			},
			link,
			MessageRouting::new(net.clone(), peer_id),
			InherentDataProviders::new(),
			futures::empty(),
		).expect("all in order with client and network");

		runtime.spawn(voter);
	}

	// wait for all finalized on each.
	let wait_for = ::futures::future::join_all(finality_notifications)
		.map(|_| ())
		.map_err(|_| ());

	let drive_to_completion = ::tokio::timer::Interval::new_interval(TEST_ROUTING_INTERVAL)
		.for_each(move |_| { net.lock().route_fast(); Ok(()) })
		.map(|_| ())
		.map_err(|_| ());

	runtime.block_on(wait_for.select(drive_to_completion).map_err(|_| ())).unwrap();
}

#[test]
fn transition_3_voters_twice_1_observer() {
	let _ = env_logger::try_init();
	let peers_a = &[
		Keyring::Alice,
		Keyring::Bob,
		Keyring::Charlie,
	];

	let peers_b = &[
		Keyring::Dave,
		Keyring::Eve,
		Keyring::Ferdie,
	];

	let peers_c = &[
		Keyring::Alice,
		Keyring::Eve,
		Keyring::Two,
	];

	let observer = &[Keyring::One];

	let genesis_voters = make_ids(peers_a);

	let api = TestApi::new(genesis_voters);
	let transitions = api.scheduled_changes.clone();
	let net = Arc::new(Mutex::new(GrandpaTestNet::new(api, 8)));

	let mut runtime = current_thread::Runtime::new().unwrap();

	net.lock().peer(0).push_blocks(1, false);
	net.lock().sync();

	for (i, peer) in net.lock().peers().iter().enumerate() {
		assert_eq!(peer.client().info().unwrap().chain.best_number, 1,
					"Peer #{} failed to sync", i);

		let set: AuthoritySet<Hash, BlockNumber> = crate::aux_schema::load_authorities(
			&**peer.client().backend()
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
					let set: AuthoritySet<Hash, BlockNumber> = crate::aux_schema::load_authorities(
						&**client.backend()
					).unwrap();

					assert_eq!(set.current(), (2, make_ids(peers_c).as_slice()));
					assert_eq!(set.pending_changes().count(), 0);
				})
		);
		let voter = run_grandpa(
			Config {
				gossip_duration: TEST_GOSSIP_DURATION,
				justification_period: 32,
				local_key,
				name: Some(format!("peer#{}", peer_id)),
			},
			link,
			MessageRouting::new(net.clone(), peer_id),
			InherentDataProviders::new(),
			futures::empty(),
		).expect("all in order with client and network");

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
			net.lock().route_fast();
			Ok(())
		})
		.map(|_| ())
		.map_err(|_| ());

	runtime.block_on(wait_for.select(drive_to_completion).map_err(|_| ())).unwrap();
}

#[test]
fn justification_is_emitted_when_consensus_data_changes() {
	let peers = &[Keyring::Alice, Keyring::Bob, Keyring::Charlie];
	let mut net = GrandpaTestNet::new(TestApi::new(make_ids(peers)), 3);

	// import block#1 WITH consensus data change
	let new_authorities = vec![Ed25519AuthorityId::from([42; 32])];
	net.peer(0).push_authorities_change_block(new_authorities);
	net.sync();
	let net = Arc::new(Mutex::new(net));
	run_to_completion(1, net.clone(), peers);

	// ... and check that there's no justification for block#1
	assert!(net.lock().peer(0).client().backend().blockchain().justification(BlockId::Number(1)).unwrap().is_some(),
		"Missing justification for block#1");
}

#[test]
fn justification_is_generated_periodically() {
	let peers = &[Keyring::Alice, Keyring::Bob, Keyring::Charlie];
	let voters = make_ids(peers);

	let mut net = GrandpaTestNet::new(TestApi::new(voters), 3);
	net.peer(0).push_blocks(32, false);
	net.sync();

	let net = Arc::new(Mutex::new(net));
	run_to_completion(32, net.clone(), peers);

	// when block#32 (justification_period) is finalized, justification
	// is required => generated
	for i in 0..3 {
		assert!(net.lock().peer(i).client().backend().blockchain()
			.justification(BlockId::Number(32)).unwrap().is_some());
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
	let peers_a = &[Keyring::Alice, Keyring::Bob, Keyring::Charlie];
	let peers_b = &[Keyring::Alice, Keyring::Bob];
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
		assert_eq!(net.peer(i).client().info().unwrap().chain.best_number, 25,
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
		net.lock().route_fast();
	}
}

#[test]
fn finalizes_multiple_pending_changes_in_order() {
	let _ = env_logger::try_init();

	let peers_a = &[Keyring::Alice, Keyring::Bob, Keyring::Charlie];
	let peers_b = &[Keyring::Dave, Keyring::Eve, Keyring::Ferdie];
	let peers_c = &[Keyring::Dave, Keyring::Alice, Keyring::Bob];

	let all_peers = &[
		Keyring::Alice, Keyring::Bob, Keyring::Charlie,
		Keyring::Dave, Keyring::Eve, Keyring::Ferdie,
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
		assert_eq!(net.peer(i).client().info().unwrap().chain.best_number, 30,
			"Peer #{} failed to sync", i);
	}

	let net = Arc::new(Mutex::new(net));
	run_to_completion(30, net.clone(), all_peers);
}

#[test]
fn doesnt_vote_on_the_tip_of_the_chain() {
	let peers_a = &[Keyring::Alice, Keyring::Bob, Keyring::Charlie];
	let voters = make_ids(peers_a);
	let api = TestApi::new(voters);
	let mut net = GrandpaTestNet::new(api, 3);

	// add 100 blocks
	net.peer(0).push_blocks(100, false);
	net.sync();

	for i in 0..3 {
		assert_eq!(net.peer(i).client().info().unwrap().chain.best_number, 100,
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
	let genesis_authorities = &[Keyring::Alice, Keyring::Bob, Keyring::Charlie, Keyring::One, Keyring::Two];
	let peers_a = &[Keyring::Alice, Keyring::Bob, Keyring::Charlie];
	let api = TestApi::new(make_ids(genesis_authorities));

	let voters = make_ids(peers_a);
	let normal_transitions = api.scheduled_changes.clone();
	let forced_transitions = api.forced_changes.clone();
	let net = GrandpaTestNet::new(api, 3);
	let net = Arc::new(Mutex::new(net));

	let runner_net = net.clone();
	let add_blocks = move || {
		net.lock().peer(0).push_blocks(1, false);

		{
			// add a forced transition at block 12.
			let parent_hash = net.lock().peer(0).client().info().unwrap().chain.best_hash;
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
			assert_eq!(peer.client().info().unwrap().chain.best_number, 26,
					"Peer #{} failed to sync", i);

			let set: AuthoritySet<Hash, BlockNumber> = crate::aux_schema::load_authorities(
				&**peer.client().backend()
			).unwrap();

			assert_eq!(set.current(), (1, voters.as_slice()));
			assert_eq!(set.pending_changes().count(), 0);
		}
	};

	// it will only finalize if the forced transition happens.
	// we add_blocks after the voters are spawned because otherwise
	// the link-halfs have the wrong AuthoritySet
	run_to_completion_with(25, runner_net, peers_a, add_blocks);
}

#[test]
fn allows_reimporting_change_blocks() {
	let peers_a = &[Keyring::Alice, Keyring::Bob, Keyring::Charlie];
	let peers_b = &[Keyring::Alice, Keyring::Bob];
	let voters = make_ids(peers_a);
	let api = TestApi::new(voters);
	let net = GrandpaTestNet::new(api.clone(), 3);

	let client = net.peer(0).client().clone();
	let (block_import, ..) = net.make_block_import(client.clone());

	let builder = client.new_block_at(&BlockId::Number(0)).unwrap();
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
		block_import.import_block(block(), None).unwrap(),
		ImportResult::Imported(ImportedAux { needs_justification: true, clear_justification_requests: false }),
	);

	assert_eq!(
		block_import.import_block(block(), None).unwrap(),
		ImportResult::AlreadyInChain
	);
}
