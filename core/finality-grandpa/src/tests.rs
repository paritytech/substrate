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
use network::test::{Block, Hash, TestNetFactory, Peer, PeersClient};
use network::test::{PassThroughVerifier};
use network::config::{ProtocolConfig, Roles};
use parking_lot::Mutex;
use tokio::runtime::current_thread;
use keyring::Keyring;
use client::{
	BlockchainEvents, error::Result,
	blockchain::Backend as BlockchainBackend,
	runtime_api::{Core, RuntimeVersion, ApiExt, ConstructRuntimeApi, CallRuntimeAt},
};
use test_client::{self, runtime::BlockNumber};
use codec::Decode;
use consensus_common::{BlockOrigin, Error as ConsensusError};
use std::{collections::HashSet, result};
use runtime_primitives::traits::{ApiRef, ProvideRuntimeApi, RuntimeApiInfo};
use runtime_primitives::generic::BlockId;

use authorities::AuthoritySet;

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
type GrandpaPeer = Peer<PassThroughVerifier, PeerData>;

struct GrandpaTestNet {
	peers: Vec<Arc<GrandpaPeer>>,
	test_config: TestApi,
	started: bool
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
	type Verifier = PassThroughVerifier;
	type PeerData = PeerData;

	/// Create new test network with peers and given config.
	fn from_config(_config: &ProtocolConfig) -> Self {
		GrandpaTestNet {
			peers: Vec::new(),
			test_config: Default::default(),
			started: false
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
		-> (Arc<BlockImport<Block,Error=ConsensusError> + Send + Sync>, PeerData)
	{
		let (import, link) = block_import(
			client,
			Arc::new(self.test_config.clone())
		).expect("Could not create block import for fresh peer.");
		(Arc::new(import), Mutex::new(Some(link)))
	}

	fn peer(&self, i: usize) -> &GrandpaPeer {
		&self.peers[i]
	}

	fn peers(&self) -> &Vec<Arc<GrandpaPeer>> {
		&self.peers
	}

	fn mut_peers<F: Fn(&mut Vec<Arc<GrandpaPeer>>)>(&mut self, closure: F) {
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

fn make_topic(round: u64, set_id: u64) -> Hash {
	let mut hash = Hash::default();
	round.using_encoded(|s| {
		let raw = hash.as_mut();
		raw[..8].copy_from_slice(s);
	});
	set_id.using_encoded(|s| {
		let raw = hash.as_mut();
		raw[8..16].copy_from_slice(s);
	});
	hash
}

fn make_commit_topic(set_id: u64) -> Hash {
	let mut hash = Hash::default();

	{
		let raw = hash.as_mut();
		raw[16..22].copy_from_slice(b"commit");
	}
	set_id.using_encoded(|s| {
		let raw = hash.as_mut();
		raw[24..].copy_from_slice(s);
	});

	hash
}

impl Network for MessageRouting {
	type In = Box<Stream<Item=Vec<u8>,Error=()> + Send>;

	fn messages_for(&self, round: u64, set_id: u64) -> Self::In {
		let inner = self.inner.lock();
		let peer = inner.peer(self.peer_id);
		let mut gossip = peer.consensus_gossip().write();
		let messages = peer.with_spec(move |_, _| {
			gossip.messages_for(make_topic(round, set_id))
		});

		let messages = messages.map_err(
			move |_| panic!("Messages for round {} dropped too early", round)
		);

		Box::new(messages)
	}

	fn send_message(&self, round: u64, set_id: u64, message: Vec<u8>) {
		let mut inner = self.inner.lock();
		inner.peer(self.peer_id).gossip_message(make_topic(round, set_id), message, false);
		inner.route_until_complete();
	}

	fn drop_messages(&self, round: u64, set_id: u64) {
		let topic = make_topic(round, set_id);
		let inner = self.inner.lock();
		let peer = inner.peer(self.peer_id);
		let mut gossip = peer.consensus_gossip().write();
		peer.with_spec(move |_, _| {
			gossip.collect_garbage(|t| t == &topic)
		});
	}

	fn commit_messages(&self, set_id: u64) -> Self::In {
		let inner = self.inner.lock();
		let peer = inner.peer(self.peer_id);
		let mut gossip = peer.consensus_gossip().write();
		let messages = peer.with_spec(move |_, _| {
			gossip.messages_for(make_commit_topic(set_id))
		});

		let messages = messages.map_err(
			move |_| panic!("Commit messages for set {} dropped too early", set_id)
		);

		Box::new(messages)
	}

	fn send_commit(&self, set_id: u64, message: Vec<u8>) {
		let mut inner = self.inner.lock();
		inner.peer(self.peer_id).gossip_message(make_commit_topic(set_id), message, true);
		inner.route_until_complete();
	}
}

#[derive(Default, Clone)]
struct TestApi {
	genesis_authorities: Vec<(Ed25519AuthorityId, u64)>,
	scheduled_changes: Arc<Mutex<HashMap<Hash, ScheduledChange<BlockNumber>>>>,
}

impl TestApi {
	fn new(genesis_authorities: Vec<(Ed25519AuthorityId, u64)>) -> Self {
		TestApi {
			genesis_authorities,
			scheduled_changes: Arc::new(Mutex::new(HashMap::new())),
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
	fn version(&self, _: &BlockId<Block>) -> Result<RuntimeVersion> {
		unimplemented!("Not required for testing!")
	}

	fn authorities(&self, _: &BlockId<Block>) -> Result<Vec<Ed25519AuthorityId>> {
		unimplemented!("Not required for testing!")
	}

	fn execute_block(&self, _: &BlockId<Block>, _: &Block) -> Result<()> {
		unimplemented!("Not required for testing!")
	}

	fn initialise_block(
		&self,
		_: &BlockId<Block>,
		_: &<Block as BlockT>::Header
	) -> Result<()> {
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

	fn has_api<A: RuntimeApiInfo + ?Sized>(&self, _: &BlockId<Block>) -> Result<bool> {
		unimplemented!("Not required for testing!")
	}
}

impl ConstructRuntimeApi<Block> for RuntimeApi {
	fn construct_runtime_api<'a, T: CallRuntimeAt<Block>>(_: &'a T) -> ApiRef<'a, Self> {
		unimplemented!("Not required for testing!")
	}
}

impl GrandpaApi<Block> for RuntimeApi {
	fn grandpa_authorities(
		&self,
		at: &BlockId<Block>
	) -> Result<Vec<(Ed25519AuthorityId, u64)>> {
		if at == &BlockId::Number(0) {
			Ok(self.inner.genesis_authorities.clone())
		} else {
			panic!("should generally only request genesis authorities")
		}
	}

	fn grandpa_pending_change(&self, at: &BlockId<Block>, _: &DigestFor<Block>)
		-> Result<Option<ScheduledChange<NumberFor<Block>>>>
	{
		let parent_hash = match at {
			&BlockId::Hash(at) => at,
			_ => panic!("not requested by block hash!!"),
		};

		// we take only scheduled changes at given block number where there are no
		// extrinsics.
		Ok(self.inner.scheduled_changes.lock().get(&parent_hash).map(|c| c.clone()))
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

fn run_to_completion(blocks: u64, net: Arc<Mutex<GrandpaTestNet>>, peers: &[Keyring]) {
	let mut finality_notifications = Vec::new();
	let mut runtime = current_thread::Runtime::new().unwrap();

	for (peer_id, key) in peers.iter().enumerate() {
		let (client, link) = {
			let mut net = net.lock();
			// temporary needed for some reason
			let link = net.peers[peer_id].data.lock().take().expect("link initialized at startup; qed");
			(
				net.peers[peer_id].client().clone(),
				link,
			)
		};
		finality_notifications.push(
			client.finality_notification_stream()
				.take_while(|n| Ok(n.header.number() < &blocks))
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
		.for_each(move |_| { net.lock().route_until_complete(); Ok(()) })
		.map(|_| ())
		.map_err(|_| ());

	runtime.block_on(wait_for.select(drive_to_completion).map_err(|_| ())).unwrap();
}

#[test]
fn finalize_3_voters_no_observers() {
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
			let mut net = net.lock();
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
			futures::empty(),
		).expect("all in order with client and network");

		runtime.spawn(voter);
	}

	// wait for all finalized on each.
	let wait_for = ::futures::future::join_all(finality_notifications)
		.map(|_| ())
		.map_err(|_| ());

	let drive_to_completion = ::tokio::timer::Interval::new_interval(TEST_ROUTING_INTERVAL)
		.for_each(move |_| { net.lock().route_until_complete(); Ok(()) })
		.map(|_| ())
		.map_err(|_| ());

	runtime.block_on(wait_for.select(drive_to_completion).map_err(|_| ())).unwrap();
}

#[test]
fn transition_3_voters_twice_1_observer() {
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

	let mut runtime = tokio::runtime::Runtime::new().unwrap();

	net.lock().peer(0).push_blocks(1, false);
	net.lock().sync();

	for (i, peer) in net.lock().peers().iter().enumerate() {
		assert_eq!(peer.client().info().unwrap().chain.best_number, 1,
				   "Peer #{} failed to sync", i);

		let set_raw = peer.client().backend().get_aux(::AUTHORITY_SET_KEY).unwrap().unwrap();
		let set = AuthoritySet::<Hash, BlockNumber>::decode(&mut &set_raw[..]).unwrap();

		assert_eq!(set.current(), (0, make_ids(peers_a).as_slice()));
		assert_eq!(set.pending_changes().len(), 0);
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
			let mut net = net.lock();
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
					let set_raw = client.backend().get_aux(::AUTHORITY_SET_KEY).unwrap().unwrap();
					let set = AuthoritySet::<Hash, BlockNumber>::decode(&mut &set_raw[..]).unwrap();

					assert_eq!(set.current(), (2, make_ids(peers_c).as_slice()));
					assert!(set.pending_changes().is_empty());
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
			net.lock().sync();
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
	changes.note_change((10, 1.into()));
	assert_eq!(changes.finalize((5, 5.into()), |_| Ok(None)).unwrap(), (false, false));

	// no change is selected from competing pending changes
	changes.note_change((1, 1.into()));
	changes.note_change((1, 101.into()));
	assert_eq!(changes.finalize((10, 10.into()), |_| Ok(Some(1001.into()))).unwrap(), (true, false));

	// change is selected from competing pending changes
	changes.note_change((1, 1.into()));
	changes.note_change((1, 101.into()));
	assert_eq!(changes.finalize((10, 10.into()), |_| Ok(Some(1.into()))).unwrap(), (true, true));
}