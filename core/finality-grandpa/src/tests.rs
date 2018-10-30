use super::*;
use network::test::{Block, Hash, TestNetFactory, Peer, PeersClient};
use network::import_queue::{PassThroughVerifier};
use network::ProtocolConfig;
use parking_lot::Mutex;
use tokio::runtime::current_thread;
use keyring::Keyring;
use client::BlockchainEvents;
use test_client::{self, runtime::BlockNumber};

type PeerData = Mutex<Option<LinkHalf<test_client::Backend, test_client::Executor, Block>>>;
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

	fn make_verifier(&self, _client: Arc<PeersClient>, _cfg: &ProtocolConfig)
		-> Arc<Self::Verifier>
	{
		Arc::new(PassThroughVerifier(false)) // use non-instant finality.
	}

	fn make_block_import(&self, client: Arc<PeersClient>)
		-> (Arc<BlockImport<Block,Error=ClientError> + Send + Sync>, PeerData)
	{
		let (import, link) = block_import(client, self.test_config.clone()).expect("Could not create block import for fresh peer.");
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

fn round_to_topic(round: u64) -> Hash {
	let mut hash = Hash::default();
	round.using_encoded(|s| {
		let raw = hash.as_mut();
		raw[..8].copy_from_slice(s);
	});
	hash
}

impl Network for MessageRouting {
	type In = Box<Stream<Item=Vec<u8>,Error=()>>;

	fn messages_for(&self, round: u64) -> Self::In {
		let messages = self.inner.lock().peer(self.peer_id)
			.with_spec(|spec, _| spec.gossip.messages_for(round_to_topic(round)));

		let messages = messages.map_err(
			move |_| panic!("Messages for round {} dropped too early", round)
		);

		Box::new(messages)
	}

	fn send_message(&self, round: u64, message: Vec<u8>) {
		let mut inner = self.inner.lock();
		inner.peer(self.peer_id).gossip_message(round_to_topic(round), message);
		inner.route();
	}

	fn drop_messages(&self, round: u64) {
		let topic = round_to_topic(round);
		self.inner.lock().peer(self.peer_id)
			.with_spec(|spec, _| spec.gossip.collect_garbage(|t| t == &topic));
	}
}

#[derive(Default, Clone)]
struct TestApi {
	genesis_authorities: Vec<(AuthorityId, u64)>,
	scheduled_changes: HashMap<BlockNumber, ScheduledChange<BlockNumber>>,
}

impl TestApi {
	fn new(genesis_authorities: Vec<(AuthorityId, u64)>) -> Self {
		TestApi {
			genesis_authorities,
			scheduled_changes: HashMap::new(),
		}
	}
}

impl ApiClient<Block> for TestApi {
	fn genesis_authorities(&self) -> Result<Vec<(AuthorityId, u64)>, ClientError> {
		Ok(self.genesis_authorities.clone())
	}

	fn scheduled_change(&self, header: &<Block as BlockT>::Header)
		-> Result<Option<ScheduledChange<NumberFor<Block>>>, ClientError>
	{
		// we take only scheduled changes at given block number where there are no
		// extrinsics.
		Ok(self.scheduled_changes.get(header.number()).map(|c| c.clone()))
	}
}

const TEST_GOSSIP_DURATION: Duration = Duration::from_millis(500);
const TEST_ROUTING_INTERVAL: Duration = Duration::from_millis(50);

#[test]
fn finalize_3_voters_no_observers() {
	let peers = &[Keyring::Alice, Keyring::Bob, Keyring::Charlie];
	let voters: Vec<_> = peers.iter()
		.map(|key| AuthorityId(key.to_raw_public()))
		.map(|id| (id, 1))
		.collect();

	let mut net = GrandpaTestNet::new(TestApi::new(voters), 3);
	net.peer(0).push_blocks(20, false);
	net.sync();

	for i in 0..3 {
		assert_eq!(net.peer(i).client().info().unwrap().chain.best_number, 20,
			"Peer #{} failed to sync", i);
	}

	let net = Arc::new(Mutex::new(net));

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
				.take_while(|n| Ok(n.header.number() < &20))
				.for_each(|_| Ok(()))
		);
		let voter = run_grandpa(
			Config {
				gossip_duration: TEST_GOSSIP_DURATION,
				local_key: Some(Arc::new(key.clone().into())),
			},
			link,
			MessageRouting::new(net.clone(), peer_id),
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
fn finalize_3_voters_1_observer() {
	let peers = &[Keyring::Alice, Keyring::Bob, Keyring::Charlie];
	let voters: Vec<_> = peers.iter()
		.map(|key| AuthorityId(key.to_raw_public()))
		.map(|id| (id, 1))
		.collect();

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
				local_key,
			},
			link,
			MessageRouting::new(net.clone(), peer_id),
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
