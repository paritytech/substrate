use super::*;
use network::test::{Block, Hash, TestNetFactory, Peer, PeersClient};
use network::import_queue::{PassThroughVerifier};
use network::ProtocolConfig;
use parking_lot::Mutex;
use tokio::runtime::current_thread;
use keyring::Keyring;
use client::BlockchainEvents;
use test_client;

type PeerData = Mutex<Option<LinkHalf<test_client::Backend, test_client::Executor, Block>>>;
type GrandpaPeer = Peer<PassThroughVerifier, PeerData>;

struct GrandpaTestNet {
	peers: Vec<Arc<GrandpaPeer>>,
	started: bool
}

impl TestNetFactory for GrandpaTestNet {
	type Verifier = PassThroughVerifier;
	type PeerData = PeerData;

	/// Create new test network with peers and given config.
	fn from_config(_config: &ProtocolConfig) -> Self {
		GrandpaTestNet {
			peers: Vec::new(),
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
		let (import, link) = block_import(client).expect("Could not create block import for fresh peer.");
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

const TEST_GOSSIP_DURATION: Duration = Duration::from_millis(500);
const TEST_ROUTING_INTERVAL: Duration = Duration::from_millis(50);

#[test]
fn finalize_20_unanimous_3_peers() {
	let mut net = GrandpaTestNet::new(3);
	net.peer(0).push_blocks(20, false);
	net.sync();

	let net = Arc::new(Mutex::new(net));
	let peers = &[
		(0, Keyring::Alice),
		(1, Keyring::Bob),
		(2, Keyring::Charlie),
	];

	let voters: Vec<_> = peers.iter()
		.map(|&(_, ref key)| AuthorityId(key.to_raw_public()))
		.collect();

	let mut finality_notifications = Vec::new();

	let mut runtime = current_thread::Runtime::new().unwrap();
	for (peer_id, key) in peers {
		let (client, link) = {
			let mut net = net.lock();
			// temporary needed for some reason
			let link = net.peers[*peer_id].data.lock().take().expect("link initialized at startup; qed");
			(
				net.peers[*peer_id].client().clone(),
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
				local_key: Some(Arc::new(key.clone().into())),
			},
			link,
			MessageRouting::new(net.clone(), *peer_id),
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
fn observer_can_finalize() {
	let mut net = GrandpaTestNet::new(4);
	net.peer(0).push_blocks(20, false);
	net.sync();

	let net = Arc::new(Mutex::new(net));
	let peers = &[
		(0, Keyring::Alice),
		(1, Keyring::Bob),
		(2, Keyring::Charlie),
	];

	let voters: HashMap<_, _> = peers.iter()
		.map(|&(_, ref key)| (AuthorityId(key.to_raw_public()), 1))
		.collect();

	let mut finality_notifications = Vec::new();

	let mut runtime = current_thread::Runtime::new().unwrap();
	let all_peers = peers.iter()
		.cloned()
		.map(|(id, key)| (id, Some(Arc::new(key.into()))))
		.chain(::std::iter::once((3, None)));

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
