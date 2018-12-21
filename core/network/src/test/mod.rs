// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

#![allow(missing_docs)]

#[cfg(test)]
mod sync;

use std::collections::{VecDeque, HashSet, HashMap};
use std::sync::Arc;

use parking_lot::RwLock;
use client;
use client::error::Error as ClientError;
use client::block_builder::BlockBuilder;
use runtime_primitives::generic::BlockId;
use io::SyncIo;
use protocol::{Context, Protocol, ProtocolContext};
use config::ProtocolConfig;
use service::TransactionPool;
use network_libp2p::{NodeIndex, PeerId, Severity};
use keyring::Keyring;
use codec::Encode;
use import_queue::{SyncImportQueue, PassThroughVerifier, Verifier};
use consensus::BlockOrigin;
use specialization::NetworkSpecialization;
use consensus_gossip::ConsensusGossip;
use import_queue::{BlockImport, ImportQueue};
use service::ExecuteInContext;
use test_client;

pub use test_client::runtime::{Block, Hash, Transfer, Extrinsic};
pub use test_client::TestClient;

struct DummyContextExecutor(Arc<Protocol<Block, DummySpecialization, Hash>>, Arc<RwLock<VecDeque<TestPacket>>>);
unsafe impl Send for DummyContextExecutor {}
unsafe impl Sync for DummyContextExecutor {}

impl ExecuteInContext<Block> for DummyContextExecutor {
	fn execute_in_context<F: Fn(&mut Context<Block>)>(&self, closure: F) {
		let mut io = TestIo::new(&self.1, None);
		let mut context = ProtocolContext::new(&self.0.context_data(), &mut io);
		closure(&mut context);
	}
}

/// The test specialization.
pub struct DummySpecialization { }

impl NetworkSpecialization<Block> for DummySpecialization {
	fn status(&self) -> Vec<u8> { vec![] }

	fn on_connect(&mut self, _ctx: &mut Context<Block>, _peer_id: NodeIndex, _status: ::message::Status<Block>) {
	}

	fn on_disconnect(&mut self, _ctx: &mut Context<Block>, _peer_id: NodeIndex) {
	}

	fn on_message(
		&mut self,
		_ctx: &mut Context<Block>,
		_peer_id: NodeIndex,
		_message: &mut Option<::message::Message<Block>>
	) {
	}
}

pub struct TestIo<'p> {
	queue: &'p RwLock<VecDeque<TestPacket>>,
	pub to_disconnect: HashSet<NodeIndex>,
	packets: Vec<TestPacket>,
	_sender: Option<NodeIndex>,
}

impl<'p> TestIo<'p> where {
	pub fn new(queue: &'p RwLock<VecDeque<TestPacket>>, sender: Option<NodeIndex>) -> TestIo<'p> {
		TestIo {
			queue: queue,
			_sender: sender,
			to_disconnect: HashSet::new(),
			packets: Vec::new(),
		}
	}
}

impl<'p> Drop for TestIo<'p> {
	fn drop(&mut self) {
		self.queue.write().extend(self.packets.drain(..));
	}
}

impl<'p> SyncIo for TestIo<'p> {
	fn report_peer(&mut self, who: NodeIndex, _reason: Severity) {
		self.to_disconnect.insert(who);
	}

	fn send(&mut self, who: NodeIndex, data: Vec<u8>) {
		self.packets.push(TestPacket {
			data: data,
			recipient: who,
		});
	}

	fn peer_debug_info(&self, _who: NodeIndex) -> String {
		"unknown".to_string()
	}

	fn peer_id(&self, _peer_id: NodeIndex) -> Option<PeerId> {
		None
	}
}

/// Mocked subprotocol packet
pub struct TestPacket {
	data: Vec<u8>,
	recipient: NodeIndex,
}

pub type PeersClient = client::Client<test_client::Backend, test_client::Executor, Block, test_client::runtime::RuntimeApi>;

pub struct Peer<V: Verifier<Block>, D> {
	client: Arc<PeersClient>,
	pub sync: Arc<Protocol<Block, DummySpecialization, Hash>>,
	pub queue: Arc<RwLock<VecDeque<TestPacket>>>,
	import_queue: Arc<SyncImportQueue<Block, V>>,
	executor: Arc<DummyContextExecutor>,
	/// Some custom data set up at initialization time.
	pub data: D,
}

impl<V: 'static + Verifier<Block>, D> Peer<V, D> {
	fn new(
		client: Arc<PeersClient>,
		sync: Arc<Protocol<Block, DummySpecialization, Hash>>,
		queue: Arc<RwLock<VecDeque<TestPacket>>>,
		import_queue: Arc<SyncImportQueue<Block, V>>,
		data: D,
	) -> Self {
		let executor = Arc::new(DummyContextExecutor(sync.clone(), queue.clone()));
		Peer { client, sync, queue, import_queue, executor, data }
	}
	/// Called after blockchain has been populated to updated current state.
	fn start(&self) {
		// Update the sync state to the latest chain state.
		let info = self.client.info().expect("In-mem client does not fail");
		let header = self.client.header(&BlockId::Hash(info.chain.best_hash)).unwrap().unwrap();
		let network_link = ::import_queue::NetworkLink {
			sync: Arc::downgrade(self.sync.sync()),
			context: Arc::downgrade(&self.executor),
		};

		self.import_queue.start(network_link).expect("Test ImportQueue always starts");
		self.sync.on_block_imported(&mut TestIo::new(&self.queue, None), info.chain.best_hash, &header);
	}

	/// Called on connection to other indicated peer.
	fn on_connect(&self, other: NodeIndex) {
		self.sync.on_peer_connected(&mut TestIo::new(&self.queue, Some(other)), other);
	}

	pub fn consensus_gossip(&self) -> &RwLock<ConsensusGossip<Block>> {
		self.sync.consensus_gossip()
	}

	/// Called on disconnect from other indicated peer.
	fn on_disconnect(&self, other: NodeIndex) {
		let mut io = TestIo::new(&self.queue, Some(other));
		self.sync.on_peer_disconnected(&mut io, other);
	}

	/// Receive a message from another peer. Return a set of peers to disconnect.
	fn receive_message(&self, from: NodeIndex, msg: TestPacket) -> HashSet<NodeIndex> {
		let mut io = TestIo::new(&self.queue, Some(from));
		self.sync.handle_packet(&mut io, from, &msg.data);
		self.flush();
		io.to_disconnect.clone()
	}

	#[cfg(test)]
	fn with_io<'a, F, U>(&'a self, f: F) -> U where F: FnOnce(&mut TestIo<'a>) -> U {
		let mut io = TestIo::new(&self.queue, None);
		f(&mut io)
	}

	/// Produce the next pending message to send to another peer.
	fn pending_message(&self) -> Option<TestPacket> {
		self.flush();
		self.queue.write().pop_front()
	}

	/// Whether this peer is done syncing (has no messages to send).
	fn is_done(&self) -> bool {
		self.queue.read().is_empty()
	}

	/// Execute a "sync step". This is called for each peer after it sends a packet.
	fn sync_step(&self) {
		self.flush();
		self.sync.tick(&mut TestIo::new(&self.queue, None));
	}

	/// Send block import notifications.
	fn send_import_notifications(&self) {
		let info = self.client.info().expect("In-mem client does not fail");
		let header = self.client.header(&BlockId::Hash(info.chain.best_hash)).unwrap().unwrap();
		self.sync.on_block_imported(&mut TestIo::new(&self.queue, None), info.chain.best_hash, &header);
	}

	/// Restart sync for a peer.
	fn restart_sync(&self) {
		self.sync.abort();
	}

	fn flush(&self) {
	}

	/// Push a message into the gossip network and relay to peers.
	/// `TestNet::sync_step` needs to be called to ensure it's propagated.
	pub fn gossip_message(&self, topic: Hash, data: Vec<u8>, broadcast: bool) {
		self.sync.gossip_consensus_message(&mut TestIo::new(&self.queue, None), topic, data, broadcast);
	}

	/// Add blocks to the peer -- edit the block before adding
	pub fn generate_blocks<F>(&self, count: usize, origin: BlockOrigin, mut edit_block: F)
		where F: FnMut(BlockBuilder<Block, (), PeersClient>) -> Block
	{
		use blocks::BlockData;

		for _  in 0..count {
			let builder = self.client.new_block().unwrap();
			let block = edit_block(builder);
			let hash = block.header.hash();
			trace!("Generating {}, (#{}, parent={})", hash, block.header.number, block.header.parent_hash);
			let header = block.header.clone();

			// NOTE: if we use a non-synchronous queue in the test-net in the future,
			// this may not work.
		 	self.import_queue.import_blocks(origin, vec![BlockData {
				origin: None,
				block: ::message::BlockData::<Block> {
					hash,
					header: Some(header),
					body: Some(block.extrinsics),
					receipt: None,
					message_queue: None,
					justification: None,
				},
			}]);
		}

	}

	/// Push blocks to the peer (simplified: with or without a TX)
	pub fn push_blocks(&self, count: usize, with_tx: bool) {
		let mut nonce = 0;
		if with_tx {
			self.generate_blocks(count, BlockOrigin::File, |mut builder| {
				let transfer = Transfer {
					from: Keyring::Alice.to_raw_public().into(),
					to: Keyring::Alice.to_raw_public().into(),
					amount: 1,
					nonce,
				};
				let signature = Keyring::from_raw_public(transfer.from.to_fixed_bytes()).unwrap().sign(&transfer.encode()).into();
				builder.push(Extrinsic { transfer, signature }).unwrap();
				nonce = nonce + 1;
				builder.bake().unwrap()
			});
		} else {
			self.generate_blocks(count, BlockOrigin::File, |builder| builder.bake().unwrap());
		}
	}

	/// Execute a function with specialization for this peer.
	pub fn with_spec<F, U>(&self, f: F) -> U
		where F: FnOnce(&mut DummySpecialization, &mut Context<Block>) -> U
	{
		self.sync.with_spec(&mut TestIo::new(&self.queue, None), f)
	}

	/// Get a reference to the client.
	pub fn client(&self) -> &Arc<PeersClient> {
		&self.client
	}
}

pub struct EmptyTransactionPool;

impl TransactionPool<Hash, Block> for EmptyTransactionPool {
	fn transactions(&self) -> Vec<(Hash, Extrinsic)> {
		Vec::new()
	}

	fn import(&self, _transaction: &Extrinsic) -> Option<Hash> {
		None
	}

	fn on_broadcasted(&self, _: HashMap<Hash, Vec<String>>) {}
}

pub trait TestNetFactory: Sized {
	type Verifier: 'static + Verifier<Block>;
	type PeerData: Default;

	/// These two need to be implemented!
	fn from_config(config: &ProtocolConfig) -> Self;
	fn make_verifier(&self, client: Arc<PeersClient>, config: &ProtocolConfig) -> Arc<Self::Verifier>;


	/// Get reference to peer.
	fn peer(&self, i: usize) -> &Peer<Self::Verifier, Self::PeerData>;
	fn peers(&self) -> &Vec<Arc<Peer<Self::Verifier, Self::PeerData>>>;
	fn mut_peers<F: Fn(&mut Vec<Arc<Peer<Self::Verifier, Self::PeerData>>>)>(&mut self, closure: F);

	fn started(&self) -> bool;
	fn set_started(&mut self, now: bool);

	/// Get custom block import handle for fresh client, along with peer data.
	fn make_block_import(&self, client: Arc<PeersClient>)
		-> (Arc<BlockImport<Block,Error=ClientError> + Send + Sync>, Self::PeerData)
	{
		(client, Default::default())
	}

	fn default_config() -> ProtocolConfig {
		ProtocolConfig::default()
	}

	/// Create new test network with this many peers.
	fn new(n: usize) -> Self {
		let config = Self::default_config();
		let mut net = Self::from_config(&config);

		for _ in 0..n {
			net.add_peer(&config);
		}
		net
	}

	/// Add a peer.
	fn add_peer(&mut self, config: &ProtocolConfig) {
		let client = Arc::new(test_client::new());
		let tx_pool = Arc::new(EmptyTransactionPool);
		let verifier = self.make_verifier(client.clone(), config);
		let (block_import, data) = self.make_block_import(client.clone());

		let import_queue = Arc::new(SyncImportQueue::new(verifier, block_import));
		let specialization = DummySpecialization { };
		let sync = Protocol::new(
			config.clone(),
			client.clone(),
			import_queue.clone(),
			None,
			tx_pool,
			specialization
		).unwrap();

		let peer = Arc::new(Peer::new(
			client,
			Arc::new(sync),
			Arc::new(RwLock::new(VecDeque::new())),
			import_queue,
			data,
		));

		self.mut_peers(|peers| {
			peers.push(peer.clone())
		});
	}

	/// Start network.
	fn start(&mut self) {
		if self.started() {
			return;
		}
		self.mut_peers(|peers| {
			for peer in 0..peers.len() {
				peers[peer].start();
				for client in 0..peers.len() {
					if peer != client {
						peers[peer].on_connect(client as NodeIndex);
					}
				}
			}
		});
		self.set_started(true);
	}

	/// Do one step of routing.
	fn route(&mut self) {
		self.mut_peers(move |peers| {
			for peer in 0..peers.len() {
				let packet = peers[peer].pending_message();
				if let Some(packet) = packet {
					let disconnecting = {
						let recipient = packet.recipient;
						trace!(target: "sync", "--- {} -> {} ---", peer, recipient);
						let to_disconnect = peers[recipient].receive_message(peer as NodeIndex, packet);
						for d in &to_disconnect {
							// notify this that disconnecting peers are disconnecting
							peers[recipient].on_disconnect(*d as NodeIndex);
						}
						to_disconnect
					};
					for d in &disconnecting {
						// notify other peers that this peer is disconnecting
						peers[*d].on_disconnect(peer as NodeIndex);
					}
				}
			}
		});
	}

	/// Route messages between peers until all queues are empty.
	fn route_until_complete(&mut self) {
		while !self.done() {
			self.route()
		}
	}

	/// Do a step of synchronization.
	fn sync_step(&mut self) {
		self.route();

		self.mut_peers(|peers| {
			for peer in peers {
				peer.sync_step();
			}
		})
	}

	/// Send block import notifications for all peers.
	fn send_import_notifications(&mut self) {
		self.mut_peers(|peers| {
			for peer in peers {
				peer.send_import_notifications();
			}
		})
	}

	/// Restart sync for a peer.
	fn restart_peer(&mut self, i: usize) {
		self.peers()[i].restart_sync();
	}

	/// Perform synchronization until complete.
	fn sync(&mut self) -> u32 {
		self.start();
		let mut total_steps = 0;
		while !self.done() {
			self.sync_step();
			total_steps += 1;
			self.route();
		}
		total_steps
	}

	/// Do the given amount of sync steps.
	fn sync_steps(&mut self, count: usize) {
		self.start();
		for _ in 0..count {
			self.sync_step();
		}
	}

	/// Whether all peers have synced.
	fn done(&self) -> bool {
		self.peers().iter().all(|p| p.is_done())
	}
}

pub struct TestNet {
	peers: Vec<Arc<Peer<PassThroughVerifier, ()>>>,
	started: bool
}

impl TestNetFactory for TestNet {
	type Verifier = PassThroughVerifier;
	type PeerData = ();

	/// Create new test network with peers and given config.
	fn from_config(_config: &ProtocolConfig) -> Self {
		TestNet {
			peers: Vec::new(),
			started: false
		}
	}

	fn make_verifier(&self, _client: Arc<PeersClient>, _config: &ProtocolConfig)
		-> Arc<Self::Verifier>
	{
		Arc::new(PassThroughVerifier(false))
	}

	fn peer(&self, i: usize) -> &Peer<Self::Verifier, ()> {
		&self.peers[i]
	}

	fn peers(&self) -> &Vec<Arc<Peer<Self::Verifier, ()>>> {
		&self.peers
	}

	fn mut_peers<F: Fn(&mut Vec<Arc<Peer<Self::Verifier, ()>>>)>(&mut self, closure: F ) {
		closure(&mut self.peers);
	}

	fn started(&self) -> bool {
		self.started
	}

	fn set_started(&mut self, new: bool) {
		self.started = new;
	}
}
