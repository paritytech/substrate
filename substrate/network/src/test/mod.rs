// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

mod sync;

use std::collections::{VecDeque, HashSet, HashMap};
use std::sync::Arc;

use parking_lot::RwLock;
use client;
use client::block_builder::BlockBuilder;
use runtime_primitives::traits::Block as BlockT;
use runtime_primitives::generic::BlockId;
use io::SyncIo;
use protocol::{Context, Protocol};
use primitives::{KeccakHasher, RlpCodec};
use config::ProtocolConfig;
use service::TransactionPool;
use network_libp2p::{NodeIndex, SessionInfo, Severity};
use keyring::Keyring;
use codec::Encode;
use import_queue::tests::SyncImportQueue;
use test_client::{self, TestClient};
use test_client::runtime::{Block, Hash, Transfer, Extrinsic};
use specialization::Specialization;

pub struct DummySpecialization;

impl Specialization<Block> for DummySpecialization {
	fn status(&self) -> Vec<u8> { vec![] }

	fn on_connect(&mut self, _ctx: &mut Context<Block>, _peer_id: NodeIndex, _status: ::message::Status<Block>) {

	}

	fn on_disconnect(&mut self, _ctx: &mut Context<Block>, _peer_id: NodeIndex) {

	}

	fn on_message(&mut self, _ctx: &mut Context<Block>, _peer_id: NodeIndex, _message: ::message::Message<Block>) {

	}
}

pub struct TestIo<'p> {
	queue: &'p RwLock<VecDeque<TestPacket>>,
	pub to_disconnect: HashSet<NodeIndex>,
	packets: Vec<TestPacket>,
	peers_info: HashMap<NodeIndex, String>,
	_sender: Option<NodeIndex>,
}

impl<'p> TestIo<'p> where {
	pub fn new(queue: &'p RwLock<VecDeque<TestPacket>>, sender: Option<NodeIndex>) -> TestIo<'p> {
		TestIo {
			queue: queue,
			_sender: sender,
			to_disconnect: HashSet::new(),
			packets: Vec::new(),
			peers_info: HashMap::new(),
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

	fn is_expired(&self) -> bool {
		false
	}

	fn send(&mut self, who: NodeIndex, data: Vec<u8>) {
		self.packets.push(TestPacket {
			data: data,
			recipient: who,
		});
	}

	fn peer_info(&self, who: NodeIndex) -> String {
		self.peers_info.get(&who)
			.cloned()
			.unwrap_or_else(|| who.to_string())
	}

	fn peer_session_info(&self, _peer_id: NodeIndex) -> Option<SessionInfo> {
		None
	}
}

/// Mocked subprotocol packet
pub struct TestPacket {
	data: Vec<u8>,
	recipient: NodeIndex,
}

pub struct Peer {
	client: Arc<client::Client<test_client::Backend, test_client::Executor, Block>>,
	pub sync: Protocol<Block, DummySpecialization>,
	pub queue: RwLock<VecDeque<TestPacket>>,
}

impl Peer {
	/// Called after blockchain has been populated to updated current state.
	fn start(&self) {
		// Update the sync state to the latest chain state.
		let info = self.client.info().expect("In-mem client does not fail");
		let header = self.client.header(&BlockId::Hash(info.chain.best_hash)).unwrap().unwrap();
		self.sync.on_block_imported(&mut TestIo::new(&self.queue, None), info.chain.best_hash, &header);
	}

	/// Called on connection to other indicated peer.
	fn on_connect(&self, other: NodeIndex) {
		self.sync.on_peer_connected(&mut TestIo::new(&self.queue, Some(other)), other);
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

	/// Restart sync for a peer.
	fn restart_sync(&self) {
		self.sync.abort();
	}

	fn flush(&self) {
	}

	fn generate_blocks<F>(&self, count: usize, mut edit_block: F)
	where F: FnMut(&mut BlockBuilder<test_client::Backend, test_client::Executor, Block, KeccakHasher, RlpCodec>)
	{
		for _ in 0 .. count {
			let mut builder = self.client.new_block().unwrap();
			edit_block(&mut builder);
			let block = builder.bake().unwrap();
			trace!("Generating {}, (#{})", block.hash(), block.header.number);
			self.client.justify_and_import(client::BlockOrigin::File, block).unwrap();
		}
	}

	fn push_blocks(&self, count: usize, with_tx: bool) {
		let mut nonce = 0;
		if with_tx {
			self.generate_blocks(count, |builder| {
				let transfer = Transfer {
					from: Keyring::Alice.to_raw_public().into(),
					to: Keyring::Alice.to_raw_public().into(),
					amount: 1,
					nonce,
				};
				let signature = Keyring::from_raw_public(transfer.from.0).unwrap().sign(&transfer.encode()).into();
				builder.push(Extrinsic { transfer, signature }).unwrap();
				nonce = nonce + 1;
			});
		} else {
			self.generate_blocks(count, |_| ());
		}
	}
}

pub struct EmptyTransactionPool;

impl TransactionPool<Block> for EmptyTransactionPool {
	fn transactions(&self) -> Vec<(Hash, Extrinsic)> {
		Vec::new()
	}

	fn import(&self, _transaction: &Extrinsic) -> Option<Hash> {
		None
	}

	fn on_broadcasted(&self, _: HashMap<Hash, Vec<String>>) {}
}

pub struct TestNet {
	peers: Vec<Arc<Peer>>,
	started: bool,
	disconnect_events: Vec<(NodeIndex, NodeIndex)>, //disconnected (initiated by, to)
}

impl TestNet {
	fn new(n: usize) -> Self {
		Self::new_with_config(n, ProtocolConfig::default())
	}

	fn new_with_config(n: usize, config: ProtocolConfig) -> Self {
		let mut net = TestNet {
			peers: Vec::new(),
			started: false,
			disconnect_events: Vec::new(),
		};

		for _ in 0..n {
			net.add_peer(&config);
		}
		net
	}

	pub fn add_peer(&mut self, config: &ProtocolConfig) {
		let client = Arc::new(test_client::new());
		let tx_pool = Arc::new(EmptyTransactionPool);
		let import_queue = Arc::new(SyncImportQueue);
		let sync = Protocol::new(config.clone(), client.clone(), import_queue, None, tx_pool, DummySpecialization).unwrap();
		self.peers.push(Arc::new(Peer {
			sync: sync,
			client: client,
			queue: RwLock::new(VecDeque::new()),
		}));
	}

	pub fn peer(&self, i: usize) -> &Peer {
		&self.peers[i]
	}

	fn start(&mut self) {
		if self.started {
			return;
		}
		for peer in 0..self.peers.len() {
			self.peers[peer].start();
			for client in 0..self.peers.len() {
				if peer != client {
					self.peers[peer].on_connect(client as NodeIndex);
				}
			}
		}
		self.started = true;
	}

	fn sync_step(&mut self) {
		for peer in 0..self.peers.len() {
			let packet = self.peers[peer].pending_message();
			if let Some(packet) = packet {
				let disconnecting = {
					let recipient = packet.recipient;
					trace!("--- {} -> {} ---", peer, recipient);
					let to_disconnect = self.peers[recipient].receive_message(peer as NodeIndex, packet);
					for d in &to_disconnect {
						// notify this that disconnecting peers are disconnecting
						self.peers[recipient].on_disconnect(*d as NodeIndex);
						self.disconnect_events.push((peer, *d));
					}
					to_disconnect
				};
				for d in &disconnecting {
					// notify other peers that this peer is disconnecting
					self.peers[*d].on_disconnect(peer as NodeIndex);
				}
			}

			self.sync_step_peer(peer);
		}
	}

	fn sync_step_peer(&mut self, peer_num: usize) {
		self.peers[peer_num].sync_step();
	}

	fn restart_peer(&mut self, i: usize) {
		self.peers[i].restart_sync();
	}

	fn sync(&mut self) -> u32 {
		self.start();
		let mut total_steps = 0;
		while !self.done() {
			self.sync_step();
			total_steps += 1;
		}
		total_steps
	}

	fn sync_steps(&mut self, count: usize) {
		self.start();
		for _ in 0..count {
			self.sync_step();
		}
	}

	fn done(&self) -> bool {
		self.peers.iter().all(|p| p.is_done())
	}
}
