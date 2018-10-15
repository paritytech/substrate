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
use client::block_builder::BlockBuilder;
use runtime_primitives::generic::BlockId;
use io::SyncIo;
use protocol::{Context, Protocol};
use primitives::{Blake2Hasher};
use config::ProtocolConfig;
use service::TransactionPool;
use network_libp2p::{NodeIndex, PeerId, Severity};
use keyring::Keyring;
use codec::{Encode, Decode};
use import_queue::SyncImportQueue;
use test_client::{self, TestClient};
use specialization::Specialization;
use consensus_gossip::ConsensusGossip;

pub use test_client::runtime::{Block, Hash, Transfer, Extrinsic};

/// The test specialization.
pub struct DummySpecialization {
	/// Consensus gossip handle.
	pub gossip: ConsensusGossip<Block>,
}

#[derive(Encode, Decode)]
pub struct GossipMessage {
	/// The topic to classify under.
	pub topic: Hash,
	/// The data to send.
	pub data: Vec<u8>,
}

impl Specialization<Block> for DummySpecialization {
	fn status(&self) -> Vec<u8> { vec![] }

	fn on_connect(&mut self, ctx: &mut Context<Block>, peer_id: NodeIndex, status: ::message::Status<Block>) {
		self.gossip.new_peer(ctx, peer_id, status.roles);
	}

	fn on_disconnect(&mut self, ctx: &mut Context<Block>, peer_id: NodeIndex) {
		self.gossip.peer_disconnected(ctx, peer_id);
	}

	fn on_message(&mut self, ctx: &mut Context<Block>, peer_id: NodeIndex, message: &mut Option<::message::Message<Block>>) {
		if let Some(::message::generic::Message::ChainSpecific(data)) = message.take() {
			let gossip_message = GossipMessage::decode(&mut &data[..])
				.expect("gossip messages all in known format; qed");
			self.gossip.on_chain_specific(ctx, peer_id, data, gossip_message.topic)
		}
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

pub struct Peer {
	client: Arc<client::Client<test_client::Backend, test_client::Executor, Block>>,
	pub sync: Protocol<Block, DummySpecialization, Hash>,
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

	/// Push a message into the gossip network and relay to peers.
	/// `TestNet::sync_step` needs to be called to ensure it's propagated.
	pub fn gossip_message(&self, topic: Hash, data: Vec<u8>) {
		self.sync.with_spec(&mut TestIo::new(&self.queue, None), |spec, ctx| {
			let message = GossipMessage { topic, data }.encode();
			spec.gossip.multicast_chain_specific(ctx, message, topic);
		})
	}

	/// Add blocks to the peer -- edit the block before adding
	pub fn generate_blocks<F>(&self, count: usize, mut edit_block: F)
	where F: FnMut(&mut BlockBuilder<test_client::Backend, test_client::Executor, Block, Blake2Hasher>)
	{
		for _ in 0 .. count {
			let mut builder = self.client.new_block().unwrap();
			edit_block(&mut builder);
			let block = builder.bake().unwrap();
			trace!("Generating {}, (#{}, parent={})", block.header.hash(), block.header.number, block.header.parent_hash);
			self.client.justify_and_import(client::BlockOrigin::File, block).unwrap();
		}
	}

	/// Push blocks to the peer (simplified: with or without a TX)
	pub fn push_blocks(&self, count: usize, with_tx: bool) {
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

	/// Execute a function with specialization for this peer.
	pub fn with_spec<F, U>(&self, f: F) -> U
		where F: FnOnce(&mut DummySpecialization, &mut Context<Block>) -> U
	{
		self.sync.with_spec(&mut TestIo::new(&self.queue, None), f)
	}

	/// Get a reference to the client.
	pub fn client(&self) -> &Arc<client::Client<test_client::Backend, test_client::Executor, Block>> {
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

pub struct TestNet {
	peers: Vec<Arc<Peer>>,
	started: bool,
	disconnect_events: Vec<(NodeIndex, NodeIndex)>, //disconnected (initiated by, to)
}

impl TestNet {
	/// Create new test network with this many peers.
	pub fn new(n: usize) -> Self {
		Self::new_with_config(n, ProtocolConfig::default())
	}

	/// Create new test network with peers and given config.
	pub fn new_with_config(n: usize, config: ProtocolConfig) -> Self {
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

	/// Add a peer.
	pub fn add_peer(&mut self, config: &ProtocolConfig) {
		let client = Arc::new(test_client::new());
		let tx_pool = Arc::new(EmptyTransactionPool);
		let import_queue = Arc::new(SyncImportQueue(false));
		let specialization = DummySpecialization {
			gossip: ConsensusGossip::new(),
		};
		let sync = Protocol::new(
			config.clone(),
			client.clone(),
			import_queue,
			None,
			tx_pool,
			specialization
		).unwrap();

		self.peers.push(Arc::new(Peer {
			sync: sync,
			client: client,
			queue: RwLock::new(VecDeque::new()),
		}));
	}

	/// Get reference to peer.
	pub fn peer(&self, i: usize) -> &Peer {
		&self.peers[i]
	}

	/// Start network.
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

	/// Do one step of routing.
	pub fn route(&mut self) {
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
		}
	}

	/// Route messages between peers until all queues are empty.
	pub fn route_until_complete(&mut self) {
		while !self.done() {
			self.route()
		}
	}

	/// Do a step of synchronization.
	pub fn sync_step(&mut self) {
		self.route();

		for peer in &mut self.peers {
			peer.sync_step();
		}
	}

	/// Restart sync for a peer.
	pub fn restart_peer(&mut self, i: usize) {
		self.peers[i].restart_sync();
	}

	/// Perform synchronization until complete.
	pub fn sync(&mut self) -> u32 {
		self.start();
		let mut total_steps = 0;
		while !self.done() {
			self.sync_step();
			total_steps += 1;
		}
		total_steps
	}

	/// Do the given amount of sync steps.
	pub fn sync_steps(&mut self, count: usize) {
		self.start();
		for _ in 0..count {
			self.sync_step();
		}
	}

	/// Whether all peers have synced.
	pub fn done(&self) -> bool {
		self.peers.iter().all(|p| p.is_done())
	}
}
