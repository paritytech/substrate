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

mod consensus;
mod sync;

use std::collections::{VecDeque, HashSet, HashMap};
use std::sync::Arc;

use parking_lot::RwLock;
use client;
use client::block_builder::BlockBuilder;
use primitives::block::{Id as BlockId, ExtrinsicHash, HeaderHash};
use primitives;
use io::SyncIo;
use protocol::Protocol;
use config::ProtocolConfig;
use service::TransactionPool;
use network::{PeerId, SessionInfo, Error as NetworkError};
use runtime_support::Hashable;
use keyring::Keyring;
use codec::Slicable;
use test_client::{self, TestClient};

pub struct TestIo<'p> {
	pub queue: &'p RwLock<VecDeque<TestPacket>>,
	pub sender: Option<PeerId>,
	pub to_disconnect: HashSet<PeerId>,
	pub packets: Vec<TestPacket>,
	pub peers_info: HashMap<PeerId, String>,
}

impl<'p> TestIo<'p> where {
	pub fn new(queue: &'p RwLock<VecDeque<TestPacket>>, sender: Option<PeerId>) -> TestIo<'p> {
		TestIo {
			queue: queue,
			sender: sender,
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
	fn disable_peer(&mut self, peer_id: PeerId) {
		self.disconnect_peer(peer_id);
	}

	fn disconnect_peer(&mut self, peer_id: PeerId) {
		self.to_disconnect.insert(peer_id);
	}

	fn is_expired(&self) -> bool {
		false
	}

	fn send(&mut self, peer_id: PeerId, data: Vec<u8>) -> Result<(), NetworkError> {
		self.packets.push(TestPacket {
			data: data,
			recipient: peer_id,
		});
		Ok(())
	}

	fn peer_info(&self, peer_id: PeerId) -> String {
		self.peers_info.get(&peer_id)
			.cloned()
			.unwrap_or_else(|| peer_id.to_string())
	}

	fn peer_session_info(&self, _peer_id: PeerId) -> Option<SessionInfo> {
		None
	}
}

/// Mocked subprotocol packet
pub struct TestPacket {
	pub data: Vec<u8>,
	pub recipient: PeerId,
}

pub struct Peer {
	client: Arc<client::Client<test_client::Backend, test_client::Executor>>,
	pub sync: Protocol,
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
	fn on_connect(&self, other: PeerId) {
		self.sync.on_peer_connected(&mut TestIo::new(&self.queue, Some(other)), other);
	}

	/// Called on disconnect from other indicated peer.
	fn on_disconnect(&self, other: PeerId) {
		let mut io = TestIo::new(&self.queue, Some(other));
		self.sync.on_peer_disconnected(&mut io, other);
	}

	/// Receive a message from another peer. Return a set of peers to disconnect.
	fn receive_message(&self, from: PeerId, msg: TestPacket) -> HashSet<PeerId> {
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

	fn generate_blocks<F>(&self, count: usize, mut edit_block: F) where F: FnMut(&mut BlockBuilder<test_client::Backend, test_client::Executor>) {
		for _ in 0 .. count {
			let mut builder = self.client.new_block().unwrap();
			edit_block(&mut builder);
			let block = builder.bake().unwrap();
			trace!("Generating {}, (#{})", primitives::block::HeaderHash::from(block.header.blake2_256()), block.header.number);
			self.client.justify_and_import(client::BlockOrigin::File, block).unwrap();
		}
	}

	fn push_blocks(&self, count: usize, with_tx: bool) {
		let mut nonce = 0;
		if with_tx {
			self.generate_blocks(count, |builder| {
				let tx = test_client::runtime::Transaction {
					from: Keyring::Alice.to_raw_public(),
					to: Keyring::Alice.to_raw_public(),
					amount: 1,
					nonce: nonce,
				};
				let signature = Keyring::from_raw_public(tx.from.clone()).unwrap().sign(&tx.encode());
				let tx = primitives::block::Extrinsic::decode(&mut test_client::runtime::UncheckedTransaction { signature, tx: tx }.encode().as_ref()).unwrap();
				builder.push(tx).unwrap();
				nonce = nonce + 1;
			});
		} else {
			self.generate_blocks(count, |_| ());
		}
	}

	pub fn genesis_hash(&self) -> HeaderHash {
		let info = self.client.info().expect("In-mem client does not fail");
		info.chain.genesis_hash
	}
}

struct EmptyTransactionPool;

impl TransactionPool for EmptyTransactionPool {
	fn transactions(&self) -> Vec<(ExtrinsicHash, Vec<u8>)> {
		Vec::new()
	}

	fn import(&self, _transaction: &[u8]) -> Option<ExtrinsicHash> {
		None
	}

	fn on_broadcasted(&self, _: HashMap<ExtrinsicHash, Vec<String>>) {}
}

pub struct TestNet {
	pub peers: Vec<Arc<Peer>>,
	pub started: bool,
	pub disconnect_events: Vec<(PeerId, PeerId)>, //disconnected (initiated by, to)
}

impl TestNet {
	pub fn new(n: usize) -> Self {
		Self::new_with_config(n, ProtocolConfig::default())
	}

	pub fn new_with_config(n: usize, config: ProtocolConfig) -> Self {
		let mut net = TestNet {
			peers: Vec::new(),
			started: false,
			disconnect_events: Vec::new(),
		};

		for _ in 0..n {
			let client = Arc::new(test_client::new());
			let tx_pool = Arc::new(EmptyTransactionPool);
			let sync = Protocol::new(config.clone(), client.clone(), None, tx_pool).unwrap();
			net.peers.push(Arc::new(Peer {
				sync: sync,
				client: client,
				queue: RwLock::new(VecDeque::new()),
			}));
		}
		net
	}

	pub fn peer(&self, i: usize) -> &Peer {
		&self.peers[i]
	}

	pub fn start(&mut self) {
		if self.started {
			return;
		}
		for peer in 0..self.peers.len() {
			self.peers[peer].start();
			for client in 0..self.peers.len() {
				if peer != client {
					self.peers[peer].on_connect(client as PeerId);
				}
			}
		}
		self.started = true;
	}

	pub fn sync_step(&mut self) {
		for peer in 0..self.peers.len() {
			let packet = self.peers[peer].pending_message();
			if let Some(packet) = packet {
				let disconnecting = {
					let recipient = packet.recipient;
					trace!("--- {} -> {} ---", peer, recipient);
					let to_disconnect = self.peers[recipient].receive_message(peer as PeerId, packet);
					for d in &to_disconnect {
						// notify this that disconnecting peers are disconnecting
						self.peers[recipient].on_disconnect(*d as PeerId);
						self.disconnect_events.push((peer, *d));
					}
					to_disconnect
				};
				for d in &disconnecting {
					// notify other peers that this peer is disconnecting
					self.peers[*d].on_disconnect(peer as PeerId);
				}
			}

			self.sync_step_peer(peer);
		}
	}

	pub fn sync_step_peer(&mut self, peer_num: usize) {
		self.peers[peer_num].sync_step();
	}

	pub fn restart_peer(&mut self, i: usize) {
		self.peers[i].restart_sync();
	}

	pub fn sync(&mut self) -> u32 {
		self.start();
		let mut total_steps = 0;
		while !self.done() {
			self.sync_step();
			total_steps += 1;
		}
		total_steps
	}

	pub fn sync_steps(&mut self, count: usize) {
		self.start();
		for _ in 0..count {
			self.sync_step();
		}
	}

	pub fn done(&self) -> bool {
		self.peers.iter().all(|p| p.is_done())
	}
}
