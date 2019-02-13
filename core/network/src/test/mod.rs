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
mod block_import;
#[cfg(test)]
mod sync;

use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use std::time::Duration;

use log::trace;
use client;
use client::block_builder::BlockBuilder;
use crate::config::ProtocolConfig;
use consensus::import_queue::{import_many_blocks, ImportQueue, ImportQueueStatus, IncomingBlock};
use consensus::import_queue::{Link, SharedBlockImport, SharedJustificationImport, Verifier};
use consensus::{Error as ConsensusError, ErrorKind as ConsensusErrorKind};
use consensus::{BlockOrigin, ForkChoiceStrategy, ImportBlock, JustificationImport};
use crate::consensus_gossip::{ConsensusGossip, ConsensusMessage};
use crossbeam_channel::{self as channel, Sender, select};
use futures::Future;
use futures::sync::{mpsc, oneshot};
use keyring::Keyring;
use crate::message::Message;
use network_libp2p::{NodeIndex, ProtocolId};
use parity_codec::Encode;
use parking_lot::Mutex;
use primitives::{H256, Ed25519AuthorityId};
use crate::protocol::{Context, Protocol, ProtocolMsg, ProtocolStatus};
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{AuthorityIdFor, Block as BlockT, Digest, DigestItem, Header, Zero, NumberFor};
use runtime_primitives::Justification;
use crate::service::{network_channel, NetworkChan, NetworkLink, NetworkMsg, NetworkPort, TransactionPool};
use crate::specialization::NetworkSpecialization;
use test_client;

pub use test_client::runtime::{Block, Extrinsic, Hash, Transfer};
pub use test_client::TestClient;

#[cfg(any(test, feature = "test-helpers"))]
use std::cell::RefCell;

#[cfg(any(test, feature = "test-helpers"))]
struct ImportCB<B: BlockT>(RefCell<Option<Box<dyn Fn(BlockOrigin, Vec<IncomingBlock<B>>) -> bool>>>);

#[cfg(any(test, feature = "test-helpers"))]
impl<B: BlockT> ImportCB<B> {
	fn new() -> Self {
		ImportCB(RefCell::new(None))
	}
	fn set<F>(&self, cb: Box<F>)
	where F: 'static + Fn(BlockOrigin, Vec<IncomingBlock<B>>) -> bool,
	{
		*self.0.borrow_mut() = Some(cb);
	}
	fn call(&self, origin: BlockOrigin, data: Vec<IncomingBlock<B>>) -> bool {
		let b = self.0.borrow();
		b.as_ref().expect("The Callback has been set before. qed.")(origin, data)
	}
}

#[cfg(any(test, feature = "test-helpers"))]
unsafe impl<B: BlockT> Send for ImportCB<B> {}
#[cfg(any(test, feature = "test-helpers"))]
unsafe impl<B: BlockT> Sync for ImportCB<B> {}


#[cfg(any(test, feature = "test-helpers"))]
/// A Verifier that accepts all blocks and passes them on with the configured
/// finality to be imported.
pub struct PassThroughVerifier(pub bool);

#[cfg(any(test, feature = "test-helpers"))]
/// This Verifiyer accepts all data as valid
impl<B: BlockT> Verifier<B> for PassThroughVerifier {
	fn verify(
		&self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Option<Justification>,
		body: Option<Vec<B::Extrinsic>>
	) -> Result<(ImportBlock<B>, Option<Vec<AuthorityIdFor<B>>>), String> {
		let new_authorities = header.digest().log(DigestItem::as_authorities_change)
			.map(|auth| auth.iter().cloned().collect());

		Ok((ImportBlock {
			origin,
			header,
			body,
			finalized: self.0,
			justification,
			post_digests: vec![],
			auxiliary: Vec::new(),
			fork_choice: ForkChoiceStrategy::LongestChain,
		}, new_authorities))
	}
}

/// A link implementation that does nothing.
pub struct NoopLink;

impl<B: BlockT> Link<B> for NoopLink { }

/// Blocks import queue that is importing blocks in the same thread.
/// The boolean value indicates whether blocks should be imported without instant finality.
#[cfg(any(test, feature = "test-helpers"))]
pub struct SyncImportQueue<B: BlockT, V: Verifier<B>> {
	verifier: Arc<V>,
	link: ImportCB<B>,
	block_import: SharedBlockImport<B>,
	justification_import: Option<SharedJustificationImport<B>>,
}

#[cfg(any(test, feature = "test-helpers"))]
impl<B: 'static + BlockT, V: 'static + Verifier<B>> SyncImportQueue<B, V> {
	/// Create a new SyncImportQueue wrapping the given Verifier and block import
	/// handle.
	pub fn new(verifier: Arc<V>, block_import: SharedBlockImport<B>, justification_import: Option<SharedJustificationImport<B>>) -> Self {
		let queue = SyncImportQueue {
			verifier,
			link: ImportCB::new(),
			block_import,
			justification_import,
		};

		let v = queue.verifier.clone();
		let import_handle = queue.block_import.clone();
		queue.link.set(Box::new(move |origin, new_blocks| {
			let verifier = v.clone();
			import_many_blocks(
				&*import_handle,
				&NoopLink,
				None,
				(origin, new_blocks),
				verifier,
			)
		}));

		queue
	}
}

#[cfg(any(test, feature = "test-helpers"))]
impl<B: 'static + BlockT, V: 'static + Verifier<B>> ImportQueue<B> for SyncImportQueue<B, V>
{
	fn start<L: 'static + Link<B>>(
		&self,
		link: L,
	) -> Result<(), std::io::Error> {
		let v = self.verifier.clone();
		let import_handle = self.block_import.clone();
		self.link.set(Box::new(move |origin, new_blocks| {
			let verifier = v.clone();
			import_many_blocks(
				&*import_handle,
				&link,
				None,
				(origin, new_blocks),
				verifier
			)
		}));
		Ok(())
	}
	fn clear(&self) { }

	fn stop(&self) { }

	fn status(&self) -> ImportQueueStatus<B> {
		ImportQueueStatus {
			importing_count: 0,
			best_importing_number: Zero::zero(),
		}
	}

	fn is_importing(&self, _hash: &B::Hash) -> bool {
		false
	}

	fn import_blocks(&self, origin: BlockOrigin, blocks: Vec<IncomingBlock<B>>) {
		self.link.call(origin, blocks);
	}

	fn import_justification(
		&self,
		hash: B::Hash,
		number: NumberFor<B>,
		justification: Justification,
	) -> bool {
		self.justification_import.as_ref().map(|justification_import| {
			justification_import.import_justification(hash, number, justification).is_ok()
		}).unwrap_or(false)
	}
}

/// The test specialization.
pub struct DummySpecialization { }

impl NetworkSpecialization<Block> for DummySpecialization {
	fn status(&self) -> Vec<u8> {
		vec![]
	}

	fn on_connect(&mut self, _ctx: &mut Context<Block>, _peer_id: NodeIndex, _status: crate::message::Status<Block>) {
	}

	fn on_disconnect(&mut self, _ctx: &mut Context<Block>, _peer_id: NodeIndex) {
	}

	fn on_message(
		&mut self,
		_ctx: &mut Context<Block>,
		_peer_id: NodeIndex,
		_message: &mut Option<crate::message::Message<Block>>,
	) {
	}
}

pub type PeersClient = client::Client<test_client::Backend, test_client::Executor, Block, test_client::runtime::RuntimeApi>;

pub struct Peer<V: 'static + Verifier<Block>, D> {
	client: Arc<PeersClient>,
	pub protocol_sender: Sender<ProtocolMsg<Block, DummySpecialization>>,
	network_port: Mutex<NetworkPort<Block>>,
	import_queue: Arc<SyncImportQueue<Block, V>>,
	network_sender: NetworkChan<Block>,
	pub data: D,
}

impl<V: 'static + Verifier<Block>, D> Peer<V, D> {
	fn new(
		client: Arc<PeersClient>,
		import_queue: Arc<SyncImportQueue<Block, V>>,
		protocol_sender: Sender<ProtocolMsg<Block, DummySpecialization>>,
		network_sender: NetworkChan<Block>,
		network_port: NetworkPort<Block>,
		data: D,
	) -> Self {
		let network_port = Mutex::new(network_port);
		Peer {
			client,
			protocol_sender,
			import_queue,
			network_sender,
			network_port,
			data,
		}
	}
	/// Called after blockchain has been populated to updated current state.
	fn start(&self) {
		// Update the sync state to the latest chain state.
		let info = self.client.info().expect("In-mem client does not fail");
		let header = self
			.client
			.header(&BlockId::Hash(info.chain.best_hash))
			.unwrap()
			.unwrap();
		let network_link = NetworkLink {
			protocol_sender: self.protocol_sender.clone(),
			network_sender: self.network_sender.clone(),
		};

		self.import_queue.start(network_link).expect("Test ImportQueue always starts");
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::BlockImported(info.chain.best_hash, header));
	}

	pub fn on_block_imported(
		&self,
		hash: <Block as BlockT>::Hash,
		header: &<Block as BlockT>::Header,
	) {
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::BlockImported(hash, header.clone()));
	}

	/// Called on connection to other indicated peer.
	fn on_connect(&self, other: NodeIndex) {
		let _ = self.protocol_sender.send(ProtocolMsg::PeerConnected(other, String::new()));
	}

	/// Called on disconnect from other indicated peer.
	fn on_disconnect(&self, other: NodeIndex) {
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::PeerDisconnected(other, String::new()));
	}

	/// Receive a message from another peer. Return a set of peers to disconnect.
	fn receive_message(&self, from: NodeIndex, msg: Message<Block>) {
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::CustomMessage(from, msg));
	}

	/// Produce the next pending message to send to another peer.
	fn pending_message(&self) -> Option<NetworkMsg<Block>> {
		select! {
			recv(self.network_port.lock().receiver()) -> msg => return msg.ok(),
			// If there are no messages ready, give protocol a change to send one.
			recv(channel::after(Duration::from_millis(100))) -> _ => return None,
		}
	}

	/// Produce the next pending message to send to another peer, without waiting.
	fn pending_message_fast(&self) -> Option<NetworkMsg<Block>> {
		self.network_port.lock().receiver().try_recv().ok()
	}

	/// Whether this peer is done syncing (has no messages to send).
	fn is_done(&self) -> bool {
		self.network_port.lock().receiver().is_empty()
	}

	/// Execute a "sync step". This is called for each peer after it sends a packet.
	fn sync_step(&self) {
		let _ = self.protocol_sender.send(ProtocolMsg::Tick);
	}

	/// Send block import notifications.
	fn send_import_notifications(&self) {
		let info = self.client.info().expect("In-mem client does not fail");
		let header = self.client.header(&BlockId::Hash(info.chain.best_hash)).unwrap().unwrap();
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::BlockImported(info.chain.best_hash, header));
	}

	/// Send block finalization notifications.
	pub fn send_finality_notifications(&self) {
		let info = self.client.info().expect("In-mem client does not fail");
		let header = self.client.header(&BlockId::Hash(info.chain.finalized_hash)).unwrap().unwrap();
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::BlockFinalized(info.chain.finalized_hash, header.clone()));
	}

	/// Restart sync for a peer.
	fn restart_sync(&self) {
		let _ = self.protocol_sender.send(ProtocolMsg::Abort);
	}

	pub fn status(&self) -> ProtocolStatus<Block> {
		let (sender, port) = channel::unbounded();
		let _ = self.protocol_sender.send(ProtocolMsg::Status(sender));
		port.recv().unwrap()
	}

	/// Push a message into the gossip network and relay to peers.
	/// `TestNet::sync_step` needs to be called to ensure it's propagated.
	pub fn gossip_message(&self, topic: <Block as BlockT>::Hash, data: Vec<u8>, broadcast: bool) {
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::GossipConsensusMessage(topic, data, broadcast));
	}

	pub fn consensus_gossip_collect_garbage_for_topic(&self, topic: <Block as BlockT>::Hash) {
		self.with_gossip(move |gossip, _| gossip.collect_garbage_for_topic(topic))
	}

	/// access the underlying consensus gossip handler
	pub fn consensus_gossip_messages_for(
		&self,
		topic: <Block as BlockT>::Hash,
	) -> mpsc::UnboundedReceiver<ConsensusMessage> {
		let (tx, rx) = oneshot::channel();
		self.with_gossip(move |gossip, _| {
			let inner_rx = gossip.messages_for(topic);
			let _ = tx.send(inner_rx);
		});
		rx.wait().ok().expect("1. Network is running, 2. it should handle the above closure successfully")
	}

	/// Execute a closure with the consensus gossip.
	pub fn with_gossip<F>(&self, f: F)
		where F: FnOnce(&mut ConsensusGossip<Block>, &mut Context<Block>) + Send + 'static
	{
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::ExecuteWithGossip(Box::new(f)));
	}

	/// Announce a block to peers.
	pub fn announce_block(&self, block: Hash) {
		let _ = self.protocol_sender.send(ProtocolMsg::AnnounceBlock(block));
	}

	/// Request a justification for the given block.
	#[cfg(test)]
	fn request_justification(&self, hash: &::primitives::H256, number: NumberFor<Block>) {
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::RequestJustification(hash.clone(), number));
	}

	/// Add blocks to the peer -- edit the block before adding
	pub fn generate_blocks<F>(&self, count: usize, origin: BlockOrigin, edit_block: F)
		where F: FnMut(BlockBuilder<Block, PeersClient>) -> Block
	{
		let best_hash = self.client.info().unwrap().chain.best_hash;
		self.generate_blocks_at(BlockId::Hash(best_hash), count, origin, edit_block)
	}

	/// Add blocks to the peer -- edit the block before adding. The chain will
	/// start at the given block iD.
	pub fn generate_blocks_at<F>(&self, mut at: BlockId<Block>, count: usize, origin: BlockOrigin, mut edit_block: F)
		where F: FnMut(BlockBuilder<Block, PeersClient>) -> Block
	{
		for _  in 0..count {
			let builder = self.client.new_block_at(&at).unwrap();
			let block = edit_block(builder);
			let hash = block.header.hash();
			trace!(
				"Generating {}, (#{}, parent={})",
				hash,
				block.header.number,
				block.header.parent_hash
			);
			let header = block.header.clone();
			at = BlockId::Hash(hash);

			// NOTE: if we use a non-synchronous queue in the test-net in the future,
			// this may not work.
			self.import_queue.import_blocks(
				origin,
				vec![IncomingBlock {
					origin: None,
					hash,
					header: Some(header),
					body: Some(block.extrinsics),
					justification: None,
				}
			]);
		}
	}

	/// Push blocks to the peer (simplified: with or without a TX)
	pub fn push_blocks(&self, count: usize, with_tx: bool) {
		let best_hash = self.client.info().unwrap().chain.best_hash;
		self.push_blocks_at(BlockId::Hash(best_hash), count, with_tx);
	}

	/// Push blocks to the peer (simplified: with or without a TX) starting from
	/// given hash.
	pub fn push_blocks_at(&self, at: BlockId<Block>, count: usize, with_tx: bool) {
		let mut nonce = 0;
		if with_tx {
			self.generate_blocks_at(at, count, BlockOrigin::File, |mut builder| {
				let transfer = Transfer {
					from: Keyring::Alice.to_raw_public().into(),
					to: Keyring::Alice.to_raw_public().into(),
					amount: 1,
					nonce,
				};
				let signature = Keyring::from_raw_public(transfer.from.to_fixed_bytes()).unwrap().sign(&transfer.encode()).into();
				builder.push(Extrinsic::Transfer(transfer, signature)).unwrap();
				nonce = nonce + 1;
				builder.bake().unwrap()
			});
		} else {
			self.generate_blocks_at(at, count, BlockOrigin::File, |builder| builder.bake().unwrap());
		}
	}

	pub fn push_authorities_change_block(&self, new_authorities: Vec<Ed25519AuthorityId>) {
		self.generate_blocks(1, BlockOrigin::File, |mut builder| {
			builder.push(Extrinsic::AuthoritiesChange(new_authorities.clone())).unwrap();
			builder.bake().unwrap()
		});
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
		-> (SharedBlockImport<Block>, Option<SharedJustificationImport<Block>>, Self::PeerData)
	{
		(client, None, Default::default())
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
		let (block_import, justification_import, data) = self.make_block_import(client.clone());
		let (network_sender, network_port) = network_channel(ProtocolId::default());

		let import_queue = Arc::new(SyncImportQueue::new(verifier, block_import, justification_import));
		let specialization = DummySpecialization { };
		let protocol_sender = Protocol::new(
			network_sender.clone(),
			config.clone(),
			client.clone(),
			import_queue.clone(),
			None,
			tx_pool,
			specialization,
		).unwrap();

		let peer = Arc::new(Peer::new(
			client,
			import_queue,
			protocol_sender,
			network_sender,
			network_port,
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
		self.route(None);
		self.set_started(true);
	}

	/// Do one step of routing.
	fn route(&mut self, disconnected: Option<HashSet<NodeIndex>>) {
		self.mut_peers(move |peers| {
			let mut to_disconnect = HashSet::new();
			for peer in 0..peers.len() {
				let packet = peers[peer].pending_message();
				match packet {
					None => continue,
					Some(NetworkMsg::Outgoing(recipient, packet)) => {
						if let Some(disconnected) = disconnected.as_ref() {
							let mut current = HashSet::new();
							current.insert(peer);
							current.insert(recipient);
							// Not routing message between "disconnected" nodes.
							if disconnected.is_subset(&current) {
								continue;
							}
						}
						peers[recipient].receive_message(peer as NodeIndex, packet)
					}
					Some(NetworkMsg::ReportPeer(who, _)) => {
						to_disconnect.insert(who);
					}
					Some(_msg) => continue,
				}
			}
			for d in to_disconnect {
				for peer in 0..peers.len() {
					peers[peer].on_disconnect(d);
				}
			}
		});
	}

	/// Route all pending outgoing messages, without waiting or disconnecting.
	fn route_fast(&mut self) {
		self.mut_peers(move |peers| {
			for peer in 0..peers.len() {
				while let Some(NetworkMsg::Outgoing(recipient, packet)) = peers[peer].pending_message_fast() {
					peers[recipient].receive_message(peer as NodeIndex, packet)
				}
			}
		});
	}

	/// Do a step of synchronization.
	fn sync_step(&mut self) {
		self.route(None);

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

	/// Send block finalization notifications for all peers.
	fn send_finality_notifications(&mut self) {
		self.mut_peers(|peers| {
			for peer in peers {
				peer.send_finality_notifications();
			}
		})
	}

	/// Restart sync for a peer.
	fn restart_peer(&mut self, i: usize) {
		self.peers()[i].restart_sync();
	}

	/// Perform synchronization until complete, if provided the
	/// given nodes set are excluded from sync.
	fn sync_with(&mut self, disconnected: Option<HashSet<NodeIndex>>) -> u32 {
		self.start();
		let mut total_steps = 0;
		let mut done = 0;

		loop {
			if done > 10 { break; }
			if self.done() {
				done += 1;
			} else {
				done = 0;
			}

			self.sync_step();
			self.route(disconnected.clone());

			total_steps += 1;
		}

		total_steps
	}

	/// Perform synchronization until complete.
	fn sync(&mut self) -> u32 {
		self.sync_with(None)
	}

	/// Perform synchronization until complete,
	/// excluding sync between certain nodes.
	fn sync_with_disconnected(&mut self, disconnected: HashSet<NodeIndex>) -> u32 {
		self.sync_with(Some(disconnected))
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

pub struct ForceFinalized(Arc<PeersClient>);

impl JustificationImport<Block> for ForceFinalized {
	type Error = ConsensusError;

	fn import_justification(
		&self,
		hash: H256,
		_number: NumberFor<Block>,
		justification: Justification,
	) -> Result<(), Self::Error> {
		self.0.finalize_block(BlockId::Hash(hash), Some(justification), true)
			.map_err(|_| ConsensusErrorKind::InvalidJustification.into())
	}
}

pub struct JustificationTestNet(TestNet);

impl TestNetFactory for JustificationTestNet {
	type Verifier = PassThroughVerifier;
	type PeerData = ();

	fn from_config(config: &ProtocolConfig) -> Self {
		JustificationTestNet(TestNet::from_config(config))
	}

	fn make_verifier(&self, client: Arc<PeersClient>, config: &ProtocolConfig)
		-> Arc<Self::Verifier>
	{
		self.0.make_verifier(client, config)
	}

	fn peer(&self, i: usize) -> &Peer<Self::Verifier, ()> {
		self.0.peer(i)
	}

	fn peers(&self) -> &Vec<Arc<Peer<Self::Verifier, ()>>> {
		self.0.peers()
	}

	fn mut_peers<F: Fn(&mut Vec<Arc<Peer<Self::Verifier, ()>>>)>(&mut self, closure: F ) {
		self.0.mut_peers(closure)
	}

	fn started(&self) -> bool {
		self.0.started()
	}

	fn set_started(&mut self, new: bool) {
		self.0.set_started(new)
	}

	fn make_block_import(&self, client: Arc<PeersClient>)
		-> (SharedBlockImport<Block>, Option<SharedJustificationImport<Block>>, Self::PeerData)
	{
		(client.clone(), Some(Arc::new(ForceFinalized(client))), Default::default())
	}
}
