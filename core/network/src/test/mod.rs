// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use std::sync::atomic::{AtomicBool, Ordering};
use std::thread;
use std::time::Duration;

use log::trace;
use client;
use client::block_builder::BlockBuilder;
use crate::config::ProtocolConfig;
use consensus::import_queue::{BasicQueue, ImportQueue, IncomingBlock};
use consensus::import_queue::{Link, SharedBlockImport, SharedJustificationImport, Verifier};
use consensus::{Error as ConsensusError, ErrorKind as ConsensusErrorKind};
use consensus::{BlockOrigin, ForkChoiceStrategy, ImportBlock, JustificationImport};
use crate::consensus_gossip::ConsensusGossip;
use crossbeam_channel::{self as channel, Sender, select};
use futures::Future;
use futures::sync::{mpsc, oneshot};
use crate::message::{Message, ConsensusEngineId};
use network_libp2p::{NodeIndex, ProtocolId, PeerId};
use parity_codec::Encode;
use parking_lot::{Mutex, RwLock};
use primitives::{H256, ed25519::Public as AuthorityId};
use crate::protocol::{ConnectedPeer, Context, FromNetworkMsg, Protocol, ProtocolMsg};
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{AuthorityIdFor, Block as BlockT, Digest, DigestItem, Header, NumberFor};
use runtime_primitives::Justification;
use crate::service::{network_channel, NetworkChan, NetworkLink, NetworkMsg, NetworkPort, TransactionPool};
use crate::specialization::NetworkSpecialization;
use test_client::{self, AccountKeyring};

pub use test_client::runtime::{Block, Extrinsic, Hash, Transfer};
pub use test_client::TestClient;

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
pub struct NoopLink { }

impl<B: BlockT> Link<B> for NoopLink { }

/// The test specialization.
#[derive(Clone)]
pub struct DummySpecialization;

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

#[derive(Clone)]
/// A Link that can wait for a block to have been imported.
pub struct TestLink<S: NetworkSpecialization<Block> + Clone> {
	import_done: Arc<AtomicBool>,
	hash: Arc<Mutex<Hash>>,
	link: NetworkLink<Block, S>,
}

impl<S: NetworkSpecialization<Block> + Clone> TestLink<S> {
	fn new(
		protocol_sender: Sender<ProtocolMsg<Block, S>>,
		network_sender: NetworkChan<Block>
	) -> TestLink<S> {
		TestLink {
			import_done: Arc::new(AtomicBool::new(false)),
			hash: Arc::new(Mutex::new(Default::default())),
			link: NetworkLink {
				protocol_sender,
				network_sender,
			}
		}
	}

	/// Set the hash which will be awaited for import.
	fn with_hash(&self, hash: Hash) {
		self.import_done.store(false, Ordering::SeqCst);
		*self.hash.lock() = hash;
	}

	/// Simulate a synchronous import.
	fn wait_for_import(&self) {
		while !self.import_done.load(Ordering::SeqCst) {
			thread::sleep(Duration::from_millis(20));
		}
	}
}

impl<S: NetworkSpecialization<Block> + Clone> Link<Block> for TestLink<S> {
	fn block_imported(&self, hash: &Hash, number: NumberFor<Block>) {
		if hash == &*self.hash.lock() {
			self.import_done.store(true, Ordering::SeqCst);
		}
		self.link.block_imported(hash, number);
	}

	fn blocks_processed(&self, processed_blocks: Vec<Hash>, has_error: bool) {
		self.link.blocks_processed(processed_blocks, has_error);
	}

	fn justification_imported(&self, who: NodeIndex, hash: &Hash, number:NumberFor<Block>, success: bool) {
		self.link.justification_imported(who, hash, number, success);
	}

	fn request_justification(&self, hash: &Hash, number: NumberFor<Block>) {
		self.link.request_justification(hash, number);
	}

	fn useless_peer(&self, who: NodeIndex, reason: &str) {
		self.link.useless_peer(who, reason);
	}

	fn note_useless_and_restart_sync(&self, who: NodeIndex, reason: &str) {
		self.link.note_useless_and_restart_sync(who, reason);
	}

	fn restart(&self) {
		self.link.restart();
	}
}

pub struct Peer<D, S: NetworkSpecialization<Block> + Clone> {
	pub is_offline: Arc<AtomicBool>,
	pub is_major_syncing: Arc<AtomicBool>,
	pub peers: Arc<RwLock<HashMap<NodeIndex, ConnectedPeer<Block>>>>,
	client: Arc<PeersClient>,
	network_to_protocol_sender: Sender<FromNetworkMsg<Block>>,
	pub protocol_sender: Sender<ProtocolMsg<Block, S>>,
	network_link: TestLink<S>,
	network_port: Arc<Mutex<NetworkPort<Block>>>,
	pub import_queue: Box<ImportQueue<Block>>,
	pub data: D,
	best_hash: Mutex<Option<H256>>,
	finalized_hash: Mutex<Option<H256>>,
}

impl<D, S: NetworkSpecialization<Block> + Clone> Peer<D, S> {
	fn new(
		is_offline: Arc<AtomicBool>,
		is_major_syncing: Arc<AtomicBool>,
		peers: Arc<RwLock<HashMap<NodeIndex, ConnectedPeer<Block>>>>,
		client: Arc<PeersClient>,
		import_queue: Box<ImportQueue<Block>>,
		network_to_protocol_sender: Sender<FromNetworkMsg<Block>>,
		protocol_sender: Sender<ProtocolMsg<Block, S>>,
		network_sender: NetworkChan<Block>,
		network_port: NetworkPort<Block>,
		data: D,
	) -> Self {
		let network_port = Arc::new(Mutex::new(network_port));
		let network_link = TestLink::new(protocol_sender.clone(), network_sender.clone());
		import_queue.start(Box::new(network_link.clone())).expect("Test ImportQueue always starts");
		Peer {
			is_offline,
			is_major_syncing,
			peers,
			client,
			network_to_protocol_sender,
			protocol_sender,
			import_queue,
			network_link,
			network_port,
			data,
			best_hash: Mutex::new(None),
			finalized_hash: Mutex::new(None),
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

	// SyncOracle: are we connected to any peer?
	fn is_offline(&self) -> bool {
		self.is_offline.load(Ordering::Relaxed)
	}

	// SyncOracle: are we in the process of catching-up with the chain?
	fn is_major_syncing(&self) -> bool {
		self.is_major_syncing.load(Ordering::Relaxed)
	}

	/// Called on connection to other indicated peer.
	fn on_connect(&self, other: NodeIndex) {
		let _ = self.network_to_protocol_sender.send(FromNetworkMsg::PeerConnected(PeerId::random(), other, String::new()));
	}

	/// Called on disconnect from other indicated peer.
	fn on_disconnect(&self, other: NodeIndex) {
		let _ = self
			.network_to_protocol_sender
			.send(FromNetworkMsg::PeerDisconnected(other, String::new()));
	}

	/// Receive a message from another peer. Return a set of peers to disconnect.
	fn receive_message(&self, from: NodeIndex, msg: Message<Block>) {
		let _ = self
			.network_to_protocol_sender
			.send(FromNetworkMsg::CustomMessage(from, msg));
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

		let mut best_hash = self.best_hash.lock();
		match *best_hash {
			None => {},
			Some(hash) if hash != info.chain.best_hash => {},
			_ => return,
		}

		let header = self.client.header(&BlockId::Hash(info.chain.best_hash)).unwrap().unwrap();
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::BlockImported(info.chain.best_hash, header));

		*best_hash = Some(info.chain.best_hash);
	}

	/// Send block finalization notifications.
	pub fn send_finality_notifications(&self) {
		let info = self.client.info().expect("In-mem client does not fail");

		let mut finalized_hash = self.finalized_hash.lock();
		match *finalized_hash {
			None => {},
			Some(hash) if hash != info.chain.finalized_hash => {},
			_ => return,
		}

		let header = self.client.header(&BlockId::Hash(info.chain.finalized_hash)).unwrap().unwrap();
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::BlockFinalized(info.chain.finalized_hash, header.clone()));

		*finalized_hash = Some(info.chain.finalized_hash);
	}

	/// Restart sync for a peer.
	fn restart_sync(&self) {
		let _ = self.protocol_sender.send(ProtocolMsg::Abort);
	}

	/// Push a message into the gossip network and relay to peers.
	/// `TestNet::sync_step` needs to be called to ensure it's propagated.
	pub fn gossip_message(&self, topic: <Block as BlockT>::Hash, engine_id: ConsensusEngineId, data: Vec<u8>) {
		let _ = self
			.protocol_sender
			.send(ProtocolMsg::GossipConsensusMessage(topic, engine_id, data));
	}

	pub fn consensus_gossip_collect_garbage_for_topic(&self, _topic: <Block as BlockT>::Hash) {
		self.with_gossip(move |gossip, _| gossip.collect_garbage())
	}

	/// access the underlying consensus gossip handler
	pub fn consensus_gossip_messages_for(
		&self,
		engine_id: ConsensusEngineId,
		topic: <Block as BlockT>::Hash,
	) -> mpsc::UnboundedReceiver<Vec<u8>> {
		let (tx, rx) = oneshot::channel();
		self.with_gossip(move |gossip, _| {
			let inner_rx = gossip.messages_for(engine_id, topic);
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
	pub fn generate_blocks<F>(&self, count: usize, origin: BlockOrigin, edit_block: F) -> H256
		where F: FnMut(BlockBuilder<Block, PeersClient>) -> Block
	{
		let best_hash = self.client.info().unwrap().chain.best_hash;
		self.generate_blocks_at(BlockId::Hash(best_hash), count, origin, edit_block)
	}

	/// Add blocks to the peer -- edit the block before adding. The chain will
	/// start at the given block iD.
	pub fn generate_blocks_at<F>(&self, at: BlockId<Block>, count: usize, origin: BlockOrigin, mut edit_block: F) -> H256
		where F: FnMut(BlockBuilder<Block, PeersClient>) -> Block
	{
		let mut at = self.client.header(&at).unwrap().unwrap().hash();
		for _  in 0..count {
			let builder = self.client.new_block_at(&BlockId::Hash(at)).unwrap();
			let block = edit_block(builder);
			let hash = block.header.hash();
			trace!(
				"Generating {}, (#{}, parent={})",
				hash,
				block.header.number,
				block.header.parent_hash
			);
			let header = block.header.clone();
			at = hash;
			self.network_link.with_hash(hash);
			self.import_queue.import_blocks(
				origin,
				vec![IncomingBlock {
					origin: None,
					hash,
					header: Some(header),
					body: Some(block.extrinsics),
					justification: None,
				}],
			);
			// Simulate a sync import.
			self.network_link.wait_for_import();
		}
		at
	}

	/// Push blocks to the peer (simplified: with or without a TX)
	pub fn push_blocks(&self, count: usize, with_tx: bool) -> H256 {
		let best_hash = self.client.info().unwrap().chain.best_hash;
		self.push_blocks_at(BlockId::Hash(best_hash), count, with_tx)
	}

	/// Push blocks to the peer (simplified: with or without a TX) starting from
	/// given hash.
	pub fn push_blocks_at(&self, at: BlockId<Block>, count: usize, with_tx: bool) -> H256 {
		let mut nonce = 0;
		if with_tx {
			self.generate_blocks_at(at, count, BlockOrigin::File, |mut builder| {
				let transfer = Transfer {
					from: AccountKeyring::Alice.into(),
					to: AccountKeyring::Alice.into(),
					amount: 1,
					nonce,
				};
				let signature = AccountKeyring::from_public(&transfer.from).unwrap().sign(&transfer.encode()).into();
				builder.push(Extrinsic::Transfer(transfer, signature)).unwrap();
				nonce = nonce + 1;
				builder.bake().unwrap()
			})
		} else {
			self.generate_blocks_at(at, count, BlockOrigin::File, |builder| builder.bake().unwrap())
		}
	}

	pub fn push_authorities_change_block(&self, new_authorities: Vec<AuthorityId>) -> H256 {
		self.generate_blocks(1, BlockOrigin::File, |mut builder| {
			builder.push(Extrinsic::AuthoritiesChange(new_authorities.clone())).unwrap();
			builder.bake().unwrap()
		})
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

pub trait SpecializationFactory {
    fn create() -> Self;
}

impl SpecializationFactory for DummySpecialization {
	fn create() -> DummySpecialization {
		DummySpecialization
	}
}

pub trait TestNetFactory: Sized {
	type Specialization: NetworkSpecialization<Block> + Clone + SpecializationFactory;
	type Verifier: 'static + Verifier<Block>;
	type PeerData: Default;

	/// These two need to be implemented!
	fn from_config(config: &ProtocolConfig) -> Self;
	fn make_verifier(&self, client: Arc<PeersClient>, config: &ProtocolConfig) -> Arc<Self::Verifier>;

	/// Get reference to peer.
	fn peer(&self, i: usize) -> &Peer<Self::PeerData, Self::Specialization>;
	fn peers(&self) -> &Vec<Arc<Peer<Self::PeerData, Self::Specialization>>>;
	fn mut_peers<F: FnOnce(&mut Vec<Arc<Peer<Self::PeerData, Self::Specialization>>>)>(&mut self, closure: F);

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

		let import_queue = Box::new(BasicQueue::new(verifier, block_import, justification_import));
		let status_sinks = Arc::new(Mutex::new(Vec::new()));
		let is_offline = Arc::new(AtomicBool::new(true));
		let is_major_syncing = Arc::new(AtomicBool::new(false));
		let specialization = self::SpecializationFactory::create();
		let peers: Arc<RwLock<HashMap<NodeIndex, ConnectedPeer<Block>>>> = Arc::new(Default::default());

		let (protocol_sender, network_to_protocol_sender) = Protocol::new(
			status_sinks,
			is_offline.clone(),
			is_major_syncing.clone(),
			peers.clone(),
			network_sender.clone(),
			config.clone(),
			client.clone(),
			import_queue.clone(),
			None,
			tx_pool,
			specialization,
		).unwrap();

		let peer = Arc::new(Peer::new(
			is_offline,
			is_major_syncing,
			peers,
			client,
			import_queue,
			network_to_protocol_sender,
			protocol_sender,
			network_sender,
			network_port,
			data,
		));

		self.mut_peers(|peers| {
			peers.push(peer)
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
			if done > 3 { break; }
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
	peers: Vec<Arc<Peer<(), DummySpecialization>>>,
	started: bool,
}

impl TestNetFactory for TestNet {
	type Specialization = DummySpecialization;
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

	fn peer(&self, i: usize) -> &Peer<(), Self::Specialization> {
		&self.peers[i]
	}

	fn peers(&self) -> &Vec<Arc<Peer<(), Self::Specialization>>> {
		&self.peers
	}

	fn mut_peers<F: FnOnce(&mut Vec<Arc<Peer<(), Self::Specialization>>>)>(&mut self, closure: F) {
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
	type Specialization = DummySpecialization;
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

	fn peer(&self, i: usize) -> &Peer<Self::PeerData, Self::Specialization> {
		self.0.peer(i)
	}

	fn peers(&self) -> &Vec<Arc<Peer<Self::PeerData, Self::Specialization>>> {
		self.0.peers()
	}

	fn mut_peers<F: FnOnce(&mut Vec<Arc<Peer<Self::PeerData, Self::Specialization>>>)>(&mut self, closure: F ) {
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
