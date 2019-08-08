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

use std::collections::HashMap;
use std::sync::Arc;

use crate::config::build_multiaddr;
use log::trace;
use crate::chain::FinalityProofProvider;
use client::{self, ClientInfo, BlockchainEvents, BlockImportNotification, FinalityNotifications, FinalityNotification};
use client::{in_mem::Backend as InMemoryBackend, error::Result as ClientResult};
use client::block_builder::BlockBuilder;
use client::backend::AuxStore;
use crate::config::Roles;
use consensus::import_queue::BasicQueue;
use consensus::import_queue::{
	BoxBlockImport, BoxJustificationImport, Verifier, BoxFinalityProofImport,
};
use consensus::block_import::{BlockImport, ImportResult};
use consensus::{Error as ConsensusError, well_known_cache_keys::{self, Id as CacheKeyId}};
use consensus::{BlockOrigin, ForkChoiceStrategy, BlockImportParams, JustificationImport};
use futures::prelude::*;
use futures03::{StreamExt as _, TryStreamExt as _};
use crate::{NetworkWorker, NetworkService, config::ProtocolId};
use crate::config::{NetworkConfiguration, TransportConfig, BoxFinalityProofRequestBuilder};
use libp2p::PeerId;
use parking_lot::Mutex;
use primitives::{H256, Blake2Hasher};
use crate::protocol::{Context, ProtocolConfig};
use sr_primitives::generic::{BlockId, OpaqueDigestItemId};
use sr_primitives::traits::{Block as BlockT, Header, NumberFor};
use sr_primitives::Justification;
use crate::service::TransactionPool;
use crate::specialization::NetworkSpecialization;
use test_client::{self, AccountKeyring};

pub use test_client::runtime::{Block, Extrinsic, Hash, Transfer};
pub use test_client::TestClient;

type AuthorityId = babe_primitives::AuthorityId;

#[cfg(any(test, feature = "test-helpers"))]
/// A Verifier that accepts all blocks and passes them on with the configured
/// finality to be imported.
pub struct PassThroughVerifier(pub bool);

#[cfg(any(test, feature = "test-helpers"))]
/// This `Verifier` accepts all data as valid.
impl<B: BlockT> Verifier<B> for PassThroughVerifier {
	fn verify(
		&mut self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Option<Justification>,
		body: Option<Vec<B::Extrinsic>>
	) -> Result<(BlockImportParams<B>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		let maybe_keys = header.digest()
			.log(|l| l.try_as_raw(OpaqueDigestItemId::Consensus(b"aura"))
				.or_else(|| l.try_as_raw(OpaqueDigestItemId::Consensus(b"babe")))
			)
			.map(|blob| vec![(well_known_cache_keys::AUTHORITIES, blob.to_vec())]);

		Ok((BlockImportParams {
			origin,
			header,
			body,
			finalized: self.0,
			justification,
			post_digests: vec![],
			auxiliary: Vec::new(),
			fork_choice: ForkChoiceStrategy::LongestChain,
		}, maybe_keys))
	}
}

/// The test specialization.
#[derive(Clone)]
pub struct DummySpecialization;

impl NetworkSpecialization<Block> for DummySpecialization {
	fn status(&self) -> Vec<u8> {
		vec![]
	}

	fn on_connect(
		&mut self,
		_ctx: &mut dyn Context<Block>,
		_peer_id: PeerId,
		_status: crate::message::Status<Block>
	) {}

	fn on_disconnect(&mut self, _ctx: &mut dyn Context<Block>, _peer_id: PeerId) {}

	fn on_message(
		&mut self,
		_ctx: &mut dyn Context<Block>,
		_peer_id: PeerId,
		_message: Vec<u8>,
	) {}

	fn on_event(
		&mut self,
		_event: crate::specialization::Event
	) {}
}

pub type PeersFullClient =
	client::Client<test_client::Backend, test_client::Executor, Block, test_client::runtime::RuntimeApi>;
pub type PeersLightClient =
	client::Client<test_client::LightBackend, test_client::LightExecutor, Block, test_client::runtime::RuntimeApi>;

#[derive(Clone)]
pub enum PeersClient {
	Full(Arc<PeersFullClient>),
	Light(Arc<PeersLightClient>),
}

impl PeersClient {
	pub fn as_full(&self) -> Option<Arc<PeersFullClient>> {
		match *self {
			PeersClient::Full(ref client) => Some(client.clone()),
			_ => None,
		}
	}

	pub fn as_block_import(&self) -> BoxBlockImport<Block> {
		match *self {
			PeersClient::Full(ref client) => Box::new(client.clone()) as _,
			PeersClient::Light(ref client) => Box::new(client.clone()) as _,
		}
	}

	pub fn as_in_memory_backend(&self) -> InMemoryBackend<Block, Blake2Hasher> {
		#[allow(deprecated)]
		match *self {
			PeersClient::Full(ref client) => client.backend().as_in_memory(),
			PeersClient::Light(_) => unimplemented!("TODO"),
		}
	}

	pub fn get_aux(&self, key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		#[allow(deprecated)]
		match *self {
			PeersClient::Full(ref client) => client.backend().get_aux(key),
			PeersClient::Light(ref client) => client.backend().get_aux(key),
		}
	}

	pub fn info(&self) -> ClientInfo<Block> {
		match *self {
			PeersClient::Full(ref client) => client.info(),
			PeersClient::Light(ref client) => client.info(),
		}
	}

	pub fn header(&self, block: &BlockId<Block>) -> ClientResult<Option<<Block as BlockT>::Header>> {
		match *self {
			PeersClient::Full(ref client) => client.header(block),
			PeersClient::Light(ref client) => client.header(block),
		}
	}

	pub fn justification(&self, block: &BlockId<Block>) -> ClientResult<Option<Justification>> {
		match *self {
			PeersClient::Full(ref client) => client.justification(block),
			PeersClient::Light(ref client) => client.justification(block),
		}
	}

	pub fn finality_notification_stream(&self) -> FinalityNotifications<Block> {
		match *self {
			PeersClient::Full(ref client) => client.finality_notification_stream(),
			PeersClient::Light(ref client) => client.finality_notification_stream(),
		}
	}

	pub fn finalize_block(
		&self,
		id: BlockId<Block>,
		justification: Option<Justification>,
		notify: bool
	) -> ClientResult<()> {
		match *self {
			PeersClient::Full(ref client) => client.finalize_block(id, justification, notify),
			PeersClient::Light(ref client) => client.finalize_block(id, justification, notify),
		}
	}
}

pub struct Peer<D, S: NetworkSpecialization<Block>> {
	pub data: D,
	client: PeersClient,
	/// We keep a copy of the verifier so that we can invoke it for locally-generated blocks,
	/// instead of going through the import queue.
	verifier: VerifierAdapter<dyn Verifier<Block>>,
	/// We keep a copy of the block_import so that we can invoke it for locally-generated blocks,
	/// instead of going through the import queue.
	block_import: Box<dyn BlockImport<Block, Error = ConsensusError>>,
	network: NetworkWorker<Block, S, <Block as BlockT>::Hash>,
	imported_blocks_stream: Box<dyn Stream<Item = BlockImportNotification<Block>, Error = ()> + Send>,
	finality_notification_stream: Box<dyn Stream<Item = FinalityNotification<Block>, Error = ()> + Send>,
}

impl<D, S: NetworkSpecialization<Block>> Peer<D, S> {
	/// Returns true if we're major syncing.
	pub fn is_major_syncing(&self) -> bool {
		self.network.service().is_major_syncing()
	}

	/// Returns the number of peers we're connected to.
	pub fn num_peers(&self) -> usize {
		self.network.num_connected_peers()
	}

	/// Returns true if we have no peer.
	pub fn is_offline(&self) -> bool {
		self.num_peers() == 0
	}

	/// Request a justification for the given block.
	pub fn request_justification(&self, hash: &<Block as BlockT>::Hash, number: NumberFor<Block>) {
		self.network.service().request_justification(hash, number);
	}

	/// Announces an important block on the network.
	pub fn announce_block(&self, hash: <Block as BlockT>::Hash) {
		self.network.service().announce_block(hash);
	}

	/// Add blocks to the peer -- edit the block before adding
	pub fn generate_blocks<F>(&mut self, count: usize, origin: BlockOrigin, edit_block: F) -> H256
		where F: FnMut(BlockBuilder<Block, PeersFullClient>) -> Block
	{
		let best_hash = self.client.info().chain.best_hash;
		self.generate_blocks_at(BlockId::Hash(best_hash), count, origin, edit_block)
	}

	/// Add blocks to the peer -- edit the block before adding. The chain will
	/// start at the given block iD.
	fn generate_blocks_at<F>(
		&mut self,
		at: BlockId<Block>,
		count: usize,
		origin: BlockOrigin,
		mut edit_block: F
	) -> H256 where F: FnMut(BlockBuilder<Block, PeersFullClient>) -> Block {
		let full_client = self.client.as_full().expect("blocks could only be generated by full clients");
		let mut at = full_client.header(&at).unwrap().unwrap().hash();
		for _  in 0..count {
			let builder = full_client.new_block_at(&BlockId::Hash(at), Default::default()
			).unwrap();
			let block = edit_block(builder);
			let hash = block.header.hash();
			trace!(
				target: "test_network",
				"Generating {}, (#{}, parent={})",
				hash,
				block.header.number,
				block.header.parent_hash
			);
			let header = block.header.clone();
			let (import_block, cache) = self.verifier.verify(
				origin,
				header.clone(),
				None,
				Some(block.extrinsics)
			).unwrap();
			let cache = if let Some(cache) = cache {
				cache.into_iter().collect()
			} else {
				Default::default()
			};
			self.block_import.import_block(import_block, cache).expect("block_import failed");
			self.network.on_block_imported(hash, header);
			at = hash;
		}

		self.network.service().announce_block(at.clone());
		at
	}

	/// Push blocks to the peer (simplified: with or without a TX)
	pub fn push_blocks(&mut self, count: usize, with_tx: bool) -> H256 {
		let best_hash = self.client.info().chain.best_hash;
		self.push_blocks_at(BlockId::Hash(best_hash), count, with_tx)
	}

	/// Push blocks to the peer (simplified: with or without a TX) starting from
	/// given hash.
	pub fn push_blocks_at(&mut self, at: BlockId<Block>, count: usize, with_tx: bool) -> H256 {
		let mut nonce = 0;
		if with_tx {
			self.generate_blocks_at(at, count, BlockOrigin::File, |mut builder| {
				let transfer = Transfer {
					from: AccountKeyring::Alice.into(),
					to: AccountKeyring::Alice.into(),
					amount: 1,
					nonce,
				};
				builder.push(transfer.into_signed_tx()).unwrap();
				nonce = nonce + 1;
				builder.bake().unwrap()
			})
		} else {
			self.generate_blocks_at(at, count, BlockOrigin::File, |builder| builder.bake().unwrap())
		}
	}

	pub fn push_authorities_change_block(&mut self, new_authorities: Vec<AuthorityId>) -> H256 {
		self.generate_blocks(1, BlockOrigin::File, |mut builder| {
			builder.push(Extrinsic::AuthoritiesChange(new_authorities.clone())).unwrap();
			builder.bake().unwrap()
		})
	}

	/// Get a reference to the client.
	pub fn client(&self) -> &PeersClient {
		&self.client
	}

	/// Get a reference to the network service.
	pub fn network_service(&self) -> &Arc<NetworkService<Block, S, <Block as BlockT>::Hash>> {
		&self.network.service()
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

/// Implements `BlockImport` on an `Arc<Mutex<impl BlockImport>>`. Used internally. Necessary to overcome the way the
/// `TestNet` trait is designed, more specifically `make_block_import` returning a `Box<BlockImport>` makes it
/// impossible to clone the underlying object.
struct BlockImportAdapter<T: ?Sized>(Arc<Mutex<Box<T>>>);

impl<T: ?Sized> Clone for BlockImportAdapter<T> {
	fn clone(&self) -> Self {
		BlockImportAdapter(self.0.clone())
	}
}

impl<T: ?Sized + BlockImport<Block>> BlockImport<Block> for BlockImportAdapter<T> {
	type Error = T::Error;

	fn check_block(&mut self, hash: Hash, parent_hash: Hash) -> Result<ImportResult, Self::Error> {
		self.0.lock().check_block(hash, parent_hash)
	}

	fn import_block(
		&mut self,
		block: BlockImportParams<Block>,
		cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		self.0.lock().import_block(block, cache)
	}
}

/// Implements `Verifier` on an `Arc<Mutex<impl Verifier>>`. Used internally.
struct VerifierAdapter<T: ?Sized>(Arc<Mutex<Box<T>>>);

impl<T: ?Sized> Clone for VerifierAdapter<T> {
	fn clone(&self) -> Self {
		VerifierAdapter(self.0.clone())
	}
}

impl<B: BlockT, T: ?Sized + Verifier<B>> Verifier<B> for VerifierAdapter<T> {
	fn verify(
		&mut self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Option<Justification>,
		body: Option<Vec<B::Extrinsic>>
	) -> Result<(BlockImportParams<B>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		self.0.lock().verify(origin, header, justification, body)
	}
}

pub trait TestNetFactory: Sized {
	type Specialization: NetworkSpecialization<Block> + SpecializationFactory;
	type Verifier: 'static + Verifier<Block>;
	type PeerData: Default;

	/// These two need to be implemented!
	fn from_config(config: &ProtocolConfig) -> Self;
	fn make_verifier(&self, client: PeersClient, config: &ProtocolConfig) -> Self::Verifier;

	/// Get reference to peer.
	fn peer(&mut self, i: usize) -> &mut Peer<Self::PeerData, Self::Specialization>;
	fn peers(&self) -> &Vec<Peer<Self::PeerData, Self::Specialization>>;
	fn mut_peers<F: FnOnce(&mut Vec<Peer<Self::PeerData, Self::Specialization>>)>(&mut self, closure: F);

	/// Get custom block import handle for fresh client, along with peer data.
	fn make_block_import(&self, client: PeersClient)
		-> (
			BoxBlockImport<Block>,
			Option<BoxJustificationImport<Block>>,
			Option<BoxFinalityProofImport<Block>>,
			Option<BoxFinalityProofRequestBuilder<Block>>,
			Self::PeerData,
		)
	{
		(client.as_block_import(), None, None, None, Default::default())
	}

	/// Get finality proof provider (if supported).
	fn make_finality_proof_provider(&self, _client: PeersClient) -> Option<Arc<dyn FinalityProofProvider<Block>>> {
		None
	}

	fn default_config() -> ProtocolConfig {
		ProtocolConfig::default()
	}

	/// Create new test network with this many peers.
	fn new(n: usize) -> Self {
		trace!(target: "test_network", "Creating test network");
		let config = Self::default_config();
		let mut net = Self::from_config(&config);

		for i in 0..n {
			trace!(target: "test_network", "Adding peer {}", i);
			net.add_full_peer(&config);
		}
		net
	}

	/// Add a full peer.
	fn add_full_peer(&mut self, config: &ProtocolConfig) {
		let client = Arc::new(test_client::new());
		let verifier = self.make_verifier(PeersClient::Full(client.clone()), config);
		let verifier = VerifierAdapter(Arc::new(Mutex::new(Box::new(verifier) as Box<_>)));
		let (block_import, justification_import, finality_proof_import, finality_proof_request_builder, data)
			= self.make_block_import(PeersClient::Full(client.clone()));
		let block_import = BlockImportAdapter(Arc::new(Mutex::new(block_import)));

		let import_queue = Box::new(BasicQueue::new(
			verifier.clone(),
			Box::new(block_import.clone()),
			justification_import,
			finality_proof_import,
		));

		let listen_addr = build_multiaddr![Memory(rand::random::<u64>())];

		let network = NetworkWorker::new(crate::config::Params {
			roles: config.roles,
			network_config: NetworkConfiguration {
				listen_addresses: vec![listen_addr.clone()],
				transport: TransportConfig::MemoryOnly,
				..NetworkConfiguration::default()
			},
			chain: client.clone(),
			finality_proof_provider: self.make_finality_proof_provider(PeersClient::Full(client.clone())),
			finality_proof_request_builder,
			on_demand: None,
			transaction_pool: Arc::new(EmptyTransactionPool),
			protocol_id: ProtocolId::from(&b"test-protocol-name"[..]),
			import_queue,
			specialization: self::SpecializationFactory::create(),
		}).unwrap();

		self.mut_peers(|peers| {
			for peer in peers.iter_mut() {
				peer.network.add_known_address(network.service().local_peer_id(), listen_addr.clone());
			}

			let imported_blocks_stream = Box::new(client.import_notification_stream()
				.map(|v| Ok::<_, ()>(v)).compat().fuse());
			let finality_notification_stream = Box::new(client.finality_notification_stream()
				.map(|v| Ok::<_, ()>(v)).compat().fuse());

			peers.push(Peer {
				data,
				client: PeersClient::Full(client),
				imported_blocks_stream,
				finality_notification_stream,
				block_import: Box::new(block_import),
				verifier,
				network,
			});
		});
	}

	/// Add a light peer.
	fn add_light_peer(&mut self, config: &ProtocolConfig) {
		let mut config = config.clone();
		config.roles = Roles::LIGHT;

		let client = Arc::new(test_client::new_light());
		let verifier = self.make_verifier(PeersClient::Light(client.clone()), &config);
		let verifier = VerifierAdapter(Arc::new(Mutex::new(Box::new(verifier) as Box<_>)));
		let (block_import, justification_import, finality_proof_import, finality_proof_request_builder, data)
			= self.make_block_import(PeersClient::Light(client.clone()));
		let block_import = BlockImportAdapter(Arc::new(Mutex::new(block_import)));

		let import_queue = Box::new(BasicQueue::new(
			verifier.clone(),
			Box::new(block_import.clone()),
			justification_import,
			finality_proof_import,
		));

		let listen_addr = build_multiaddr![Memory(rand::random::<u64>())];

		let network = NetworkWorker::new(crate::config::Params {
			roles: config.roles,
			network_config: NetworkConfiguration {
				listen_addresses: vec![listen_addr.clone()],
				transport: TransportConfig::MemoryOnly,
				..NetworkConfiguration::default()
			},
			chain: client.clone(),
			finality_proof_provider: self.make_finality_proof_provider(PeersClient::Light(client.clone())),
			finality_proof_request_builder,
			on_demand: None,
			transaction_pool: Arc::new(EmptyTransactionPool),
			protocol_id: ProtocolId::from(&b"test-protocol-name"[..]),
			import_queue,
			specialization: self::SpecializationFactory::create(),
		}).unwrap();

		self.mut_peers(|peers| {
			for peer in peers.iter_mut() {
				peer.network.add_known_address(network.service().local_peer_id(), listen_addr.clone());
			}

			let imported_blocks_stream = Box::new(client.import_notification_stream()
				.map(|v| Ok::<_, ()>(v)).compat().fuse());
			let finality_notification_stream = Box::new(client.finality_notification_stream()
				.map(|v| Ok::<_, ()>(v)).compat().fuse());

			peers.push(Peer {
				data,
				verifier,
				block_import: Box::new(block_import),
				client: PeersClient::Light(client),
				imported_blocks_stream,
				finality_notification_stream,
				network,
			});
		});
	}

	/// Polls the testnet until all nodes are in sync.
	///
	/// Must be executed in a task context.
	fn poll_until_sync(&mut self) -> Async<()> {
		self.poll();

		// Return `NotReady` if there's a mismatch in the highest block number.
		let mut highest = None;
		for peer in self.peers().iter() {
			if peer.is_major_syncing() || peer.network.num_queued_blocks() != 0 {
				return Async::NotReady
			}
			match (highest, peer.client.info().chain.best_number) {
				(None, b) => highest = Some(b),
				(Some(ref a), ref b) if a == b => {},
				(Some(_), _) => return Async::NotReady,
			}
		}
		Async::Ready(())
	}

	/// Blocks the current thread until we are sync'ed.
	///
	/// Calls `poll_until_sync` repeatidely with the runtime passed as parameter.
	fn block_until_sync(&mut self, runtime: &mut tokio::runtime::current_thread::Runtime) {
		runtime.block_on(futures::future::poll_fn::<(), (), _>(|| Ok(self.poll_until_sync()))).unwrap();
	}

	/// Polls the testnet. Processes all the pending actions and returns `NotReady`.
	fn poll(&mut self) {
		self.mut_peers(|peers| {
			for peer in peers {
				peer.network.poll().unwrap();

				// We poll `imported_blocks_stream`.
				while let Ok(Async::Ready(Some(notification))) = peer.imported_blocks_stream.poll() {
					peer.network.on_block_imported(notification.hash, notification.header);
				}

				// We poll `finality_notification_stream`, but we only take the last event.
				let mut last = None;
				while let Ok(Async::Ready(Some(item))) = peer.finality_notification_stream.poll() {
					last = Some(item);
				}
				if let Some(notification) = last {
					peer.network.on_block_finalized(notification.hash, notification.header);
				}
			}
		});
	}
}

pub struct TestNet {
	peers: Vec<Peer<(), DummySpecialization>>,
}

impl TestNetFactory for TestNet {
	type Specialization = DummySpecialization;
	type Verifier = PassThroughVerifier;
	type PeerData = ();

	/// Create new test network with peers and given config.
	fn from_config(_config: &ProtocolConfig) -> Self {
		TestNet {
			peers: Vec::new(),
		}
	}

	fn make_verifier(&self, _client: PeersClient, _config: &ProtocolConfig)
		-> Self::Verifier
	{
		PassThroughVerifier(false)
	}

	fn peer(&mut self, i: usize) -> &mut Peer<(), Self::Specialization> {
		&mut self.peers[i]
	}

	fn peers(&self) -> &Vec<Peer<(), Self::Specialization>> {
		&self.peers
	}

	fn mut_peers<F: FnOnce(&mut Vec<Peer<(), Self::Specialization>>)>(&mut self, closure: F) {
		closure(&mut self.peers);
	}
}

pub struct ForceFinalized(PeersClient);

impl JustificationImport<Block> for ForceFinalized {
	type Error = ConsensusError;

	fn import_justification(
		&mut self,
		hash: H256,
		_number: NumberFor<Block>,
		justification: Justification,
	) -> Result<(), Self::Error> {
		self.0.finalize_block(BlockId::Hash(hash), Some(justification), true)
			.map_err(|_| ConsensusError::InvalidJustification.into())
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

	fn make_verifier(&self, client: PeersClient, config: &ProtocolConfig) -> Self::Verifier {
		self.0.make_verifier(client, config)
	}

	fn peer(&mut self, i: usize) -> &mut Peer<Self::PeerData, Self::Specialization> {
		self.0.peer(i)
	}

	fn peers(&self) -> &Vec<Peer<Self::PeerData, Self::Specialization>> {
		self.0.peers()
	}

	fn mut_peers<F: FnOnce(&mut Vec<Peer<Self::PeerData, Self::Specialization>>)>(&mut self, closure: F) {
		self.0.mut_peers(closure)
	}

	fn make_block_import(&self, client: PeersClient)
		-> (
			BoxBlockImport<Block>,
			Option<BoxJustificationImport<Block>>,
			Option<BoxFinalityProofImport<Block>>,
			Option<BoxFinalityProofRequestBuilder<Block>>,
			Self::PeerData,
		)
	{
		(client.as_block_import(), Some(Box::new(ForceFinalized(client))), None, None, Default::default())
	}
}
