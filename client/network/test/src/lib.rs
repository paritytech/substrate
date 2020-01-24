// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

use std::{collections::HashMap, pin::Pin, sync::Arc, marker::PhantomData};

use libp2p::build_multiaddr;
use log::trace;
use sc_network::FinalityProofProvider;
use sp_blockchain::{
	Result as ClientResult, well_known_cache_keys::{self, Id as CacheKeyId}, Info as BlockchainInfo,
};
use sc_client_api::{
	BlockchainEvents, BlockImportNotification,
	FinalityNotifications, ImportNotifications,
	FinalityNotification,
	backend::{TransactionFor, AuxStore, Backend, Finalizer},
};
use sc_block_builder::BlockBuilder;
use sc_client::LongestChain;
use sc_network::config::Roles;
use sp_consensus::block_validation::DefaultBlockAnnounceValidator;
use sp_consensus::import_queue::{
	BasicQueue, BoxJustificationImport, Verifier, BoxFinalityProofImport,
};
use sp_consensus::block_import::{BlockImport, ImportResult};
use sp_consensus::Error as ConsensusError;
use sp_consensus::{BlockOrigin, ForkChoiceStrategy, BlockImportParams, BlockCheckParams, JustificationImport};
use futures::prelude::*;
use futures03::{Future as _, FutureExt as _, TryFutureExt as _, StreamExt as _, TryStreamExt as _};
use sc_network::{NetworkWorker, NetworkStateInfo, NetworkService, ReportHandle, config::ProtocolId};
use sc_network::config::{NetworkConfiguration, TransportConfig, BoxFinalityProofRequestBuilder};
use libp2p::PeerId;
use parking_lot::Mutex;
use sp_core::H256;
use sc_network::{Context, ProtocolConfig};
use sp_runtime::generic::{BlockId, OpaqueDigestItemId};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, NumberFor};
use sp_runtime::Justification;
use sc_network::TransactionPool;
use sc_network::specialization::NetworkSpecialization;
use substrate_test_runtime_client::{self, AccountKeyring};

pub use substrate_test_runtime_client::runtime::{Block, Extrinsic, Hash, Transfer};
pub use substrate_test_runtime_client::{TestClient, TestClientBuilder, TestClientBuilderExt};
pub use sc_network::specialization::DummySpecialization;

type AuthorityId = sp_consensus_babe::AuthorityId;

/// A Verifier that accepts all blocks and passes them on with the configured
/// finality to be imported.
#[derive(Clone)]
pub struct PassThroughVerifier(pub bool);

/// This `Verifier` accepts all data as valid.
impl<B: BlockT> Verifier<B> for PassThroughVerifier {
	fn verify(
		&mut self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Option<Justification>,
		body: Option<Vec<B::Extrinsic>>
	) -> Result<(BlockImportParams<B, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		let maybe_keys = header.digest()
			.log(|l| l.try_as_raw(OpaqueDigestItemId::Consensus(b"aura"))
				.or_else(|| l.try_as_raw(OpaqueDigestItemId::Consensus(b"babe")))
			)
			.map(|blob| vec![(well_known_cache_keys::AUTHORITIES, blob.to_vec())]);

		Ok((BlockImportParams {
			origin,
			header,
			body,
			storage_changes: None,
			finalized: self.0,
			justification,
			post_digests: vec![],
			auxiliary: Vec::new(),
			fork_choice: ForkChoiceStrategy::LongestChain,
			allow_missing_state: false,
			import_existing: false,
		}, maybe_keys))
	}
}

pub type PeersFullClient =
	sc_client::Client<substrate_test_runtime_client::Backend, substrate_test_runtime_client::Executor, Block, substrate_test_runtime_client::runtime::RuntimeApi>;
pub type PeersLightClient =
	sc_client::Client<substrate_test_runtime_client::LightBackend, substrate_test_runtime_client::LightExecutor, Block, substrate_test_runtime_client::runtime::RuntimeApi>;

#[derive(Clone)]
pub enum PeersClient {
	Full(Arc<PeersFullClient>, Arc<substrate_test_runtime_client::Backend>),
	Light(Arc<PeersLightClient>, Arc<substrate_test_runtime_client::LightBackend>),
}

impl PeersClient {
	pub fn as_full(&self) -> Option<Arc<PeersFullClient>> {
		match *self {
			PeersClient::Full(ref client, ref _backend) => Some(client.clone()),
			_ => None,
		}
	}

	pub fn as_block_import<Transaction>(&self) -> BlockImportAdapter<Transaction> {
		match *self {
			PeersClient::Full(ref client, ref _backend) =>
				BlockImportAdapter::new_full(client.clone()),
			PeersClient::Light(ref client, ref _backend) =>
				BlockImportAdapter::Light(Arc::new(Mutex::new(client.clone())), PhantomData),
		}
	}

	pub fn get_aux(&self, key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		match *self {
			PeersClient::Full(ref client, ref _backend) => client.get_aux(key),
			PeersClient::Light(ref client, ref _backend) => client.get_aux(key),
		}
	}

	pub fn info(&self) -> BlockchainInfo<Block> {
		match *self {
			PeersClient::Full(ref client, ref _backend) => client.chain_info(),
			PeersClient::Light(ref client, ref _backend) => client.chain_info(),
		}
	}

	pub fn header(&self, block: &BlockId<Block>) -> ClientResult<Option<<Block as BlockT>::Header>> {
		match *self {
			PeersClient::Full(ref client, ref _backend) => client.header(block),
			PeersClient::Light(ref client, ref _backend) => client.header(block),
		}
	}

	pub fn justification(&self, block: &BlockId<Block>) -> ClientResult<Option<Justification>> {
		match *self {
			PeersClient::Full(ref client, ref _backend) => client.justification(block),
			PeersClient::Light(ref client, ref _backend) => client.justification(block),
		}
	}

	pub fn finality_notification_stream(&self) -> FinalityNotifications<Block> {
		match *self {
			PeersClient::Full(ref client, ref _backend) => client.finality_notification_stream(),
			PeersClient::Light(ref client, ref _backend) => client.finality_notification_stream(),
		}
	}

	pub fn import_notification_stream(&self) -> ImportNotifications<Block>{
		match *self {
			PeersClient::Full(ref client, ref _backend) => client.import_notification_stream(),
			PeersClient::Light(ref client, ref _backend) => client.import_notification_stream(),
		}
	}

	pub fn finalize_block(
		&self,
		id: BlockId<Block>,
		justification: Option<Justification>,
		notify: bool
	) -> ClientResult<()> {
		match *self {
			PeersClient::Full(ref client, ref _backend) => client.finalize_block(id, justification, notify),
			PeersClient::Light(ref client, ref _backend) => client.finalize_block(id, justification, notify),
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
	block_import: BlockImportAdapter<()>,
	select_chain: Option<LongestChain<substrate_test_runtime_client::Backend, Block>>,
	backend: Option<Arc<substrate_test_runtime_client::Backend>>,
	network: NetworkWorker<Block, S, <Block as BlockT>::Hash>,
	imported_blocks_stream: Box<dyn Stream<Item = BlockImportNotification<Block>, Error = ()> + Send>,
	finality_notification_stream: Box<dyn Stream<Item = FinalityNotification<Block>, Error = ()> + Send>,
}

impl<D, S: NetworkSpecialization<Block>> Peer<D, S> {
	/// Get this peer ID.
	pub fn id(&self) -> PeerId {
		self.network.service().local_peer_id()
	}

	/// Returns true if we're major syncing.
	pub fn is_major_syncing(&self) -> bool {
		self.network.service().is_major_syncing()
	}

	// Returns a clone of the local SelectChain, only available on full nodes
	pub fn select_chain(&self) -> Option<LongestChain<substrate_test_runtime_client::Backend, Block>> {
		self.select_chain.clone()
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
	pub fn announce_block(&self, hash: <Block as BlockT>::Hash, data: Vec<u8>) {
		self.network.service().announce_block(hash, data);
	}

	/// Request explicit fork sync.
	pub fn set_sync_fork_request(&self, peers: Vec<PeerId>, hash: <Block as BlockT>::Hash, number: NumberFor<Block>) {
		self.network.service().set_sync_fork_request(peers, hash, number);
	}

	/// Add blocks to the peer -- edit the block before adding
	pub fn generate_blocks<F>(&mut self, count: usize, origin: BlockOrigin, edit_block: F) -> H256
		where F: FnMut(BlockBuilder<Block, PeersFullClient, substrate_test_runtime_client::Backend>) -> Block
	{
		let best_hash = self.client.info().best_hash;
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
	) -> H256 where F: FnMut(BlockBuilder<Block, PeersFullClient, substrate_test_runtime_client::Backend>) -> Block {
		let full_client = self.client.as_full()
			.expect("blocks could only be generated by full clients");
		let mut at = full_client.header(&at).unwrap().unwrap().hash();
		for _  in 0..count {
			let builder = full_client.new_block_at(
				&BlockId::Hash(at),
				Default::default(),
				false,
			).unwrap();
			let block = edit_block(builder);
			let hash = block.header.hash();
			trace!(
				target: "test_network",
				"Generating {}, (#{}, parent={})",
				hash,
				block.header.number,
				block.header.parent_hash,
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
			self.network.on_block_imported(hash, header, Vec::new(), true);
			at = hash;
		}

		self.network.service().announce_block(at.clone(), Vec::new());
		at
	}

	/// Push blocks to the peer (simplified: with or without a TX)
	pub fn push_blocks(&mut self, count: usize, with_tx: bool) -> H256 {
		let best_hash = self.client.info().best_hash;
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
				builder.build().unwrap().block
			})
		} else {
			self.generate_blocks_at(
				at,
				count,
				BlockOrigin::File,
				|builder| builder.build().unwrap().block,
			)
		}
	}

	pub fn push_authorities_change_block(&mut self, new_authorities: Vec<AuthorityId>) -> H256 {
		self.generate_blocks(1, BlockOrigin::File, |mut builder| {
			builder.push(Extrinsic::AuthoritiesChange(new_authorities.clone())).unwrap();
			builder.build().unwrap().block
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

	/// Test helper to compare the blockchain state of multiple (networked)
	/// clients.
	/// Potentially costly, as it creates in-memory copies of both blockchains in order
	/// to compare them. If you have easier/softer checks that are sufficient, e.g.
	/// by using .info(), you should probably use it instead of this.
	pub fn blockchain_canon_equals(&self, other: &Self) -> bool {
		if let (Some(mine), Some(others)) = (self.backend.clone(), other.backend.clone()) {
			mine.as_in_memory().blockchain()
				.canon_equals_to(others.as_in_memory().blockchain())
		} else {
			false
		}
	}

	/// Count the total number of imported blocks.
	pub fn blocks_count(&self) -> u64 {
		self.backend.as_ref().map(
			|backend| backend.blocks_count()
		).unwrap_or(0)
	}
}

pub struct EmptyTransactionPool;

impl TransactionPool<Hash, Block> for EmptyTransactionPool {
	fn transactions(&self) -> Vec<(Hash, Extrinsic)> {
		Vec::new()
	}

	fn hash_of(&self, _transaction: &Extrinsic) -> Hash {
		Hash::default()
	}

	fn import(
		&self,
		_report_handle: ReportHandle,
		_who: PeerId,
		_rep_change_good: sc_network::ReputationChange,
		_rep_change_bad: sc_network::ReputationChange,
		_transaction: Extrinsic
	) {}

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

/// Implements `BlockImport` for any `Transaction`. Internally the transaction is
/// "converted", aka the field is set to `None`.
///
/// This is required as the `TestNetFactory` trait does not distinguish between
/// full and light nodes.
pub enum BlockImportAdapter<Transaction> {
	Full(
		Arc<Mutex<dyn BlockImport<
			Block,
			Transaction = TransactionFor<substrate_test_runtime_client::Backend, Block>,
			Error = ConsensusError
		> + Send>>,
		PhantomData<Transaction>,
	),
	Light(
		Arc<Mutex<dyn BlockImport<
			Block,
			Transaction = TransactionFor<substrate_test_runtime_client::LightBackend, Block>,
			Error = ConsensusError
		> + Send>>,
		PhantomData<Transaction>,
	),
}

impl<Transaction> BlockImportAdapter<Transaction> {
	/// Create a new instance of `Self::Full`.
	pub fn new_full(
		full: impl BlockImport<
			Block,
			Transaction = TransactionFor<substrate_test_runtime_client::Backend, Block>,
			Error = ConsensusError
		>
		+ 'static
		+ Send
	) -> Self {
		Self::Full(Arc::new(Mutex::new(full)), PhantomData)
	}

	/// Create a new instance of `Self::Light`.
	pub fn new_light(
		light: impl BlockImport<
			Block,
			Transaction = TransactionFor<substrate_test_runtime_client::LightBackend, Block>,
			Error = ConsensusError
		>
		+ 'static
		+ Send
	) -> Self {
		Self::Light(Arc::new(Mutex::new(light)), PhantomData)
	}
}

impl<Transaction> Clone for BlockImportAdapter<Transaction> {
	fn clone(&self) -> Self {
		match self {
			Self::Full(full, _) => Self::Full(full.clone(), PhantomData),
			Self::Light(light, _) => Self::Light(light.clone(), PhantomData),
		}
	}
}

impl<Transaction> BlockImport<Block> for BlockImportAdapter<Transaction> {
	type Error = ConsensusError;
	type Transaction = Transaction;

	fn check_block(
		&mut self,
		block: BlockCheckParams<Block>,
	) -> Result<ImportResult, Self::Error> {
		match self {
			Self::Full(full, _) => full.lock().check_block(block),
			Self::Light(light, _) => light.lock().check_block(block),
		}
	}

	fn import_block(
		&mut self,
		block: BlockImportParams<Block, Transaction>,
		cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		match self {
			Self::Full(full, _) => full.lock().import_block(block.convert_transaction(), cache),
			Self::Light(light, _) => light.lock().import_block(block.convert_transaction(), cache),
		}
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
	) -> Result<(BlockImportParams<B, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		self.0.lock().verify(origin, header, justification, body)
	}
}

pub trait TestNetFactory: Sized {
	type Specialization: NetworkSpecialization<Block> + SpecializationFactory;
	type Verifier: 'static + Verifier<Block>;
	type PeerData: Default;

	/// These two need to be implemented!
	fn from_config(config: &ProtocolConfig) -> Self;
	fn make_verifier(
		&self,
		client: PeersClient,
		config: &ProtocolConfig,
		peer_data: &Self::PeerData,
	) -> Self::Verifier;

	/// Get reference to peer.
	fn peer(&mut self, i: usize) -> &mut Peer<Self::PeerData, Self::Specialization>;
	fn peers(&self) -> &Vec<Peer<Self::PeerData, Self::Specialization>>;
	fn mut_peers<F: FnOnce(&mut Vec<Peer<Self::PeerData, Self::Specialization>>)>(
		&mut self,
		closure: F,
	);

	/// Get custom block import handle for fresh client, along with peer data.
	fn make_block_import<Transaction>(&self, client: PeersClient)
		-> (
			BlockImportAdapter<Transaction>,
			Option<BoxJustificationImport<Block>>,
			Option<BoxFinalityProofImport<Block>>,
			Option<BoxFinalityProofRequestBuilder<Block>>,
			Self::PeerData,
		)
	{
		(client.as_block_import(), None, None, None, Default::default())
	}

	/// Get finality proof provider (if supported).
	fn make_finality_proof_provider(
		&self,
		_client: PeersClient,
	) -> Option<Arc<dyn FinalityProofProvider<Block>>> {
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

	fn add_full_peer(&mut self, config: &ProtocolConfig) {
		self.add_full_peer_with_states(config, None)
	}

	/// Add a full peer.
	fn add_full_peer_with_states(&mut self, config: &ProtocolConfig, keep_blocks: Option<u32>) {
		let test_client_builder = match keep_blocks {
			Some(keep_blocks) => TestClientBuilder::with_pruning_window(keep_blocks),
			None => TestClientBuilder::with_default_backend(),
		};
		let backend = test_client_builder.backend();
		let (c, longest_chain) = test_client_builder.build_with_longest_chain();
		let client = Arc::new(c);

		let (
			block_import,
			justification_import,
			finality_proof_import,
			finality_proof_request_builder,
			data,
		) = self.make_block_import(PeersClient::Full(client.clone(), backend.clone()));

		let verifier = self.make_verifier(
			PeersClient::Full(client.clone(), backend.clone()),
			config,
			&data,
		);
		let verifier = VerifierAdapter(Arc::new(Mutex::new(Box::new(verifier) as Box<_>)));

		let import_queue = Box::new(BasicQueue::new(
			verifier.clone(),
			Box::new(block_import.clone()),
			justification_import,
			finality_proof_import,
		));

		let listen_addr = build_multiaddr![Memory(rand::random::<u64>())];

		let network = NetworkWorker::new(sc_network::config::Params {
			roles: config.roles,
			network_config: NetworkConfiguration {
				listen_addresses: vec![listen_addr.clone()],
				transport: TransportConfig::MemoryOnly,
				..NetworkConfiguration::default()
			},
			chain: client.clone(),
			finality_proof_provider: self.make_finality_proof_provider(
				PeersClient::Full(client.clone(), backend.clone()),
			),
			finality_proof_request_builder,
			on_demand: None,
			transaction_pool: Arc::new(EmptyTransactionPool),
			protocol_id: ProtocolId::from(&b"test-protocol-name"[..]),
			import_queue,
			specialization: self::SpecializationFactory::create(),
			block_announce_validator: Box::new(DefaultBlockAnnounceValidator::new(client.clone()))
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
				client: PeersClient::Full(client, backend.clone()),
				select_chain: Some(longest_chain),
				backend: Some(backend),
				imported_blocks_stream,
				finality_notification_stream,
				block_import,
				verifier,
				network,
			});
		});
	}

	/// Add a light peer.
	fn add_light_peer(&mut self, config: &ProtocolConfig) {
		let mut config = config.clone();
		config.roles = Roles::LIGHT;

		let (c, backend) = substrate_test_runtime_client::new_light();
		let client = Arc::new(c);
		let (
			block_import,
			justification_import,
			finality_proof_import,
			finality_proof_request_builder,
			data,
		) = self.make_block_import(PeersClient::Light(client.clone(), backend.clone()));

		let verifier = self.make_verifier(
			PeersClient::Light(client.clone(), backend.clone()),
			&config,
			&data,
		);
		let verifier = VerifierAdapter(Arc::new(Mutex::new(Box::new(verifier) as Box<_>)));

		let import_queue = Box::new(BasicQueue::new(
			verifier.clone(),
			Box::new(block_import.clone()),
			justification_import,
			finality_proof_import,
		));

		let listen_addr = build_multiaddr![Memory(rand::random::<u64>())];

		let network = NetworkWorker::new(sc_network::config::Params {
			roles: config.roles,
			network_config: NetworkConfiguration {
				listen_addresses: vec![listen_addr.clone()],
				transport: TransportConfig::MemoryOnly,
				..NetworkConfiguration::default()
			},
			chain: client.clone(),
			finality_proof_provider: self.make_finality_proof_provider(
				PeersClient::Light(client.clone(), backend.clone())
			),
			finality_proof_request_builder,
			on_demand: None,
			transaction_pool: Arc::new(EmptyTransactionPool),
			protocol_id: ProtocolId::from(&b"test-protocol-name"[..]),
			import_queue,
			specialization: self::SpecializationFactory::create(),
			block_announce_validator: Box::new(DefaultBlockAnnounceValidator::new(client.clone()))
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
				select_chain: None,
				backend: None,
				block_import,
				client: PeersClient::Light(client, backend),
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
			if peer.network.num_sync_requests() != 0 {
				return Async::NotReady
			}
			match (highest, peer.client.info().best_hash) {
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
				trace!(target: "sync", "-- Polling {}", peer.id());
				futures03::future::poll_fn(|cx| Pin::new(&mut peer.network).poll(cx))
					.map(|item| Ok::<_, ()>(item))
					.compat().poll().unwrap();
				trace!(target: "sync", "-- Polling complete {}", peer.id());

				// We poll `imported_blocks_stream`.
				while let Ok(Async::Ready(Some(notification))) = peer.imported_blocks_stream.poll() {
					peer.network.on_block_imported(
						notification.hash,
						notification.header,
						Vec::new(),
						true,
					);
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

	fn make_verifier(&self, _client: PeersClient, _config: &ProtocolConfig, _peer_data: &())
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

	fn make_verifier(&self, client: PeersClient, config: &ProtocolConfig, peer_data: &()) -> Self::Verifier {
		self.0.make_verifier(client, config, peer_data)
	}

	fn peer(&mut self, i: usize) -> &mut Peer<Self::PeerData, Self::Specialization> {
		self.0.peer(i)
	}

	fn peers(&self) -> &Vec<Peer<Self::PeerData, Self::Specialization>> {
		self.0.peers()
	}

	fn mut_peers<F: FnOnce(
		&mut Vec<Peer<Self::PeerData,
		Self::Specialization>>,
	)>(&mut self, closure: F) {
		self.0.mut_peers(closure)
	}

	fn make_block_import<Transaction>(&self, client: PeersClient)
		-> (
			BlockImportAdapter<Transaction>,
			Option<BoxJustificationImport<Block>>,
			Option<BoxFinalityProofImport<Block>>,
			Option<BoxFinalityProofRequestBuilder<Block>>,
			Self::PeerData,
		)
	{
		(
			client.as_block_import(),
			Some(Box::new(ForceFinalized(client))),
			None,
			None,
			Default::default(),
		)
	}
}
