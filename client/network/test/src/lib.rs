// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.
#![allow(missing_docs)]

#[cfg(test)]
mod block_import;
#[cfg(test)]
mod sync;

use std::{
	collections::HashMap,
	marker::PhantomData,
	pin::Pin,
	sync::Arc,
	task::{Context as FutureContext, Poll},
	time::Duration,
};

use futures::{channel::oneshot, future::BoxFuture, pin_mut, prelude::*};
use libp2p::{build_multiaddr, PeerId};
use log::trace;
use parking_lot::Mutex;
use sc_block_builder::{BlockBuilder, BlockBuilderProvider};
use sc_client_api::{
	backend::{AuxStore, Backend, Finalizer, TransactionFor},
	BlockBackend, BlockImportNotification, BlockchainEvents, FinalityNotification,
	FinalityNotifications, ImportNotifications,
};
use sc_consensus::{
	BasicQueue, BlockCheckParams, BlockImport, BlockImportParams, BoxJustificationImport,
	ForkChoiceStrategy, ImportQueue, ImportResult, JustificationImport, JustificationSyncLink,
	LongestChain, Verifier,
};
use sc_network::{
	config::{NetworkConfiguration, RequestResponseConfig, Role, SyncMode},
	Multiaddr, NetworkService, NetworkWorker,
};
use sc_network_common::{
	config::{
		MultiaddrWithPeerId, NonDefaultSetConfig, NonReservedPeerMode, ProtocolId, TransportConfig,
	},
	protocol::{role::Roles, ProtocolName},
	service::{NetworkBlock, NetworkStateInfo, NetworkSyncForkRequest},
	sync::warp::{
		AuthorityList, EncodedProof, SetId, VerificationResult, WarpSyncParams, WarpSyncProvider,
	},
};
use sc_network_light::light_client_requests::handler::LightClientRequestHandler;
use sc_network_sync::{
	block_request_handler::BlockRequestHandler, service::network::NetworkServiceProvider,
	state_request_handler::StateRequestHandler, warp_request_handler, ChainSync,
};
use sc_service::client::Client;
use sp_blockchain::{
	well_known_cache_keys::{self, Id as CacheKeyId},
	Backend as BlockchainBackend, HeaderBackend, Info as BlockchainInfo, Result as ClientResult,
};
use sp_consensus::{
	block_validation::{BlockAnnounceValidator, DefaultBlockAnnounceValidator},
	BlockOrigin, Error as ConsensusError, SyncOracle,
};
use sp_core::H256;
use sp_runtime::{
	codec::{Decode, Encode},
	generic::{BlockId, OpaqueDigestItemId},
	traits::{Block as BlockT, Header as HeaderT, NumberFor},
	Justification, Justifications,
};
use substrate_test_runtime_client::AccountKeyring;
pub use substrate_test_runtime_client::{
	runtime::{Block, Extrinsic, Hash, Header, Transfer},
	TestClient, TestClientBuilder, TestClientBuilderExt,
};
use tokio::time::timeout;

type AuthorityId = sp_consensus_babe::AuthorityId;

/// A Verifier that accepts all blocks and passes them on with the configured
/// finality to be imported.
#[derive(Clone)]
pub struct PassThroughVerifier {
	finalized: bool,
}

impl PassThroughVerifier {
	/// Create a new instance.
	///
	/// Every verified block will use `finalized` for the `BlockImportParams`.
	pub fn new(finalized: bool) -> Self {
		Self { finalized }
	}
}

/// This `Verifier` accepts all data as valid.
#[async_trait::async_trait]
impl<B: BlockT> Verifier<B> for PassThroughVerifier {
	async fn verify(
		&mut self,
		mut block: BlockImportParams<B, ()>,
	) -> Result<(BlockImportParams<B, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		let maybe_keys = block
			.header
			.digest()
			.log(|l| {
				l.try_as_raw(OpaqueDigestItemId::Consensus(b"aura"))
					.or_else(|| l.try_as_raw(OpaqueDigestItemId::Consensus(b"babe")))
			})
			.map(|blob| vec![(well_known_cache_keys::AUTHORITIES, blob.to_vec())]);
		if block.fork_choice.is_none() {
			block.fork_choice = Some(ForkChoiceStrategy::LongestChain);
		};
		block.finalized = self.finalized;
		Ok((block, maybe_keys))
	}
}

pub type PeersFullClient = Client<
	substrate_test_runtime_client::Backend,
	substrate_test_runtime_client::ExecutorDispatch,
	Block,
	substrate_test_runtime_client::runtime::RuntimeApi,
>;

#[derive(Clone)]
pub struct PeersClient {
	client: Arc<PeersFullClient>,
	backend: Arc<substrate_test_runtime_client::Backend>,
}

impl PeersClient {
	pub fn as_client(&self) -> Arc<PeersFullClient> {
		self.client.clone()
	}

	pub fn as_backend(&self) -> Arc<substrate_test_runtime_client::Backend> {
		self.backend.clone()
	}

	pub fn as_block_import(&self) -> BlockImportAdapter<Self> {
		BlockImportAdapter::new(self.clone())
	}

	pub fn get_aux(&self, key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		self.client.get_aux(key)
	}

	pub fn info(&self) -> BlockchainInfo<Block> {
		self.client.info()
	}

	pub fn header(
		&self,
		hash: <Block as BlockT>::Hash,
	) -> ClientResult<Option<<Block as BlockT>::Header>> {
		self.client.header(hash)
	}

	pub fn has_state_at(&self, block: &BlockId<Block>) -> bool {
		let (number, hash) = match *block {
			BlockId::Hash(h) => match self.as_client().number(h) {
				Ok(Some(n)) => (n, h),
				_ => return false,
			},
			BlockId::Number(n) => match self.as_client().hash(n) {
				Ok(Some(h)) => (n, h),
				_ => return false,
			},
		};
		self.backend.have_state_at(hash, number)
	}

	pub fn justifications(
		&self,
		hash: <Block as BlockT>::Hash,
	) -> ClientResult<Option<Justifications>> {
		self.client.justifications(hash)
	}

	pub fn finality_notification_stream(&self) -> FinalityNotifications<Block> {
		self.client.finality_notification_stream()
	}

	pub fn import_notification_stream(&self) -> ImportNotifications<Block> {
		self.client.import_notification_stream()
	}

	pub fn finalize_block(
		&self,
		hash: <Block as BlockT>::Hash,
		justification: Option<Justification>,
		notify: bool,
	) -> ClientResult<()> {
		self.client.finalize_block(hash, justification, notify)
	}
}

#[async_trait::async_trait]
impl BlockImport<Block> for PeersClient {
	type Error = ConsensusError;
	type Transaction = ();

	async fn check_block(
		&mut self,
		block: BlockCheckParams<Block>,
	) -> Result<ImportResult, Self::Error> {
		self.client.check_block(block).await
	}

	async fn import_block(
		&mut self,
		block: BlockImportParams<Block, ()>,
		cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		self.client.import_block(block.clear_storage_changes_and_mutate(), cache).await
	}
}

pub struct Peer<D, BlockImport> {
	pub data: D,
	client: PeersClient,
	/// We keep a copy of the verifier so that we can invoke it for locally-generated blocks,
	/// instead of going through the import queue.
	verifier: VerifierAdapter<Block>,
	/// We keep a copy of the block_import so that we can invoke it for locally-generated blocks,
	/// instead of going through the import queue.
	block_import: BlockImportAdapter<BlockImport>,
	select_chain: Option<LongestChain<substrate_test_runtime_client::Backend, Block>>,
	backend: Option<Arc<substrate_test_runtime_client::Backend>>,
	network: NetworkWorker<Block, <Block as BlockT>::Hash, PeersFullClient>,
	imported_blocks_stream: Pin<Box<dyn Stream<Item = BlockImportNotification<Block>> + Send>>,
	finality_notification_stream: Pin<Box<dyn Stream<Item = FinalityNotification<Block>> + Send>>,
	listen_addr: Multiaddr,
}

impl<D, B> Peer<D, B>
where
	B: BlockImport<Block, Error = ConsensusError> + Send + Sync,
	B::Transaction: Send,
{
	/// Get this peer ID.
	pub fn id(&self) -> PeerId {
		self.network.service().local_peer_id()
	}

	/// Returns true if we're major syncing.
	pub fn is_major_syncing(&self) -> bool {
		self.network.service().is_major_syncing()
	}

	// Returns a clone of the local SelectChain, only available on full nodes
	pub fn select_chain(
		&self,
	) -> Option<LongestChain<substrate_test_runtime_client::Backend, Block>> {
		self.select_chain.clone()
	}

	/// Returns the number of peers we're connected to.
	pub fn num_peers(&self) -> usize {
		self.network.num_connected_peers()
	}

	/// Returns the number of downloaded blocks.
	pub fn num_downloaded_blocks(&self) -> usize {
		self.network.num_downloaded_blocks()
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
	pub fn announce_block(&self, hash: <Block as BlockT>::Hash, data: Option<Vec<u8>>) {
		self.network.service().announce_block(hash, data);
	}

	/// Request explicit fork sync.
	pub fn set_sync_fork_request(
		&self,
		peers: Vec<PeerId>,
		hash: <Block as BlockT>::Hash,
		number: NumberFor<Block>,
	) {
		self.network.service().set_sync_fork_request(peers, hash, number);
	}

	/// Add blocks to the peer -- edit the block before adding
	pub fn generate_blocks<F>(
		&mut self,
		count: usize,
		origin: BlockOrigin,
		edit_block: F,
	) -> Vec<H256>
	where
		F: FnMut(
			BlockBuilder<Block, PeersFullClient, substrate_test_runtime_client::Backend>,
		) -> Block,
	{
		let best_hash = self.client.info().best_hash;
		self.generate_blocks_at(
			BlockId::Hash(best_hash),
			count,
			origin,
			edit_block,
			false,
			true,
			true,
			ForkChoiceStrategy::LongestChain,
		)
	}

	/// Add blocks to the peer -- edit the block before adding and use custom fork choice rule.
	pub fn generate_blocks_with_fork_choice<F>(
		&mut self,
		count: usize,
		origin: BlockOrigin,
		edit_block: F,
		fork_choice: ForkChoiceStrategy,
	) -> Vec<H256>
	where
		F: FnMut(
			BlockBuilder<Block, PeersFullClient, substrate_test_runtime_client::Backend>,
		) -> Block,
	{
		let best_hash = self.client.info().best_hash;
		self.generate_blocks_at(
			BlockId::Hash(best_hash),
			count,
			origin,
			edit_block,
			false,
			true,
			true,
			fork_choice,
		)
	}

	/// Add blocks to the peer -- edit the block before adding. The chain will
	/// start at the given block iD.
	pub fn generate_blocks_at<F>(
		&mut self,
		at: BlockId<Block>,
		count: usize,
		origin: BlockOrigin,
		mut edit_block: F,
		headers_only: bool,
		inform_sync_about_new_best_block: bool,
		announce_block: bool,
		fork_choice: ForkChoiceStrategy,
	) -> Vec<H256>
	where
		F: FnMut(
			BlockBuilder<Block, PeersFullClient, substrate_test_runtime_client::Backend>,
		) -> Block,
	{
		let mut hashes = Vec::with_capacity(count);
		let full_client = self.client.as_client();
		let mut at = full_client.block_hash_from_id(&at).unwrap().unwrap();
		for _ in 0..count {
			let builder = full_client.new_block_at(at, Default::default(), false).unwrap();
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
			let mut import_block = BlockImportParams::new(origin, header.clone());
			import_block.body = if headers_only { None } else { Some(block.extrinsics) };
			import_block.fork_choice = Some(fork_choice);
			let (import_block, cache) =
				futures::executor::block_on(self.verifier.verify(import_block)).unwrap();
			let cache = if let Some(cache) = cache {
				cache.into_iter().collect()
			} else {
				Default::default()
			};

			futures::executor::block_on(self.block_import.import_block(import_block, cache))
				.expect("block_import failed");
			if announce_block {
				self.network.service().announce_block(hash, None);
			}
			hashes.push(hash);
			at = hash;
		}

		if inform_sync_about_new_best_block {
			self.network.new_best_block_imported(
				at,
				*full_client.header(at).ok().flatten().unwrap().number(),
			);
		}
		hashes
	}

	/// Push blocks to the peer (simplified: with or without a TX)
	pub fn push_blocks(&mut self, count: usize, with_tx: bool) -> Vec<H256> {
		let best_hash = self.client.info().best_hash;
		self.push_blocks_at(BlockId::Hash(best_hash), count, with_tx)
	}

	/// Push blocks to the peer (simplified: with or without a TX)
	pub fn push_headers(&mut self, count: usize) -> Vec<H256> {
		let best_hash = self.client.info().best_hash;
		self.generate_tx_blocks_at(BlockId::Hash(best_hash), count, false, true, true, true)
	}

	/// Push blocks to the peer (simplified: with or without a TX) starting from
	/// given hash.
	pub fn push_blocks_at(&mut self, at: BlockId<Block>, count: usize, with_tx: bool) -> Vec<H256> {
		self.generate_tx_blocks_at(at, count, with_tx, false, true, true)
	}

	/// Push blocks to the peer (simplified: with or without a TX) starting from
	/// given hash without informing the sync protocol about the new best block.
	pub fn push_blocks_at_without_informing_sync(
		&mut self,
		at: BlockId<Block>,
		count: usize,
		with_tx: bool,
		announce_block: bool,
	) -> Vec<H256> {
		self.generate_tx_blocks_at(at, count, with_tx, false, false, announce_block)
	}

	/// Push blocks to the peer (simplified: with or without a TX) starting from
	/// given hash without announcing the block.
	pub fn push_blocks_at_without_announcing(
		&mut self,
		at: BlockId<Block>,
		count: usize,
		with_tx: bool,
	) -> Vec<H256> {
		self.generate_tx_blocks_at(at, count, with_tx, false, true, false)
	}

	/// Push blocks/headers to the peer (simplified: with or without a TX) starting from
	/// given hash.
	fn generate_tx_blocks_at(
		&mut self,
		at: BlockId<Block>,
		count: usize,
		with_tx: bool,
		headers_only: bool,
		inform_sync_about_new_best_block: bool,
		announce_block: bool,
	) -> Vec<H256> {
		let mut nonce = 0;
		if with_tx {
			self.generate_blocks_at(
				at,
				count,
				BlockOrigin::File,
				|mut builder| {
					let transfer = Transfer {
						from: AccountKeyring::Alice.into(),
						to: AccountKeyring::Alice.into(),
						amount: 1,
						nonce,
					};
					builder.push(transfer.into_signed_tx()).unwrap();
					nonce += 1;
					builder.build().unwrap().block
				},
				headers_only,
				inform_sync_about_new_best_block,
				announce_block,
				ForkChoiceStrategy::LongestChain,
			)
		} else {
			self.generate_blocks_at(
				at,
				count,
				BlockOrigin::File,
				|builder| builder.build().unwrap().block,
				headers_only,
				inform_sync_about_new_best_block,
				announce_block,
				ForkChoiceStrategy::LongestChain,
			)
		}
	}

	pub fn push_authorities_change_block(
		&mut self,
		new_authorities: Vec<AuthorityId>,
	) -> Vec<H256> {
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
	pub fn network_service(&self) -> &Arc<NetworkService<Block, <Block as BlockT>::Hash>> {
		self.network.service()
	}

	/// Get a reference to the network worker.
	pub fn network(&self) -> &NetworkWorker<Block, <Block as BlockT>::Hash, PeersFullClient> {
		&self.network
	}

	/// Test helper to compare the blockchain state of multiple (networked)
	/// clients.
	pub fn blockchain_canon_equals(&self, other: &Self) -> bool {
		if let (Some(mine), Some(others)) = (self.backend.clone(), other.backend.clone()) {
			mine.blockchain().info().best_hash == others.blockchain().info().best_hash
		} else {
			false
		}
	}

	/// Count the total number of imported blocks.
	pub fn blocks_count(&self) -> u64 {
		self.backend
			.as_ref()
			.map(|backend| backend.blockchain().info().best_number)
			.unwrap_or(0)
	}

	/// Return a collection of block hashes that failed verification
	pub fn failed_verifications(&self) -> HashMap<<Block as BlockT>::Hash, String> {
		self.verifier.failed_verifications.lock().clone()
	}

	pub fn has_block(&self, hash: H256) -> bool {
		self.backend
			.as_ref()
			.map(|backend| backend.blockchain().header(hash).unwrap().is_some())
			.unwrap_or(false)
	}

	pub fn has_body(&self, hash: H256) -> bool {
		self.backend
			.as_ref()
			.map(|backend| backend.blockchain().body(hash).unwrap().is_some())
			.unwrap_or(false)
	}
}

pub trait BlockImportAdapterFull:
	BlockImport<
		Block,
		Transaction = TransactionFor<substrate_test_runtime_client::Backend, Block>,
		Error = ConsensusError,
	> + Send
	+ Sync
	+ Clone
{
}

impl<T> BlockImportAdapterFull for T where
	T: BlockImport<
			Block,
			Transaction = TransactionFor<substrate_test_runtime_client::Backend, Block>,
			Error = ConsensusError,
		> + Send
		+ Sync
		+ Clone
{
}

/// Implements `BlockImport` for any `Transaction`. Internally the transaction is
/// "converted", aka the field is set to `None`.
///
/// This is required as the `TestNetFactory` trait does not distinguish between
/// full and light nodes.
#[derive(Clone)]
pub struct BlockImportAdapter<I, Transaction = ()> {
	inner: I,
	_phantom: PhantomData<Transaction>,
}

impl<I, Transaction> BlockImportAdapter<I, Transaction> {
	/// Create a new instance of `Self::Full`.
	pub fn new(inner: I) -> Self {
		Self { inner, _phantom: PhantomData }
	}
}

#[async_trait::async_trait]
impl<I, Transaction> BlockImport<Block> for BlockImportAdapter<I, Transaction>
where
	I: BlockImport<Block, Error = ConsensusError> + Send + Sync,
	I::Transaction: Send,
	Transaction: Send + 'static,
{
	type Error = ConsensusError;
	type Transaction = Transaction;

	async fn check_block(
		&mut self,
		block: BlockCheckParams<Block>,
	) -> Result<ImportResult, Self::Error> {
		self.inner.check_block(block).await
	}

	async fn import_block(
		&mut self,
		block: BlockImportParams<Block, Self::Transaction>,
		cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		self.inner.import_block(block.clear_storage_changes_and_mutate(), cache).await
	}
}

/// Implements `Verifier` and keeps track of failed verifications.
struct VerifierAdapter<B: BlockT> {
	verifier: Arc<futures::lock::Mutex<Box<dyn Verifier<B>>>>,
	failed_verifications: Arc<Mutex<HashMap<B::Hash, String>>>,
}

#[async_trait::async_trait]
impl<B: BlockT> Verifier<B> for VerifierAdapter<B> {
	async fn verify(
		&mut self,
		block: BlockImportParams<B, ()>,
	) -> Result<(BlockImportParams<B, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		let hash = block.header.hash();
		self.verifier.lock().await.verify(block).await.map_err(|e| {
			self.failed_verifications.lock().insert(hash, e.clone());
			e
		})
	}
}

impl<B: BlockT> Clone for VerifierAdapter<B> {
	fn clone(&self) -> Self {
		Self {
			verifier: self.verifier.clone(),
			failed_verifications: self.failed_verifications.clone(),
		}
	}
}

impl<B: BlockT> VerifierAdapter<B> {
	fn new(verifier: impl Verifier<B> + 'static) -> Self {
		VerifierAdapter {
			verifier: Arc::new(futures::lock::Mutex::new(Box::new(verifier))),
			failed_verifications: Default::default(),
		}
	}
}

struct TestWarpSyncProvider<B: BlockT>(Arc<dyn HeaderBackend<B>>);

impl<B: BlockT> WarpSyncProvider<B> for TestWarpSyncProvider<B> {
	fn generate(
		&self,
		_start: B::Hash,
	) -> Result<EncodedProof, Box<dyn std::error::Error + Send + Sync>> {
		let info = self.0.info();
		let best_header = self.0.header(info.best_hash).unwrap().unwrap();
		Ok(EncodedProof(best_header.encode()))
	}
	fn verify(
		&self,
		proof: &EncodedProof,
		_set_id: SetId,
		_authorities: AuthorityList,
	) -> Result<VerificationResult<B>, Box<dyn std::error::Error + Send + Sync>> {
		let EncodedProof(encoded) = proof;
		let header = B::Header::decode(&mut encoded.as_slice()).unwrap();
		Ok(VerificationResult::Complete(0, Default::default(), header))
	}
	fn current_authorities(&self) -> AuthorityList {
		Default::default()
	}
}

/// Configuration for a full peer.
#[derive(Default)]
pub struct FullPeerConfig {
	/// Pruning window size.
	///
	/// NOTE: only finalized blocks are subject for removal!
	pub blocks_pruning: Option<u32>,
	/// Block announce validator.
	pub block_announce_validator: Option<Box<dyn BlockAnnounceValidator<Block> + Send + Sync>>,
	/// List of notification protocols that the network must support.
	pub notifications_protocols: Vec<ProtocolName>,
	/// List of request-response protocols that the network must support.
	pub request_response_protocols: Vec<RequestResponseConfig>,
	/// The indices of the peers the peer should be connected to.
	///
	/// If `None`, it will be connected to all other peers.
	pub connect_to_peers: Option<Vec<usize>>,
	/// Whether the full peer should have the authority role.
	pub is_authority: bool,
	/// Syncing mode
	pub sync_mode: SyncMode,
	/// Extra genesis storage.
	pub extra_storage: Option<sp_core::storage::Storage>,
	/// Enable transaction indexing.
	pub storage_chain: bool,
	/// Optional target block header to sync to
	pub target_block: Option<<Block as BlockT>::Header>,
}

#[async_trait::async_trait]
pub trait TestNetFactory: Default + Sized
where
	<Self::BlockImport as BlockImport<Block>>::Transaction: Send,
{
	type Verifier: 'static + Verifier<Block>;
	type BlockImport: BlockImport<Block, Error = ConsensusError> + Clone + Send + Sync + 'static;
	type PeerData: Default;

	/// This one needs to be implemented!
	fn make_verifier(&self, client: PeersClient, peer_data: &Self::PeerData) -> Self::Verifier;

	/// Get reference to peer.
	fn peer(&mut self, i: usize) -> &mut Peer<Self::PeerData, Self::BlockImport>;
	fn peers(&self) -> &Vec<Peer<Self::PeerData, Self::BlockImport>>;
	fn mut_peers<F: FnOnce(&mut Vec<Peer<Self::PeerData, Self::BlockImport>>)>(
		&mut self,
		closure: F,
	);

	/// Get custom block import handle for fresh client, along with peer data.
	fn make_block_import(
		&self,
		client: PeersClient,
	) -> (
		BlockImportAdapter<Self::BlockImport>,
		Option<BoxJustificationImport<Block>>,
		Self::PeerData,
	);

	/// Create new test network with this many peers.
	fn new(n: usize) -> Self {
		trace!(target: "test_network", "Creating test network");
		let mut net = Self::default();

		for i in 0..n {
			trace!(target: "test_network", "Adding peer {}", i);
			net.add_full_peer();
		}
		net
	}

	fn add_full_peer(&mut self) {
		self.add_full_peer_with_config(Default::default())
	}

	/// Add a full peer.
	fn add_full_peer_with_config(&mut self, config: FullPeerConfig) {
		let mut test_client_builder = match (config.blocks_pruning, config.storage_chain) {
			(Some(blocks_pruning), true) => TestClientBuilder::with_tx_storage(blocks_pruning),
			(None, true) => TestClientBuilder::with_tx_storage(u32::MAX),
			(Some(blocks_pruning), false) => TestClientBuilder::with_pruning_window(blocks_pruning),
			(None, false) => TestClientBuilder::with_default_backend(),
		};
		if let Some(storage) = config.extra_storage {
			let genesis_extra_storage = test_client_builder.genesis_init_mut().extra_storage();
			*genesis_extra_storage = storage;
		}

		if matches!(config.sync_mode, SyncMode::Fast { .. } | SyncMode::Warp) {
			test_client_builder = test_client_builder.set_no_genesis();
		}
		let backend = test_client_builder.backend();
		let (c, longest_chain) = test_client_builder.build_with_longest_chain();
		let client = Arc::new(c);

		let (block_import, justification_import, data) = self
			.make_block_import(PeersClient { client: client.clone(), backend: backend.clone() });

		let verifier = self
			.make_verifier(PeersClient { client: client.clone(), backend: backend.clone() }, &data);
		let verifier = VerifierAdapter::new(verifier);

		let import_queue = Box::new(BasicQueue::new(
			verifier.clone(),
			Box::new(block_import.clone()),
			justification_import,
			&sp_core::testing::TaskExecutor::new(),
			None,
		));

		let listen_addr = build_multiaddr![Memory(rand::random::<u64>())];

		let mut network_config =
			NetworkConfiguration::new("test-node", "test-client", Default::default(), None);
		network_config.sync_mode = config.sync_mode;
		network_config.transport = TransportConfig::MemoryOnly;
		network_config.listen_addresses = vec![listen_addr.clone()];
		network_config.allow_non_globals_in_dht = true;
		network_config
			.request_response_protocols
			.extend(config.request_response_protocols);
		network_config.extra_sets = config
			.notifications_protocols
			.into_iter()
			.map(|p| NonDefaultSetConfig {
				notifications_protocol: p,
				fallback_names: Vec::new(),
				max_notification_size: 1024 * 1024,
				handshake: None,
				set_config: Default::default(),
			})
			.collect();
		if let Some(connect_to) = config.connect_to_peers {
			let addrs = connect_to
				.iter()
				.map(|v| {
					let peer_id = self.peer(*v).network_service().local_peer_id();
					let multiaddr = self.peer(*v).listen_addr.clone();
					MultiaddrWithPeerId { peer_id, multiaddr }
				})
				.collect();
			network_config.default_peers_set.reserved_nodes = addrs;
			network_config.default_peers_set.non_reserved_mode = NonReservedPeerMode::Deny;
		}

		let protocol_id = ProtocolId::from("test-protocol-name");

		let fork_id = Some(String::from("test-fork-id"));

		let block_request_protocol_config = {
			let (handler, protocol_config) =
				BlockRequestHandler::new(&protocol_id, None, client.clone(), 50);
			self.spawn_task(handler.run().boxed());
			protocol_config
		};

		let state_request_protocol_config = {
			let (handler, protocol_config) =
				StateRequestHandler::new(&protocol_id, None, client.clone(), 50);
			self.spawn_task(handler.run().boxed());
			protocol_config
		};

		let light_client_request_protocol_config = {
			let (handler, protocol_config) =
				LightClientRequestHandler::new(&protocol_id, None, client.clone());
			self.spawn_task(handler.run().boxed());
			protocol_config
		};

		let warp_sync = Arc::new(TestWarpSyncProvider(client.clone()));

		let warp_sync_params = match config.target_block {
			Some(target_block) => {
				let (sender, receiver) = oneshot::channel::<<Block as BlockT>::Header>();
				let _ = sender.send(target_block);
				WarpSyncParams::WaitForTarget(receiver)
			},
			_ => WarpSyncParams::WithProvider(warp_sync.clone()),
		};

		let warp_protocol_config = {
			let (handler, protocol_config) = warp_request_handler::RequestHandler::new(
				protocol_id.clone(),
				client
					.block_hash(0u32.into())
					.ok()
					.flatten()
					.expect("Genesis block exists; qed"),
				None,
				warp_sync.clone(),
			);
			self.spawn_task(handler.run().boxed());
			protocol_config
		};

		let block_announce_validator = config
			.block_announce_validator
			.unwrap_or_else(|| Box::new(DefaultBlockAnnounceValidator));
		let (chain_sync_network_provider, chain_sync_network_handle) =
			NetworkServiceProvider::new();

		let (chain_sync, chain_sync_service, block_announce_config) = ChainSync::new(
			match network_config.sync_mode {
				SyncMode::Full => sc_network_common::sync::SyncMode::Full,
				SyncMode::Fast { skip_proofs, storage_chain_mode } =>
					sc_network_common::sync::SyncMode::LightState {
						skip_proofs,
						storage_chain_mode,
					},
				SyncMode::Warp => sc_network_common::sync::SyncMode::Warp,
			},
			client.clone(),
			protocol_id.clone(),
			&fork_id,
			Roles::from(if config.is_authority { &Role::Authority } else { &Role::Full }),
			block_announce_validator,
			network_config.max_parallel_downloads,
			Some(warp_sync_params),
			None,
			chain_sync_network_handle,
			import_queue.service(),
			block_request_protocol_config.name.clone(),
			state_request_protocol_config.name.clone(),
			Some(warp_protocol_config.name.clone()),
		)
		.unwrap();

		let network = NetworkWorker::new(sc_network::config::Params {
			role: if config.is_authority { Role::Authority } else { Role::Full },
			executor: Box::new(|f| {
				tokio::spawn(f);
			}),
			network_config,
			chain: client.clone(),
			protocol_id,
			fork_id,
			chain_sync: Box::new(chain_sync),
			chain_sync_service: Box::new(chain_sync_service.clone()),
			metrics_registry: None,
			block_announce_config,
			request_response_protocol_configs: [
				block_request_protocol_config,
				state_request_protocol_config,
				light_client_request_protocol_config,
				warp_protocol_config,
			]
			.to_vec(),
		})
		.unwrap();

		trace!(target: "test_network", "Peer identifier: {}", network.service().local_peer_id());

		let service = network.service().clone();
		tokio::spawn(async move {
			chain_sync_network_provider.run(service).await;
		});
		tokio::spawn(async move {
			import_queue.run(Box::new(chain_sync_service)).await;
		});

		self.mut_peers(move |peers| {
			for peer in peers.iter_mut() {
				peer.network
					.add_known_address(network.service().local_peer_id(), listen_addr.clone());
			}

			let imported_blocks_stream = Box::pin(client.import_notification_stream().fuse());
			let finality_notification_stream =
				Box::pin(client.finality_notification_stream().fuse());

			peers.push(Peer {
				data,
				client: PeersClient { client: client.clone(), backend: backend.clone() },
				select_chain: Some(longest_chain),
				backend: Some(backend),
				imported_blocks_stream,
				finality_notification_stream,
				block_import,
				verifier,
				network,
				listen_addr,
			});
		});
	}

	/// Used to spawn background tasks, e.g. the block request protocol handler.
	fn spawn_task(&self, f: BoxFuture<'static, ()>) {
		tokio::spawn(f);
	}

	/// Polls the testnet until all nodes are in sync.
	///
	/// Must be executed in a task context.
	fn poll_until_sync(&mut self, cx: &mut FutureContext) -> Poll<()> {
		self.poll(cx);

		// Return `NotReady` if there's a mismatch in the highest block number.
		let mut highest = None;
		for peer in self.peers().iter() {
			if peer.is_major_syncing() || peer.network.num_queued_blocks() != 0 {
				return Poll::Pending
			}
			if peer.network.num_sync_requests() != 0 {
				return Poll::Pending
			}
			match (highest, peer.client.info().best_hash) {
				(None, b) => highest = Some(b),
				(Some(ref a), ref b) if a == b => {},
				(Some(_), _) => return Poll::Pending,
			}
		}
		Poll::Ready(())
	}

	/// Polls the testnet until theres' no activiy of any kind.
	///
	/// Must be executed in a task context.
	fn poll_until_idle(&mut self, cx: &mut FutureContext) -> Poll<()> {
		self.poll(cx);

		for peer in self.peers().iter() {
			if peer.is_major_syncing() || peer.network.num_queued_blocks() != 0 {
				return Poll::Pending
			}
			if peer.network.num_sync_requests() != 0 {
				return Poll::Pending
			}
		}

		Poll::Ready(())
	}

	/// Polls the testnet until all peers are connected to each other.
	///
	/// Must be executed in a task context.
	fn poll_until_connected(&mut self, cx: &mut FutureContext) -> Poll<()> {
		self.poll(cx);

		let num_peers = self.peers().len();
		if self.peers().iter().all(|p| p.num_peers() == num_peers - 1) {
			return Poll::Ready(())
		}

		Poll::Pending
	}

	/// Run the network until we are sync'ed.
	///
	/// Calls `poll_until_sync` repeatedly.
	/// (If we've not synced within 10 mins then panic rather than hang.)
	async fn run_until_sync(&mut self) {
		timeout(
			Duration::from_secs(10 * 60),
			futures::future::poll_fn::<(), _>(|cx| self.poll_until_sync(cx)),
		)
		.await
		.expect("sync didn't happen within 10 mins");
	}

	/// Run the network until there are no pending packets.
	///
	/// Calls `poll_until_idle` repeatedly with the runtime passed as parameter.
	async fn run_until_idle(&mut self) {
		futures::future::poll_fn::<(), _>(|cx| self.poll_until_idle(cx)).await;
	}

	/// Run the network until all peers are connected to each other.
	///
	/// Calls `poll_until_connected` repeatedly with the runtime passed as parameter.
	async fn run_until_connected(&mut self) {
		futures::future::poll_fn::<(), _>(|cx| self.poll_until_connected(cx)).await;
	}

	/// Polls the testnet. Processes all the pending actions.
	fn poll(&mut self, cx: &mut FutureContext) {
		self.mut_peers(|peers| {
			for (i, peer) in peers.iter_mut().enumerate() {
				trace!(target: "sync", "-- Polling {}: {}", i, peer.id());
				loop {
					// The code below is not quite correct, because we are polling a different
					// instance of the future every time. But as long as
					// `NetworkWorker::next_action()` contains just streams polling not interleaved
					// with other `.await`s, dropping the future and recreating it works the same as
					// polling a single instance.
					let net_poll_future = peer.network.next_action();
					pin_mut!(net_poll_future);
					if let Poll::Pending = net_poll_future.poll(cx) {
						break
					}
				}
				trace!(target: "sync", "-- Polling complete {}: {}", i, peer.id());

				// We poll `imported_blocks_stream`.
				while let Poll::Ready(Some(notification)) =
					peer.imported_blocks_stream.as_mut().poll_next(cx)
				{
					peer.network.service().announce_block(notification.hash, None);
				}

				// We poll `finality_notification_stream`.
				while let Poll::Ready(Some(notification)) =
					peer.finality_notification_stream.as_mut().poll_next(cx)
				{
					peer.network.on_block_finalized(notification.hash, notification.header);
				}
			}
		});
	}
}

#[derive(Default)]
pub struct TestNet {
	peers: Vec<Peer<(), PeersClient>>,
}

impl TestNetFactory for TestNet {
	type Verifier = PassThroughVerifier;
	type PeerData = ();
	type BlockImport = PeersClient;

	fn make_verifier(&self, _client: PeersClient, _peer_data: &()) -> Self::Verifier {
		PassThroughVerifier::new(false)
	}

	fn make_block_import(
		&self,
		client: PeersClient,
	) -> (
		BlockImportAdapter<Self::BlockImport>,
		Option<BoxJustificationImport<Block>>,
		Self::PeerData,
	) {
		(client.as_block_import(), None, ())
	}

	fn peer(&mut self, i: usize) -> &mut Peer<(), Self::BlockImport> {
		&mut self.peers[i]
	}

	fn peers(&self) -> &Vec<Peer<(), Self::BlockImport>> {
		&self.peers
	}

	fn mut_peers<F: FnOnce(&mut Vec<Peer<(), Self::BlockImport>>)>(&mut self, closure: F) {
		closure(&mut self.peers);
	}
}

pub struct ForceFinalized(PeersClient);

#[async_trait::async_trait]
impl JustificationImport<Block> for ForceFinalized {
	type Error = ConsensusError;

	async fn on_start(&mut self) -> Vec<(H256, NumberFor<Block>)> {
		Vec::new()
	}

	async fn import_justification(
		&mut self,
		hash: H256,
		_number: NumberFor<Block>,
		justification: Justification,
	) -> Result<(), Self::Error> {
		self.0
			.finalize_block(hash, Some(justification), true)
			.map_err(|_| ConsensusError::InvalidJustification)
	}
}

#[derive(Default)]
pub struct JustificationTestNet(TestNet);

impl TestNetFactory for JustificationTestNet {
	type Verifier = PassThroughVerifier;
	type PeerData = ();
	type BlockImport = PeersClient;

	fn make_verifier(&self, client: PeersClient, peer_data: &()) -> Self::Verifier {
		self.0.make_verifier(client, peer_data)
	}

	fn peer(&mut self, i: usize) -> &mut Peer<Self::PeerData, Self::BlockImport> {
		self.0.peer(i)
	}

	fn peers(&self) -> &Vec<Peer<Self::PeerData, Self::BlockImport>> {
		self.0.peers()
	}

	fn mut_peers<F: FnOnce(&mut Vec<Peer<Self::PeerData, Self::BlockImport>>)>(
		&mut self,
		closure: F,
	) {
		self.0.mut_peers(closure)
	}

	fn make_block_import(
		&self,
		client: PeersClient,
	) -> (
		BlockImportAdapter<Self::BlockImport>,
		Option<BoxJustificationImport<Block>>,
		Self::PeerData,
	) {
		(client.as_block_import(), Some(Box::new(ForceFinalized(client))), Default::default())
	}
}
