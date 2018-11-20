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

//! Substrate Client

use std::{marker::PhantomData, collections::{HashSet, BTreeMap}, sync::Arc};
use error::Error;
use futures::sync::mpsc;
use parking_lot::{Mutex, RwLock};
use primitives::AuthorityId;
use runtime_primitives::{
	Justification,
	generic::{BlockId, SignedBlock},
	transaction_validity::{TransactionValidity, TransactionTag},
};
use consensus::{ImportBlock, ImportResult, BlockOrigin};
use runtime_primitives::traits::{
	Block as BlockT, Header as HeaderT, Zero, As, NumberFor, CurrentHeight, BlockNumberToHash,
	ApiRef, ProvideRuntimeApi, Digest, DigestItem,
};
use runtime_primitives::BuildStorage;
use runtime_api::{Core as CoreAPI, CallApiAt, TaggedTransactionQueue, ConstructRuntimeApi};
use primitives::{Blake2Hasher, H256, ChangesTrieConfiguration, convert_hash};
use primitives::storage::{StorageKey, StorageData};
use primitives::storage::well_known_keys;
use codec::Decode;
use state_machine::{
	DBValue, Backend as StateBackend, CodeExecutor, ChangesTrieAnchorBlockId,
	ExecutionStrategy, ExecutionManager, prove_read,
	ChangesTrieRootsStorage, ChangesTrieStorage,
	key_changes, key_changes_proof, OverlayedChanges
};
use codec::Encode;

use backend::{self, BlockImportOperation};
use blockchain::{self, Info as ChainInfo, Backend as ChainBackend, HeaderBackend as ChainHeaderBackend};
use call_executor::{CallExecutor, LocalCallExecutor};
use executor::{RuntimeVersion, RuntimeInfo};
use notifications::{StorageNotifications, StorageEventStream};
use light::fetcher::ChangesProof;
use {cht, error, in_mem, block_builder::{self, api::BlockBuilder as BlockBuilderAPI}, genesis, consensus};

/// Type that implements `futures::Stream` of block import events.
pub type ImportNotifications<Block> = mpsc::UnboundedReceiver<BlockImportNotification<Block>>;

/// A stream of block finality notifications.
pub type FinalityNotifications<Block> = mpsc::UnboundedReceiver<FinalityNotification<Block>>;

/// Substrate Client
pub struct Client<B, E, Block, RA> where Block: BlockT {
	backend: Arc<B>,
	executor: E,
	storage_notifications: Mutex<StorageNotifications<Block>>,
	import_notification_sinks: Mutex<Vec<mpsc::UnboundedSender<BlockImportNotification<Block>>>>,
	finality_notification_sinks: Mutex<Vec<mpsc::UnboundedSender<FinalityNotification<Block>>>>,
	import_lock: Mutex<()>,
	importing_block: RwLock<Option<Block::Hash>>, // holds the block hash currently being imported. TODO: replace this with block queue
	block_execution_strategy: ExecutionStrategy,
	api_execution_strategy: ExecutionStrategy,
	_phantom: PhantomData<RA>,
}

/// A source of blockchain events.
pub trait BlockchainEvents<Block: BlockT> {
	/// Get block import event stream. Not guaranteed to be fired for every
	/// imported block.
	fn import_notification_stream(&self) -> ImportNotifications<Block>;

	/// Get a stream of finality notifications. Not guaranteed to be fired for every
	/// finalized block.
	fn finality_notification_stream(&self) -> FinalityNotifications<Block>;

	/// Get storage changes event stream.
	///
	/// Passing `None` as `filter_keys` subscribes to all storage changes.
	fn storage_changes_notification_stream(&self, filter_keys: Option<&[StorageKey]>) -> error::Result<StorageEventStream<Block::Hash>>;
}

/// Chain head information.
pub trait ChainHead<Block: BlockT> {
	/// Get best block header.
	fn best_block_header(&self) -> Result<<Block as BlockT>::Header, error::Error>;
	/// Get all leaves of the chain: block hashes that have no children currently.
	/// Leaves that can never be finalized will not be returned.
	fn leaves(&self) -> Result<Vec<<Block as BlockT>::Hash>, error::Error>;
}

/// Fetch block body by ID.
pub trait BlockBody<Block: BlockT> {
	/// Get block body by ID. Returns `None` if the body is not stored.
	fn block_body(&self, id: &BlockId<Block>) -> error::Result<Option<Vec<<Block as BlockT>::Extrinsic>>>;
}

/// Client info
// TODO: split queue info from chain info and amalgamate into single struct.
#[derive(Debug)]
pub struct ClientInfo<Block: BlockT> {
	/// Best block hash.
	pub chain: ChainInfo<Block>,
	/// Best block number in the queue.
	pub best_queued_number: Option<<<Block as BlockT>::Header as HeaderT>::Number>,
	/// Best queued block hash.
	pub best_queued_hash: Option<Block::Hash>,
}

/// Block status.
#[derive(Debug, PartialEq, Eq)]
pub enum BlockStatus {
	/// Added to the import queue.
	Queued,
	/// Already in the blockchain.
	InChain,
	/// Block or parent is known to be bad.
	KnownBad,
	/// Not in the queue or the blockchain.
	Unknown,
}

/// Summary of an imported block
#[derive(Clone, Debug)]
pub struct BlockImportNotification<Block: BlockT> {
	/// Imported block header hash.
	pub hash: Block::Hash,
	/// Imported block origin.
	pub origin: BlockOrigin,
	/// Imported block header.
	pub header: Block::Header,
	/// Is this the new best block.
	pub is_new_best: bool,
	/// Tags provided by transactions imported in that block.
	pub tags: Vec<TransactionTag>,
}

/// Summary of a finalized block.
#[derive(Clone, Debug)]
pub struct FinalityNotification<Block: BlockT> {
	/// Imported block header hash.
	pub hash: Block::Hash,
	/// Imported block header.
	pub header: Block::Header,
}

// used in importing a block, where additional changes are made after the runtime
// executed.
enum PrePostHeader<H> {
	// they are the same: no post-runtime digest items.
	Same(H),
	// different headers (pre, post).
	Different(H, H),
}

impl<H> PrePostHeader<H> {
	// get a reference to the "pre-header" -- the header as it should be just after the runtime.
	fn pre(&self) -> &H {
		match *self {
			PrePostHeader::Same(ref h) => h,
			PrePostHeader::Different(ref h, _) => h,
		}
	}

	// get a reference to the "post-header" -- the header as it should be after all changes are applied.
	fn post(&self) -> &H {
		match *self {
			PrePostHeader::Same(ref h) => h,
			PrePostHeader::Different(_, ref h) => h,
		}
	}

	// convert to the "post-header" -- the header as it should be after all changes are applied.
	fn into_post(self) -> H {
		match self {
			PrePostHeader::Same(h) => h,
			PrePostHeader::Different(_, h) => h,
		}
	}
}

/// Create an instance of in-memory client.
pub fn new_in_mem<E, Block, S, RA>(
	executor: E,
	genesis_storage: S,
) -> error::Result<Client<in_mem::Backend<Block, Blake2Hasher>, LocalCallExecutor<in_mem::Backend<Block, Blake2Hasher>, E>, Block, RA>>
	where
		E: CodeExecutor<Blake2Hasher> + RuntimeInfo,
		S: BuildStorage,
		Block: BlockT<Hash=H256>,
{
	new_with_backend(Arc::new(in_mem::Backend::new()), executor, genesis_storage)
}

/// Create a client with the explicitely provided backend.
/// This is useful for testing backend implementations.
pub fn new_with_backend<B, E, Block, S, RA>(
	backend: Arc<B>,
	executor: E,
	build_genesis_storage: S,
) -> error::Result<Client<B, LocalCallExecutor<B, E>, Block, RA>>
	where
		E: CodeExecutor<Blake2Hasher> + RuntimeInfo,
		S: BuildStorage,
		Block: BlockT<Hash=H256>,
		B: backend::LocalBackend<Block, Blake2Hasher>
{
	let call_executor = LocalCallExecutor::new(backend.clone(), executor);
	Client::new(backend, call_executor, build_genesis_storage, ExecutionStrategy::NativeWhenPossible, ExecutionStrategy::NativeWhenPossible)
}

impl<B, E, Block, RA> Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
	Block: BlockT<Hash=H256>,
{
	/// Creates new Substrate Client with given blockchain and code executor.
	pub fn new<S: BuildStorage>(
		backend: Arc<B>,
		executor: E,
		build_genesis_storage: S,
		block_execution_strategy: ExecutionStrategy,
		api_execution_strategy: ExecutionStrategy,
	) -> error::Result<Self> {
		if backend.blockchain().header(BlockId::Number(Zero::zero()))?.is_none() {
			let (genesis_storage, children_genesis_storage) = build_genesis_storage.build_storage()?;
			let mut op = backend.begin_operation(BlockId::Hash(Default::default()))?;
			let state_root = op.reset_storage(genesis_storage, children_genesis_storage)?;

			let genesis_block = genesis::construct_genesis_block::<Block>(state_root.into());
			info!("Initialising Genesis block/state (state: {}, header-hash: {})", genesis_block.header().state_root(), genesis_block.header().hash());
			op.set_block_data(
				genesis_block.deconstruct().0,
				Some(vec![]),
				None,
				::backend::NewBlockState::Final
			)?;
			backend.commit_operation(op)?;
		}

		Ok(Client {
			backend,
			executor,
			storage_notifications: Default::default(),
			import_notification_sinks: Default::default(),
			finality_notification_sinks: Default::default(),
			import_lock: Default::default(),
			importing_block: Default::default(),
			block_execution_strategy,
			api_execution_strategy,
			_phantom: Default::default(),
		})
	}

	/// Get a reference to the state at a given block.
	pub fn state_at(&self, block: &BlockId<Block>) -> error::Result<B::State> {
		self.backend.state_at(*block)
	}

	/// Expose backend reference. To be used in tests only
	pub fn backend(&self) -> &Arc<B> {
		&self.backend
	}

	/// Return single storage entry of contract under given address in state in a block of given hash.
	pub fn storage(&self, id: &BlockId<Block>, key: &StorageKey) -> error::Result<Option<StorageData>> {
		Ok(self.state_at(id)?
			.storage(&key.0).map_err(|e| error::Error::from_state(Box::new(e)))?
			.map(StorageData))
	}

	/// Get the code at a given block.
	pub fn code_at(&self, id: &BlockId<Block>) -> error::Result<Vec<u8>> {
		Ok(self.storage(id, &StorageKey(well_known_keys::CODE.to_vec()))?
			.expect("None is returned if there's no value stored for the given key; ':code' key is always defined; qed").0)
	}

	/// Get the set of authorities at a given block.
	pub fn authorities_at(&self, id: &BlockId<Block>) -> error::Result<Vec<AuthorityId>> {
		match self.backend.blockchain().cache().and_then(|cache| cache.authorities_at(*id)) {
			Some(cached_value) => Ok(cached_value),
			None => self.executor.call(id, "authorities",&[])
				.and_then(|r| Vec::<AuthorityId>::decode(&mut &r.return_data[..])
					.ok_or(error::ErrorKind::InvalidAuthoritiesSet.into()))
		}
	}

	/// Get the RuntimeVersion at a given block.
	pub fn runtime_version_at(&self, id: &BlockId<Block>) -> error::Result<RuntimeVersion> {
		// TODO: Post Poc-2 return an error if version is missing
		self.executor.runtime_version(id)
	}

	/// Get call executor reference.
	pub fn executor(&self) -> &E {
		&self.executor
	}

	/// Reads storage value at a given block + key, returning read proof.
	pub fn read_proof(&self, id: &BlockId<Block>, key: &[u8]) -> error::Result<Vec<Vec<u8>>> {
		self.state_at(id)
			.and_then(|state| prove_read(state, key)
				.map(|(_, proof)| proof)
				.map_err(Into::into))
	}

	/// Execute a call to a contract on top of state in a block of given hash
	/// AND returning execution proof.
	///
	/// No changes are made.
	pub fn execution_proof(&self, id: &BlockId<Block>, method: &str, call_data: &[u8]) -> error::Result<(Vec<u8>, Vec<Vec<u8>>)> {
		self.state_at(id).and_then(|state| self.executor.prove_at_state(state, &mut Default::default(), method, call_data))
	}

	/// Reads given header and generates CHT-based header proof.
	pub fn header_proof(&self, id: &BlockId<Block>) -> error::Result<(Block::Header, Vec<Vec<u8>>)> {
		self.header_proof_with_cht_size(id, cht::SIZE)
	}

	pub(crate) fn call_at_state(
		&self,
		at: &BlockId<Block>,
		function: &'static str,
		args: Vec<u8>,
		changes: &mut OverlayedChanges
	) -> error::Result<Vec<u8>> {
		let state = self.state_at(at)?;

		let execution_manager = || match self.api_execution_strategy {
			ExecutionStrategy::NativeWhenPossible => ExecutionManager::NativeWhenPossible,
			ExecutionStrategy::AlwaysWasm => ExecutionManager::AlwaysWasm,
			ExecutionStrategy::Both => ExecutionManager::Both(|wasm_result, native_result| {
				warn!("Consensus error between wasm and native runtime execution at block {:?}", at);
				warn!("   Function {:?}", function);
				warn!("   Native result {:?}", native_result);
				warn!("   Wasm result {:?}", wasm_result);
				wasm_result
			}),
		};

		self.executor.call_at_state(&state, changes, function, &args, execution_manager())
			.map(|res| res.0)
	}

	/// Get block hash by number.
	pub fn block_hash(&self, block_number: <<Block as BlockT>::Header as HeaderT>::Number) -> error::Result<Option<Block::Hash>> {
		self.backend.blockchain().hash(block_number)
	}

	/// Reads given header and generates CHT-based header proof for CHT of given size.
	pub fn header_proof_with_cht_size(&self, id: &BlockId<Block>, cht_size: u64) -> error::Result<(Block::Header, Vec<Vec<u8>>)> {
		let proof_error = || error::ErrorKind::Backend(format!("Failed to generate header proof for {:?}", id));
		let header = self.header(id)?.ok_or_else(|| error::ErrorKind::UnknownBlock(format!("{:?}", id)))?;
		let block_num = *header.number();
		let cht_num = cht::block_to_cht_number(cht_size, block_num).ok_or_else(proof_error)?;
		let cht_start = cht::start_number(cht_size, cht_num);
		let headers = (cht_start.as_()..).map(|num| self.block_hash(As::sa(num)));
		let proof = cht::build_proof::<Block::Header, Blake2Hasher, _, _>(cht_size, cht_num, ::std::iter::once(block_num), headers)?;
		Ok((header, proof))
	}

	/// Get pairs of (block, extrinsic) where key has been changed at given blocks range.
	/// Works only for runtimes that are supporting changes tries.
	pub fn key_changes(
		&self,
		first: Block::Hash,
		last: Block::Hash,
		key: &[u8]
	) -> error::Result<Vec<(NumberFor<Block>, u32)>> {
		let config = self.changes_trie_config()?;
		let storage = self.backend.changes_trie_storage();
		let (config, storage) = match (config, storage) {
			(Some(config), Some(storage)) => (config, storage),
			_ => return Err(error::ErrorKind::ChangesTriesNotSupported.into()),
		};

		key_changes::<_, Blake2Hasher>(
			&config,
			storage,
			self.require_block_number_from_id(&BlockId::Hash(first))?.as_(),
			&ChangesTrieAnchorBlockId {
				hash: convert_hash(&last),
				number: self.require_block_number_from_id(&BlockId::Hash(last))?.as_(),
			},
			self.backend.blockchain().info()?.best_number.as_(),
			key)
		.map_err(|err| error::ErrorKind::ChangesTrieAccessFailed(err).into())
		.map(|r| r.into_iter().map(|(b, e)| (As::sa(b), e)).collect())
	}

	/// Get proof for computation of (block, extrinsic) pairs where key has been changed at given blocks range.
	/// `min` is the hash of the first block, which changes trie root is known to the requester - when we're using
	/// changes tries from ascendants of this block, we should provide proofs for changes tries roots
	/// `max` is the hash of the last block known to the requester - we can't use changes tries from descendants
	/// of this block.
	/// Works only for runtimes that are supporting changes tries.
	pub fn key_changes_proof(
		&self,
		first: Block::Hash,
		last: Block::Hash,
		min: Block::Hash,
		max: Block::Hash,
		key: &[u8]
	) -> error::Result<ChangesProof<Block::Header>> {
		self.key_changes_proof_with_cht_size(
			first,
			last,
			min,
			max,
			key,
			cht::SIZE,
		)
	}

	/// Does the same work as `key_changes_proof`, but assumes that CHTs are of passed size.
	pub fn key_changes_proof_with_cht_size(
		&self,
		first: Block::Hash,
		last: Block::Hash,
		min: Block::Hash,
		max: Block::Hash,
		key: &[u8],
		cht_size: u64,
	) -> error::Result<ChangesProof<Block::Header>> {
		struct AccessedRootsRecorder<'a, Block: BlockT> {
			storage: &'a ChangesTrieStorage<Blake2Hasher>,
			min: u64,
			required_roots_proofs: Mutex<BTreeMap<NumberFor<Block>, H256>>,
		};

		impl<'a, Block: BlockT> ChangesTrieRootsStorage<Blake2Hasher> for AccessedRootsRecorder<'a, Block> {
			fn root(&self, anchor: &ChangesTrieAnchorBlockId<H256>, block: u64) -> Result<Option<H256>, String> {
				let root = self.storage.root(anchor, block)?;
				if block < self.min {
					if let Some(ref root) = root {
						self.required_roots_proofs.lock().insert(
							As::sa(block),
							root.clone()
						);
					}
				}
				Ok(root)
			}
		}

		impl<'a, Block: BlockT> ChangesTrieStorage<Blake2Hasher> for AccessedRootsRecorder<'a, Block> {
			fn get(&self, key: &H256) -> Result<Option<DBValue>, String> {
				self.storage.get(key)
			}
		}

		let config = self.changes_trie_config()?;
		let storage = self.backend.changes_trie_storage();
		let (config, storage) = match (config, storage) {
			(Some(config), Some(storage)) => (config, storage),
			_ => return Err(error::ErrorKind::ChangesTriesNotSupported.into()),
		};

		let min_number = self.require_block_number_from_id(&BlockId::Hash(min))?;
		let recording_storage = AccessedRootsRecorder::<Block> {
			storage,
			min: min_number.as_(),
			required_roots_proofs: Mutex::new(BTreeMap::new()),
		};

		let max_number = ::std::cmp::min(
			self.backend.blockchain().info()?.best_number,
			self.require_block_number_from_id(&BlockId::Hash(max))?,
		);

		// fetch key changes proof
		let key_changes_proof = key_changes_proof::<_, Blake2Hasher>(
			&config,
			&recording_storage,
			self.require_block_number_from_id(&BlockId::Hash(first))?.as_(),
			&ChangesTrieAnchorBlockId {
				hash: convert_hash(&last),
				number: self.require_block_number_from_id(&BlockId::Hash(last))?.as_(),
			},
			max_number.as_(),
			key
		)
		.map_err(|err| error::Error::from(error::ErrorKind::ChangesTrieAccessFailed(err)))?;

		// now gather proofs for all changes tries roots that were touched during key_changes_proof
		// execution AND are unknown (i.e. replaced with CHT) to the requester
		let roots = recording_storage.required_roots_proofs.into_inner();
		let roots_proof = self.changes_trie_roots_proof(cht_size, roots.keys().cloned())?;

		Ok(ChangesProof {
			max_block: max_number,
			proof: key_changes_proof,
			roots: roots.into_iter().map(|(n, h)| (n, convert_hash(&h))).collect(),
			roots_proof,
		})
	}

	/// Generate CHT-based proof for roots of changes tries at given blocks.
	fn changes_trie_roots_proof<I: IntoIterator<Item=NumberFor<Block>>>(
		&self,
		cht_size: u64,
		blocks: I
	) -> error::Result<Vec<Vec<u8>>> {
		// most probably we have touched several changes tries that are parts of the single CHT
		// => GroupBy changes tries by CHT number and then gather proof for the whole group at once
		let mut proof = HashSet::new();

		cht::for_each_cht_group::<Block::Header, _, _, _>(cht_size, blocks, |_, cht_num, cht_blocks| {
			let cht_proof = self.changes_trie_roots_proof_at_cht(cht_size, cht_num, cht_blocks)?;
			proof.extend(cht_proof);
			Ok(())
		}, ())?;

		Ok(proof.into_iter().collect())
	}

	/// Generates CHT-based proof for roots of changes tries at given blocks (that are part of single CHT).
	fn changes_trie_roots_proof_at_cht(
		&self,
		cht_size: u64,
		cht_num: NumberFor<Block>,
		blocks: Vec<NumberFor<Block>>
	) -> error::Result<Vec<Vec<u8>>> {
		let cht_start = cht::start_number(cht_size, cht_num);
		let roots = (cht_start.as_()..).map(|num| self.header(&BlockId::Number(As::sa(num)))
			.map(|block| block.and_then(|block| block.digest().log(DigestItem::as_changes_trie_root).cloned())));
		let proof = cht::build_proof::<Block::Header, Blake2Hasher, _, _>(cht_size, cht_num, blocks, roots)?;
		Ok(proof)
	}

	/// Create a new block, built on the head of the chain.
	pub fn new_block(
		&self
	) -> error::Result<block_builder::BlockBuilder<Block, Self>> where
		E: Clone + Send + Sync,
		RA: BlockBuilderAPI<Block>
	{
		block_builder::BlockBuilder::new(self)
	}

	/// Create a new block, built on top of `parent`.
	pub fn new_block_at(
		&self, parent: &BlockId<Block>
	) -> error::Result<block_builder::BlockBuilder<Block, Self>> where
		E: Clone + Send + Sync,
		RA: BlockBuilderAPI<Block>
	{
		block_builder::BlockBuilder::at_block(parent, &self)
	}

	// TODO [ToDr] Optimize and re-use tags from the pool.
	fn transaction_tags(
		&self,
		at: Block::Hash,
		body: &Option<Vec<Block::Extrinsic>>
	) -> error::Result<Vec<TransactionTag>> where
		RA: TaggedTransactionQueue<Block>,
		E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone,
	{
		let id = BlockId::Hash(at);
		Ok(match body {
			None => vec![],
			Some(ref extrinsics) => {
				let mut tags = vec![];
				for tx in extrinsics {
					let tx = self.runtime_api().validate_transaction(&id, &tx)?;
					match tx {
						TransactionValidity::Valid { mut provides, .. } => {
							tags.append(&mut provides);
						},
						// silently ignore invalid extrinsics,
						// cause they might just be inherent
						_ => {}
					}

				}
				tags
			},
		})
	}

	fn execute_and_import_block(
		&self,
		origin: BlockOrigin,
		hash: Block::Hash,
		import_headers: PrePostHeader<Block::Header>,
		justification: Justification,
		body: Option<Vec<Block::Extrinsic>>,
		authorities: Option<Vec<AuthorityId>>,
		finalized: bool,
		aux: Vec<(Vec<u8>, Option<Vec<u8>>)>,
	) -> error::Result<ImportResult> where
		RA: TaggedTransactionQueue<Block>,
		E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone,
	{
		let parent_hash = import_headers.post().parent_hash().clone();
		match self.backend.blockchain().status(BlockId::Hash(hash))? {
			blockchain::BlockStatus::InChain => return Ok(ImportResult::AlreadyInChain),
			blockchain::BlockStatus::Unknown => {},
		}

		let (last_best, last_best_number) = {
			let info = self.backend.blockchain().info()?;
			(info.best_hash, info.best_number)
		};

		// this is a fairly arbitrary choice of where to draw the line on making notifications,
		// but the general goal is to only make notifications when we are already fully synced
		// and get a new chain head.
		let make_notifications = match origin {
			BlockOrigin::NetworkBroadcast | BlockOrigin::Own | BlockOrigin::ConsensusBroadcast => true,
			BlockOrigin::Genesis | BlockOrigin::NetworkInitialSync | BlockOrigin::File => false,
		};

		// ensure parent block is finalized to maintain invariant that
		// finality is called sequentially.
		if finalized {
			self.apply_finality(parent_hash, last_best, make_notifications)?;
		}

		let tags = self.transaction_tags(parent_hash, &body)?;
		let mut transaction = self.backend.begin_operation(BlockId::Hash(parent_hash))?;
		let (storage_update, changes_update, storage_changes) = match transaction.state()? {
			Some(transaction_state) => {
				let mut overlay = Default::default();
				let mut r = self.executor.call_at_state(
					transaction_state,
					&mut overlay,
					"execute_block",
					&<Block as BlockT>::new(import_headers.pre().clone(), body.clone().unwrap_or_default()).encode(),
					match (origin, self.block_execution_strategy) {
						(BlockOrigin::NetworkInitialSync, _) | (_, ExecutionStrategy::NativeWhenPossible) =>
							ExecutionManager::NativeWhenPossible,
						(_, ExecutionStrategy::AlwaysWasm) => ExecutionManager::AlwaysWasm,
						_ => ExecutionManager::Both(|wasm_result, native_result| {
							let header = import_headers.post();
							warn!("Consensus error between wasm and native block execution at block {}", hash);
							warn!("   Header {:?}", header);
							warn!("   Native result {:?}", native_result);
							warn!("   Wasm result {:?}", wasm_result);
							telemetry!("block.execute.consensus_failure";
								"hash" => ?hash,
								"origin" => ?origin,
								"header" => ?header
							);
							wasm_result
						}),
					},
				);
				let (_, storage_update, changes_update) = r?;
				overlay.commit_prospective();
				(Some(storage_update), Some(changes_update), Some(overlay.into_committed()))
			},
			None => (None, None, None)
		};

		// TODO: non longest-chain rule.
		let is_new_best = finalized || import_headers.post().number() > &last_best_number;
		let leaf_state = if finalized {
			::backend::NewBlockState::Final
		} else if is_new_best {
			::backend::NewBlockState::Best
		} else {
			::backend::NewBlockState::Normal
		};

		trace!("Imported {}, (#{}), best={}, origin={:?}", hash, import_headers.post().number(), is_new_best, origin);

		transaction.set_block_data(
			import_headers.post().clone(),
			body,
			Some(justification),
			leaf_state,
		)?;

		if let Some(authorities) = authorities {
			transaction.update_authorities(authorities);
		}
		if let Some(storage_update) = storage_update {
			transaction.update_storage(storage_update)?;
		}
		if let Some(Some(changes_update)) = changes_update {
			transaction.update_changes_trie(changes_update)?;
		}

		transaction.set_aux(aux)?;
		self.backend.commit_operation(transaction)?;

		if make_notifications {
			if let Some(storage_changes) = storage_changes {
				// TODO [ToDr] How to handle re-orgs? Should we re-emit all storage changes?
				self.storage_notifications.lock()
					.trigger(&hash, storage_changes);
			}

			if finalized {
				let notification = FinalityNotification::<Block> {
					hash,
					header: import_headers.post().clone(),
				};

				self.finality_notification_sinks.lock()
					.retain(|sink| sink.unbounded_send(notification.clone()).is_ok());
			}

			let notification = BlockImportNotification::<Block> {
				hash,
				origin,
				header: import_headers.into_post(),
				is_new_best,
				tags,
			};

			self.import_notification_sinks.lock()
				.retain(|sink| sink.unbounded_send(notification.clone()).is_ok());
		}

		Ok(ImportResult::Queued)
	}

	/// Finalizes all blocks up to given.
	fn apply_finality(&self, block: Block::Hash, best_block: Block::Hash, notify: bool) -> error::Result<()> {
		// find tree route from last finalized to given block.
		let last_finalized = self.backend.blockchain().last_finalized()?;

		if block == last_finalized { return Ok(()) }
		let route_from_finalized = ::blockchain::tree_route(
			self.backend.blockchain(),
			BlockId::Hash(last_finalized),
			BlockId::Hash(block),
		)?;

		if let Some(retracted) = route_from_finalized.retracted().get(0) {
			warn!("Safety violation: attempted to revert finalized block {:?} which is not in the \
				same chain as last finalized {:?}", retracted, last_finalized);

			bail!(error::ErrorKind::NotInFinalizedChain);
		}

		let route_from_best = ::blockchain::tree_route(
			self.backend.blockchain(),
			BlockId::Hash(best_block),
			BlockId::Hash(block),
		)?;

		// if the block is not a direct ancestor of the current best chain,
		// then some other block is the common ancestor.
		if route_from_best.common_block().hash != block {
			// TODO: reorganize best block to be the best chain containing
			// `block`.
		}

		for finalize_new in route_from_finalized.enacted() {
			self.backend.finalize_block(BlockId::Hash(finalize_new.hash))?;
		}

		if notify {
			// sometimes when syncing, tons of blocks can be finalized at once.
			// we'll send notifications spuriously in that case.
			const MAX_TO_NOTIFY: usize = 256;
			let enacted = route_from_finalized.enacted();
			let start = enacted.len() - ::std::cmp::min(enacted.len(), MAX_TO_NOTIFY);
			let mut sinks = self.finality_notification_sinks.lock();
			for finalized in &enacted[start..] {
				let header = self.header(&BlockId::Hash(finalized.hash))?
					.expect("header already known to exist in DB because it is indicated in the tree route; qed");
				let notification = FinalityNotification {
					header,
					hash: finalized.hash,
				};

				sinks.retain(|sink| sink.unbounded_send(notification.clone()).is_ok());
			}
		}

		Ok(())
	}

	/// Finalize a block. This will implicitly finalize all blocks up to it and
	/// fire finality notifications.
	///
	/// Pass a flag to indicate whether finality notifications should be propagated.
	/// This is usually tied to some synchronization state, where we don't send notifications
	/// while performing major synchronization work.
	pub fn finalize_block(&self, id: BlockId<Block>, notify: bool) -> error::Result<()> {
		let last_best = self.backend.blockchain().info()?.best_hash;
		let to_finalize_hash = match id {
			BlockId::Hash(h) => h,
			BlockId::Number(n) => self.backend.blockchain().hash(n)?
				.ok_or_else(|| error::ErrorKind::UnknownBlock(format!("No block with number {:?}", n)))?,
		};

		self.apply_finality(to_finalize_hash, last_best, notify)
	}

	/// Attempts to revert the chain by `n` blocks. Returns the number of blocks that were
	/// successfully reverted.
	pub fn revert(&self, n: NumberFor<Block>) -> error::Result<NumberFor<Block>> {
		Ok(self.backend.revert(n)?)
	}

	/// Get blockchain info.
	pub fn info(&self) -> error::Result<ClientInfo<Block>> {
		let info = self.backend.blockchain().info().map_err(|e| error::Error::from_blockchain(Box::new(e)))?;
		Ok(ClientInfo {
			chain: info,
			best_queued_hash: None,
			best_queued_number: None,
		})
	}

	/// Get block status.
	pub fn block_status(&self, id: &BlockId<Block>) -> error::Result<BlockStatus> {
		// TODO: more efficient implementation
		if let BlockId::Hash(ref h) = id {
			if self.importing_block.read().as_ref().map_or(false, |importing| h == importing) {
				return Ok(BlockStatus::Queued);
			}
		}
		match self.backend.blockchain().header(*id).map_err(|e| error::Error::from_blockchain(Box::new(e)))?.is_some() {
			true => Ok(BlockStatus::InChain),
			false => Ok(BlockStatus::Unknown),
		}
	}

	/// Convert an arbitrary block ID into a block hash, returning error if the block is unknown.
	fn require_block_number_from_id(&self, id: &BlockId<Block>) -> error::Result<NumberFor<Block>> {
		self.backend.blockchain().block_number_from_id(id)
			.and_then(|n| n.ok_or_else(|| error::ErrorKind::UnknownBlock(format!("{}", id)).into()))
	}

	/// Get block header by id.
	pub fn header(&self, id: &BlockId<Block>) -> error::Result<Option<<Block as BlockT>::Header>> {
		self.backend.blockchain().header(*id)
	}

	/// Get block body by id.
	pub fn body(&self, id: &BlockId<Block>) -> error::Result<Option<Vec<<Block as BlockT>::Extrinsic>>> {
		self.backend.blockchain().body(*id)
	}

	/// Get block justification set by id.
	pub fn justification(&self, id: &BlockId<Block>) -> error::Result<Option<Justification>> {
		self.backend.blockchain().justification(*id)
	}

	/// Get full block by id.
	pub fn block(&self, id: &BlockId<Block>)
		-> error::Result<Option<SignedBlock<Block>>>
	{
		Ok(match (self.header(id)?, self.body(id)?, self.justification(id)?) {
			(Some(header), Some(extrinsics), Some(justification)) =>
				Some(SignedBlock { block: Block::new(header, extrinsics), justification }),
			_ => None,
		})
	}

	/// Get best block header.
	pub fn best_block_header(&self) -> error::Result<<Block as BlockT>::Header> {
		let info = self.backend.blockchain().info().map_err(|e| error::Error::from_blockchain(Box::new(e)))?;
		Ok(self.header(&BlockId::Hash(info.best_hash))?.expect("Best block header must always exist"))
	}

	/// Get the most recent block hash of the best (longest) chains
	/// that contain block with the given `target_hash`.
	/// If `maybe_max_block_number` is `Some(max_block_number)`
	/// the search is limited to block `numbers <= max_block_number`.
	/// in other words as if there were no blocks greater `max_block_number`.
	/// TODO [snd] possibly implement this on blockchain::Backend and just redirect here
	/// Returns `Ok(None)` if `target_hash` is not found in search space.
	/// TODO [snd] write down time complexity
	pub fn best_containing(&self, target_hash: Block::Hash, maybe_max_number: Option<NumberFor<Block>>)
		-> error::Result<Option<Block::Hash>>
	{
		let target_header = {
			match self.backend.blockchain().header(BlockId::Hash(target_hash))? {
				Some(x) => x,
				// target not in blockchain
				None => { return Ok(None); },
			}
		};

		if let Some(max_number) = maybe_max_number {
			// target outside search range
			if target_header.number() > &max_number {
				return Ok(None);
			}
		}

		let (leaves, best_already_checked) = {
			// ensure no blocks are imported during this code block.
			// an import could trigger a reorg which could change the canonical chain.
			// we depend on the canonical chain staying the same during this code block.
			let _import_lock = self.import_lock.lock();

			let info = self.backend.blockchain().info()?;

			let canon_hash = self.backend.blockchain().hash(*target_header.number())?
				.ok_or_else(|| error::Error::from(format!("failed to get hash for block number {}", target_header.number())))?;

			if canon_hash == target_hash {
				if let Some(max_number) = maybe_max_number {
					// something has to guarantee that max_number is in chain
					return Ok(Some(self.backend.blockchain().hash(max_number)?.ok_or_else(|| error::Error::from(format!("failed to get hash for block number {}", max_number)))?));
				} else {
					return Ok(Some(info.best_hash));
				}
			}
			(self.backend.blockchain().leaves()?, info.best_hash)
		};

		// for each chain. longest chain first. shortest last
		for leaf_hash in leaves {
			// ignore canonical chain which we already checked above
			if leaf_hash == best_already_checked {
				continue;
			}

			// start at the leaf
			let mut current_hash = leaf_hash;

			// if search is not restricted then the leaf is the best
			let mut best_hash = leaf_hash;

			// go backwards entering the search space
			// waiting until we are <= max_number
			if let Some(max_number) = maybe_max_number {
				loop {
					// TODO [snd] this should be a panic
					let current_header = self.backend.blockchain().header(BlockId::Hash(current_hash.clone()))?
						.ok_or_else(|| error::Error::from(format!("failed to get header for hash {}", current_hash)))?;

					if current_header.number() <= &max_number {
						best_hash = current_header.hash();
						break;
					}

					current_hash = *current_header.parent_hash();
				}
			}

			// go backwards through the chain (via parent links)
			loop {
				// until we find target
				if current_hash == target_hash {
					return Ok(Some(best_hash));
				}

				// TODO [snd] this should be a panic
				let current_header = self.backend.blockchain().header(BlockId::Hash(current_hash.clone()))?
					.ok_or_else(|| error::Error::from(format!("failed to get header for hash {}", current_hash)))?;

				// stop search in this chain once we go below the target's block number
				if current_header.number() < target_header.number() {
					break;
				}

				current_hash = *current_header.parent_hash();
			}
		}

		unreachable!("this is a bug. `target_hash` is in blockchain but wasn't found following all leaves backwards");
	}

	fn changes_trie_config(&self) -> Result<Option<ChangesTrieConfiguration>, Error> {
		Ok(self.backend.state_at(BlockId::Number(self.backend.blockchain().info()?.best_number))?
			.storage(well_known_keys::CHANGES_TRIE_CONFIG)
			.map_err(|e| error::Error::from_state(Box::new(e)))?
			.and_then(|c| Decode::decode(&mut &*c)))
	}
}

impl<B, E, Block, RA> ChainHeaderBackend<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync,
	Block: BlockT<Hash=H256>,
	RA: Send + Sync
{
	fn header(&self, id: BlockId<Block>) -> error::Result<Option<Block::Header>> {
		self.backend.blockchain().header(id)
	}

	fn info(&self) -> error::Result<blockchain::Info<Block>> {
		self.backend.blockchain().info()
	}

	fn status(&self, id: BlockId<Block>) -> error::Result<blockchain::BlockStatus> {
		self.backend.blockchain().status(id)
	}

	fn number(&self, hash: Block::Hash) -> error::Result<Option<<<Block as BlockT>::Header as HeaderT>::Number>> {
		self.backend.blockchain().number(hash)
	}

	fn hash(&self, number: NumberFor<Block>) -> error::Result<Option<Block::Hash>> {
		self.backend.blockchain().hash(number)
	}
}

impl<B, E, Block, RA> ProvideRuntimeApi for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Clone + Send + Sync,
	Block: BlockT<Hash=H256>,
	RA: CoreAPI<Block>
{
	type Api = RA;

	fn runtime_api<'a>(&'a self) -> ApiRef<'a, Self::Api> {
		Self::Api::construct_runtime_api(self)
	}
}

impl<B, E, Block, RA> CallApiAt<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Clone + Send + Sync,
	Block: BlockT<Hash=H256>,
	RA: CoreAPI<Block>, // not strictly necessary at the moment
						// but we want to bound to make sure the API is actually available.
{
	fn call_api_at(
		&self,
		at: &BlockId<Block>,
		function: &'static str,
		args: Vec<u8>,
		changes: &mut OverlayedChanges,
		initialised_block: &mut Option<BlockId<Block>>,
	) -> error::Result<Vec<u8>> {
		//TODO: Find a better way to prevent double block initialization
		if function != "initialise_block" && initialised_block.map(|id| id != *at).unwrap_or(true) {
			let parent = at;
			let header = <<Block as BlockT>::Header as HeaderT>::new(
				self.block_number_from_id(parent)?
					.ok_or_else(|| error::ErrorKind::UnknownBlock(format!("{:?}", parent)))?
				+ As::sa(1),
				Default::default(),
				Default::default(),
				self.block_hash_from_id(&parent)?
					.ok_or_else(|| error::ErrorKind::UnknownBlock(format!("{:?}", parent)))?,
				Default::default()
			);
			self.call_at_state(at, "initialise_block", header.encode(), changes)?;
			*initialised_block = Some(*at);
		}

		self.call_at_state(at, function, args, changes)
	}
}


impl<B, E, Block, RA> consensus::BlockImport<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Clone + Send + Sync,
	Block: BlockT<Hash=H256>,
	RA: TaggedTransactionQueue<Block>
{
	type Error = Error;

	/// Import a checked and validated block
	fn import_block(
		&self,
		import_block: ImportBlock<Block>,
		new_authorities: Option<Vec<AuthorityId>>,
	) -> Result<ImportResult, Self::Error> {
		use runtime_primitives::traits::Digest;

		let ImportBlock {
			origin,
			header,
			justification,
			post_digests,
			body,
			finalized,
			auxiliary,
		} = import_block;
		let parent_hash = header.parent_hash().clone();

		match self.backend.blockchain().status(BlockId::Hash(parent_hash))? {
			blockchain::BlockStatus::InChain => {},
			blockchain::BlockStatus::Unknown => return Ok(ImportResult::UnknownParent),
		}

		let import_headers = if post_digests.is_empty() {
			PrePostHeader::Same(header)
		} else {
			let mut post_header = header.clone();
			for item in post_digests {
				post_header.digest_mut().push(item);
			}
			PrePostHeader::Different(header, post_header)
		};

		let hash = import_headers.post().hash();
		let _import_lock = self.import_lock.lock();
		let height: u64 = import_headers.post().number().as_();
		*self.importing_block.write() = Some(hash);

		let result = self.execute_and_import_block(
			origin,
			hash,
			import_headers,
			justification,
			body,
			new_authorities,
			finalized,
			auxiliary,
		);

		*self.importing_block.write() = None;
		telemetry!("block.import";
			"height" => height,
			"best" => ?hash,
			"origin" => ?origin
		);
		result.map_err(|e| e.into())
	}
}

impl<B, E, Block, RA> consensus::Authorities<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Clone,
	Block: BlockT<Hash=H256>,
{
	type Error = Error;
	fn authorities(&self, at: &BlockId<Block>) -> Result<Vec<AuthorityId>, Self::Error> {
		self.authorities_at(at).map_err(|e| e.into())
	}
}

impl<B, E, Block, RA> CurrentHeight for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Clone,
	Block: BlockT<Hash=H256>,
{
	type BlockNumber = <Block::Header as HeaderT>::Number;
	fn current_height(&self) -> Self::BlockNumber {
		self.backend.blockchain().info().map(|i| i.best_number).unwrap_or_else(|_| Zero::zero())
	}
}

impl<B, E, Block, RA> BlockNumberToHash for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Clone,
	Block: BlockT<Hash=H256>,
{
	type BlockNumber = <Block::Header as HeaderT>::Number;
	type Hash = Block::Hash;
	fn block_number_to_hash(&self, n: Self::BlockNumber) -> Option<Self::Hash> {
		self.block_hash(n).unwrap_or(None)
	}
}


impl<B, E, Block, RA> BlockchainEvents<Block> for Client<B, E, Block, RA>
where
	E: CallExecutor<Block, Blake2Hasher>,
	Block: BlockT<Hash=H256>,
{
	/// Get block import event stream.
	fn import_notification_stream(&self) -> ImportNotifications<Block> {
		let (sink, stream) = mpsc::unbounded();
		self.import_notification_sinks.lock().push(sink);
		stream
	}

	fn finality_notification_stream(&self) -> FinalityNotifications<Block> {
		let (sink, stream) = mpsc::unbounded();
		self.finality_notification_sinks.lock().push(sink);
		stream
	}

	/// Get storage changes event stream.
	fn storage_changes_notification_stream(&self, filter_keys: Option<&[StorageKey]>) -> error::Result<StorageEventStream<Block::Hash>> {
		Ok(self.storage_notifications.lock().listen(filter_keys))
	}
}

impl<B, E, Block, RA> ChainHead<Block> for Client<B, E, Block, RA>
where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
	Block: BlockT<Hash=H256>,
{
	fn best_block_header(&self) -> error::Result<<Block as BlockT>::Header> {
		Client::best_block_header(self)
	}

	fn leaves(&self) -> Result<Vec<<Block as BlockT>::Hash>, error::Error> {
		self.backend.blockchain().leaves()
	}
}

impl<B, E, Block, RA> BlockBody<Block> for Client<B, E, Block, RA>
	where
		B: backend::Backend<Block, Blake2Hasher>,
		E: CallExecutor<Block, Blake2Hasher>,
		Block: BlockT<Hash=H256>,
{
	fn block_body(&self, id: &BlockId<Block>) -> error::Result<Option<Vec<<Block as BlockT>::Extrinsic>>> {
		self.body(id)
	}
}

#[cfg(test)]
pub(crate) mod tests {
	use std::collections::HashMap;
	use super::*;
	use keyring::Keyring;
	use primitives::twox_128;
	use runtime_primitives::traits::DigestItem as DigestItemT;
	use runtime_primitives::generic::DigestItem;
	use test_client::{self, TestClient};
	use consensus::BlockOrigin;
	use test_client::client::backend::Backend as TestBackend;
	use test_client::BlockBuilderExt;
	use test_client::runtime::{self, Block, Transfer, RuntimeApi, test_api::TestAPI};

	/// Returns tuple, consisting of:
	/// 1) test client pre-filled with blocks changing balances;
	/// 2) roots of changes tries for these blocks
	/// 3) test cases in form (begin, end, key, vec![(block, extrinsic)]) that are required to pass
	pub fn prepare_client_with_key_changes() -> (
		test_client::client::Client<test_client::Backend, test_client::Executor, Block, RuntimeApi>,
		Vec<H256>,
		Vec<(u64, u64, Vec<u8>, Vec<(u64, u32)>)>,
	) {
		// prepare block structure
		let blocks_transfers = vec![
			vec![(Keyring::Alice, Keyring::Dave), (Keyring::Bob, Keyring::Dave)],
			vec![(Keyring::Charlie, Keyring::Eve)],
			vec![],
			vec![(Keyring::Alice, Keyring::Dave)],
		];

		// prepare client ang import blocks
		let mut local_roots = Vec::new();
		let remote_client = test_client::new_with_changes_trie();
		let mut nonces: HashMap<_, u64> = Default::default();
		for (i, block_transfers) in blocks_transfers.into_iter().enumerate() {
			let mut builder = remote_client.new_block().unwrap();
			for (from, to) in block_transfers {
				builder.push_transfer(Transfer {
					from: from.to_raw_public().into(),
					to: to.to_raw_public().into(),
					amount: 1,
					nonce: *nonces.entry(from).and_modify(|n| { *n = *n + 1 }).or_default(),
				}).unwrap();
			}
			remote_client.justify_and_import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();

			let header = remote_client.header(&BlockId::Number(i as u64 + 1)).unwrap().unwrap();
			let trie_root = header.digest().log(DigestItem::as_changes_trie_root)
				.map(|root| H256::from_slice(root.as_ref()))
				.unwrap();
			local_roots.push(trie_root);
		}

		// prepare test cases
		let alice = twox_128(&runtime::system::balance_of_key(Keyring::Alice.to_raw_public().into())).to_vec();
		let bob = twox_128(&runtime::system::balance_of_key(Keyring::Bob.to_raw_public().into())).to_vec();
		let charlie = twox_128(&runtime::system::balance_of_key(Keyring::Charlie.to_raw_public().into())).to_vec();
		let dave = twox_128(&runtime::system::balance_of_key(Keyring::Dave.to_raw_public().into())).to_vec();
		let eve = twox_128(&runtime::system::balance_of_key(Keyring::Eve.to_raw_public().into())).to_vec();
		let ferdie = twox_128(&runtime::system::balance_of_key(Keyring::Ferdie.to_raw_public().into())).to_vec();
		let test_cases = vec![
			(1, 4, alice.clone(), vec![(4, 0), (1, 0)]),
			(1, 3, alice.clone(), vec![(1, 0)]),
			(2, 4, alice.clone(), vec![(4, 0)]),
			(2, 3, alice.clone(), vec![]),

			(1, 4, bob.clone(), vec![(1, 1)]),
			(1, 1, bob.clone(), vec![(1, 1)]),
			(2, 4, bob.clone(), vec![]),

			(1, 4, charlie.clone(), vec![(2, 0)]),

			(1, 4, dave.clone(), vec![(4, 0), (1, 1), (1, 0)]),
			(1, 1, dave.clone(), vec![(1, 1), (1, 0)]),
			(3, 4, dave.clone(), vec![(4, 0)]),

			(1, 4, eve.clone(), vec![(2, 0)]),
			(1, 1, eve.clone(), vec![]),
			(3, 4, eve.clone(), vec![]),

			(1, 4, ferdie.clone(), vec![]),
		];

		(remote_client, local_roots, test_cases)
	}

	#[test]
	fn client_initialises_from_genesis_ok() {
		let client = test_client::new();

		assert_eq!(
			client.runtime_api().balance_of(
				&BlockId::Number(client.info().unwrap().chain.best_number),
				&Keyring::Alice.to_raw_public()
			).unwrap(),
			1000
		);
		assert_eq!(
			client.runtime_api().balance_of(
				&BlockId::Number(client.info().unwrap().chain.best_number),
				&Keyring::Ferdie.to_raw_public()
			).unwrap(),
			0
		);
	}

	#[test]
	fn authorities_call_works() {
		let client = test_client::new();

		assert_eq!(client.info().unwrap().chain.best_number, 0);
		assert_eq!(client.authorities_at(&BlockId::Number(0)).unwrap(), vec![
			Keyring::Alice.to_raw_public().into(),
			Keyring::Bob.to_raw_public().into(),
			Keyring::Charlie.to_raw_public().into()
		]);
	}

	#[test]
	fn block_builder_works_with_no_transactions() {
		let client = test_client::new();

		let builder = client.new_block().unwrap();

		client.justify_and_import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();

		assert_eq!(client.info().unwrap().chain.best_number, 1);
	}

	#[test]
	fn block_builder_works_with_transactions() {
		let client = test_client::new();

		let mut builder = client.new_block().unwrap();

		builder.push_transfer(Transfer {
			from: Keyring::Alice.to_raw_public().into(),
			to: Keyring::Ferdie.to_raw_public().into(),
			amount: 42,
			nonce: 0,
		}).unwrap();

		client.justify_and_import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();

		assert_eq!(client.info().unwrap().chain.best_number, 1);
		assert!(client.state_at(&BlockId::Number(1)).unwrap() != client.state_at(&BlockId::Number(0)).unwrap());
		assert_eq!(
			client.runtime_api().balance_of(
				&BlockId::Number(client.info().unwrap().chain.best_number),
				&Keyring::Alice.to_raw_public()
			).unwrap(),
			958
		);
		assert_eq!(
			client.runtime_api().balance_of(
				&BlockId::Number(client.info().unwrap().chain.best_number),
				&Keyring::Ferdie.to_raw_public()
			).unwrap(),
			42
		);
	}

	#[test]
	fn client_uses_authorities_from_blockchain_cache() {
		let client = test_client::new();
		test_client::client::in_mem::cache_authorities_at(
			client.backend().blockchain(),
			Default::default(),
			Some(vec![[1u8; 32].into()]));
		assert_eq!(client.authorities_at(
			&BlockId::Hash(Default::default())).unwrap(),
			vec![[1u8; 32].into()]);
	}

	#[test]
	fn block_builder_does_not_include_invalid() {
		let client = test_client::new();

		let mut builder = client.new_block().unwrap();

		builder.push_transfer(Transfer {
			from: Keyring::Alice.to_raw_public().into(),
			to: Keyring::Ferdie.to_raw_public().into(),
			amount: 42,
			nonce: 0,
		}).unwrap();

		assert!(builder.push_transfer(Transfer {
			from: Keyring::Eve.to_raw_public().into(),
			to: Keyring::Alice.to_raw_public().into(),
			amount: 42,
			nonce: 0,
		}).is_err());

		client.justify_and_import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();

		assert_eq!(client.info().unwrap().chain.best_number, 1);
		assert!(client.state_at(&BlockId::Number(1)).unwrap() != client.state_at(&BlockId::Number(0)).unwrap());
		assert_eq!(client.body(&BlockId::Number(1)).unwrap().unwrap().len(), 1)
	}

	#[test]
	fn best_containing_with_genesis_block() {
		// block tree:
		// G

		let client = test_client::new();

		let genesis_hash = client.info().unwrap().chain.genesis_hash;

		assert_eq!(genesis_hash.clone(), client.best_containing(genesis_hash.clone(), None).unwrap().unwrap());
	}

	#[test]
	fn best_containing_with_hash_not_found() {
		// block tree:
		// G

		let client = test_client::new();

		let uninserted_block = client.new_block().unwrap().bake().unwrap();

		assert_eq!(None, client.best_containing(uninserted_block.hash().clone(), None).unwrap());
	}

	#[test]
	fn best_containing_with_single_chain_3_blocks() {
		// block tree:
		// G -> A1 -> A2

		let client = test_client::new();

		// G -> A1
		let a1 = client.new_block().unwrap().bake().unwrap();
		client.justify_and_import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block().unwrap().bake().unwrap();
		client.justify_and_import(BlockOrigin::Own, a2.clone()).unwrap();

		let genesis_hash = client.info().unwrap().chain.genesis_hash;

		assert_eq!(a2.hash(), client.best_containing(genesis_hash, None).unwrap().unwrap());
		assert_eq!(a2.hash(), client.best_containing(a1.hash(), None).unwrap().unwrap());
		assert_eq!(a2.hash(), client.best_containing(a2.hash(), None).unwrap().unwrap());
	}

	#[test]
	fn best_containing_with_multiple_forks() {
		// NOTE: we use the version of the trait from `test_client`
		// because that is actually different than the version linked to
		// in the test facade crate.
		use test_client::blockchain::Backend as BlockchainBackendT;

		// block tree:
		// G -> A1 -> A2 -> A3 -> A4 -> A5
		//      A1 -> B2 -> B3 -> B4
		//	          B2 -> C3
		//	    A1 -> D2
		let client = test_client::new();

		// G -> A1
		let a1 = client.new_block().unwrap().bake().unwrap();
		client.justify_and_import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block_at(&BlockId::Hash(a1.hash())).unwrap().bake().unwrap();
		client.justify_and_import(BlockOrigin::Own, a2.clone()).unwrap();

		// A2 -> A3
		let a3 = client.new_block_at(&BlockId::Hash(a2.hash())).unwrap().bake().unwrap();
		client.justify_and_import(BlockOrigin::Own, a3.clone()).unwrap();

		// A3 -> A4
		let a4 = client.new_block_at(&BlockId::Hash(a3.hash())).unwrap().bake().unwrap();
		client.justify_and_import(BlockOrigin::Own, a4.clone()).unwrap();

		// A4 -> A5
		let a5 = client.new_block_at(&BlockId::Hash(a4.hash())).unwrap().bake().unwrap();
		client.justify_and_import(BlockOrigin::Own, a5.clone()).unwrap();

		// A1 -> B2
		let mut builder = client.new_block_at(&BlockId::Hash(a1.hash())).unwrap();
		// this push is required as otherwise B2 has the same hash as A2 and won't get imported
		builder.push_transfer(Transfer {
			from: Keyring::Alice.to_raw_public().into(),
			to: Keyring::Ferdie.to_raw_public().into(),
			amount: 41,
			nonce: 0,
		}).unwrap();
		let b2 = builder.bake().unwrap();
		client.justify_and_import(BlockOrigin::Own, b2.clone()).unwrap();

		// B2 -> B3
		let b3 = client.new_block_at(&BlockId::Hash(b2.hash())).unwrap().bake().unwrap();
		client.justify_and_import(BlockOrigin::Own, b3.clone()).unwrap();

		// B3 -> B4
		let b4 = client.new_block_at(&BlockId::Hash(b3.hash())).unwrap().bake().unwrap();
		client.justify_and_import(BlockOrigin::Own, b4.clone()).unwrap();

		// // B2 -> C3
		let mut builder = client.new_block_at(&BlockId::Hash(b2.hash())).unwrap();
		// this push is required as otherwise C3 has the same hash as B3 and won't get imported
		builder.push_transfer(Transfer {
			from: Keyring::Alice.to_raw_public().into(),
			to: Keyring::Ferdie.to_raw_public().into(),
			amount: 1,
			nonce: 1,
		}).unwrap();
		let c3 = builder.bake().unwrap();
		client.justify_and_import(BlockOrigin::Own, c3.clone()).unwrap();

		// A1 -> D2
		let mut builder = client.new_block_at(&BlockId::Hash(a1.hash())).unwrap();
		// this push is required as otherwise D2 has the same hash as B2 and won't get imported
		builder.push_transfer(Transfer {
			from: Keyring::Alice.to_raw_public().into(),
			to: Keyring::Ferdie.to_raw_public().into(),
			amount: 1,
			nonce: 0,
		}).unwrap();
		let d2 = builder.bake().unwrap();
		client.justify_and_import(BlockOrigin::Own, d2.clone()).unwrap();

		assert_eq!(client.info().unwrap().chain.best_hash, a5.hash());

		let genesis_hash = client.info().unwrap().chain.genesis_hash;
		let leaves = BlockchainBackendT::leaves(client.backend().blockchain()).unwrap();

		assert!(leaves.contains(&a5.hash()));
		assert!(leaves.contains(&b4.hash()));
		assert!(leaves.contains(&c3.hash()));
		assert!(leaves.contains(&d2.hash()));
		assert_eq!(leaves.len(), 4);

		// search without restriction

		assert_eq!(a5.hash(), client.best_containing(genesis_hash, None).unwrap().unwrap());
		assert_eq!(a5.hash(), client.best_containing(a1.hash(), None).unwrap().unwrap());
		assert_eq!(a5.hash(), client.best_containing(a2.hash(), None).unwrap().unwrap());
		assert_eq!(a5.hash(), client.best_containing(a3.hash(), None).unwrap().unwrap());
		assert_eq!(a5.hash(), client.best_containing(a4.hash(), None).unwrap().unwrap());
		assert_eq!(a5.hash(), client.best_containing(a5.hash(), None).unwrap().unwrap());

		assert_eq!(b4.hash(), client.best_containing(b2.hash(), None).unwrap().unwrap());
		assert_eq!(b4.hash(), client.best_containing(b3.hash(), None).unwrap().unwrap());
		assert_eq!(b4.hash(), client.best_containing(b4.hash(), None).unwrap().unwrap());

		assert_eq!(c3.hash(), client.best_containing(c3.hash(), None).unwrap().unwrap());

		assert_eq!(d2.hash(), client.best_containing(d2.hash(), None).unwrap().unwrap());


		// search only blocks with number <= 5. equivalent to without restriction for this scenario

		assert_eq!(a5.hash(), client.best_containing(genesis_hash, Some(5)).unwrap().unwrap());
		assert_eq!(a5.hash(), client.best_containing(a1.hash(), Some(5)).unwrap().unwrap());
		assert_eq!(a5.hash(), client.best_containing(a2.hash(), Some(5)).unwrap().unwrap());
		assert_eq!(a5.hash(), client.best_containing(a3.hash(), Some(5)).unwrap().unwrap());
		assert_eq!(a5.hash(), client.best_containing(a4.hash(), Some(5)).unwrap().unwrap());
		assert_eq!(a5.hash(), client.best_containing(a5.hash(), Some(5)).unwrap().unwrap());

		assert_eq!(b4.hash(), client.best_containing(b2.hash(), Some(5)).unwrap().unwrap());
		assert_eq!(b4.hash(), client.best_containing(b3.hash(), Some(5)).unwrap().unwrap());
		assert_eq!(b4.hash(), client.best_containing(b4.hash(), Some(5)).unwrap().unwrap());

		assert_eq!(c3.hash(), client.best_containing(c3.hash(), Some(5)).unwrap().unwrap());

		assert_eq!(d2.hash(), client.best_containing(d2.hash(), Some(5)).unwrap().unwrap());


		// search only blocks with number <= 4

		assert_eq!(a4.hash(), client.best_containing(genesis_hash, Some(4)).unwrap().unwrap());
		assert_eq!(a4.hash(), client.best_containing(a1.hash(), Some(4)).unwrap().unwrap());
		assert_eq!(a4.hash(), client.best_containing(a2.hash(), Some(4)).unwrap().unwrap());
		assert_eq!(a4.hash(), client.best_containing(a3.hash(), Some(4)).unwrap().unwrap());
		assert_eq!(a4.hash(), client.best_containing(a4.hash(), Some(4)).unwrap().unwrap());
		assert_eq!(None, client.best_containing(a5.hash(), Some(4)).unwrap());

		assert_eq!(b4.hash(), client.best_containing(b2.hash(), Some(4)).unwrap().unwrap());
		assert_eq!(b4.hash(), client.best_containing(b3.hash(), Some(4)).unwrap().unwrap());
		assert_eq!(b4.hash(), client.best_containing(b4.hash(), Some(4)).unwrap().unwrap());

		assert_eq!(c3.hash(), client.best_containing(c3.hash(), Some(4)).unwrap().unwrap());

		assert_eq!(d2.hash(), client.best_containing(d2.hash(), Some(4)).unwrap().unwrap());


		// search only blocks with number <= 3

		assert_eq!(a3.hash(), client.best_containing(genesis_hash, Some(3)).unwrap().unwrap());
		assert_eq!(a3.hash(), client.best_containing(a1.hash(), Some(3)).unwrap().unwrap());
		assert_eq!(a3.hash(), client.best_containing(a2.hash(), Some(3)).unwrap().unwrap());
		assert_eq!(a3.hash(), client.best_containing(a3.hash(), Some(3)).unwrap().unwrap());
		assert_eq!(None, client.best_containing(a4.hash(), Some(3)).unwrap());
		assert_eq!(None, client.best_containing(a5.hash(), Some(3)).unwrap());

		assert_eq!(b3.hash(), client.best_containing(b2.hash(), Some(3)).unwrap().unwrap());
		assert_eq!(b3.hash(), client.best_containing(b3.hash(), Some(3)).unwrap().unwrap());
		assert_eq!(None, client.best_containing(b4.hash(), Some(3)).unwrap());

		assert_eq!(c3.hash(), client.best_containing(c3.hash(), Some(3)).unwrap().unwrap());

		assert_eq!(d2.hash(), client.best_containing(d2.hash(), Some(3)).unwrap().unwrap());


		// search only blocks with number <= 2

		assert_eq!(a2.hash(), client.best_containing(genesis_hash, Some(2)).unwrap().unwrap());
		assert_eq!(a2.hash(), client.best_containing(a1.hash(), Some(2)).unwrap().unwrap());
		assert_eq!(a2.hash(), client.best_containing(a2.hash(), Some(2)).unwrap().unwrap());
		assert_eq!(None, client.best_containing(a3.hash(), Some(2)).unwrap());
		assert_eq!(None, client.best_containing(a4.hash(), Some(2)).unwrap());
		assert_eq!(None, client.best_containing(a5.hash(), Some(2)).unwrap());

		assert_eq!(b2.hash(), client.best_containing(b2.hash(), Some(2)).unwrap().unwrap());
		assert_eq!(None, client.best_containing(b3.hash(), Some(2)).unwrap());
		assert_eq!(None, client.best_containing(b4.hash(), Some(2)).unwrap());

		assert_eq!(None, client.best_containing(c3.hash(), Some(2)).unwrap());

		assert_eq!(d2.hash(), client.best_containing(d2.hash(), Some(2)).unwrap().unwrap());


		// search only blocks with number <= 1

		assert_eq!(a1.hash(), client.best_containing(genesis_hash, Some(1)).unwrap().unwrap());
		assert_eq!(a1.hash(), client.best_containing(a1.hash(), Some(1)).unwrap().unwrap());
		assert_eq!(None, client.best_containing(a2.hash(), Some(1)).unwrap());
		assert_eq!(None, client.best_containing(a3.hash(), Some(1)).unwrap());
		assert_eq!(None, client.best_containing(a4.hash(), Some(1)).unwrap());
		assert_eq!(None, client.best_containing(a5.hash(), Some(1)).unwrap());

		assert_eq!(None, client.best_containing(b2.hash(), Some(1)).unwrap());
		assert_eq!(None, client.best_containing(b3.hash(), Some(1)).unwrap());
		assert_eq!(None, client.best_containing(b4.hash(), Some(1)).unwrap());

		assert_eq!(None, client.best_containing(c3.hash(), Some(1)).unwrap());

		assert_eq!(None, client.best_containing(d2.hash(), Some(1)).unwrap());

		// search only blocks with number <= 0

		assert_eq!(genesis_hash, client.best_containing(genesis_hash, Some(0)).unwrap().unwrap());
		assert_eq!(None, client.best_containing(a1.hash(), Some(0)).unwrap());
		assert_eq!(None, client.best_containing(a2.hash(), Some(0)).unwrap());
		assert_eq!(None, client.best_containing(a3.hash(), Some(0)).unwrap());
		assert_eq!(None, client.best_containing(a4.hash(), Some(0)).unwrap());
		assert_eq!(None, client.best_containing(a5.hash(), Some(0)).unwrap());

		assert_eq!(None, client.best_containing(b2.hash(), Some(0)).unwrap());
		assert_eq!(None, client.best_containing(b3.hash(), Some(0)).unwrap());
		assert_eq!(None, client.best_containing(b4.hash(), Some(0)).unwrap());

		assert_eq!(None, client.best_containing(c3.hash().clone(), Some(0)).unwrap());

		assert_eq!(None, client.best_containing(d2.hash().clone(), Some(0)).unwrap());
	}

	#[test]
	fn key_changes_works() {
		let (client, _, test_cases) = prepare_client_with_key_changes();

		for (index, (begin, end, key, expected_result)) in test_cases.into_iter().enumerate() {
			let begin = client.block_hash(begin).unwrap().unwrap();
			let end = client.block_hash(end).unwrap().unwrap();
			let actual_result = client.key_changes(begin, end, &key).unwrap();
			match actual_result == expected_result {
				true => (),
				false => panic!(format!("Failed test {}: actual = {:?}, expected = {:?}",
					index, actual_result, expected_result)),
			}
		}
	}
}
