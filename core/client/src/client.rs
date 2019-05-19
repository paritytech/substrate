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

//! Substrate Client

use std::{
	marker::PhantomData, collections::{HashSet, BTreeMap, HashMap}, sync::Arc,
	panic::UnwindSafe, result, cell::RefCell, rc::Rc,
};
use crate::error::Error;
use futures::sync::mpsc;
use parking_lot::{Mutex, RwLock};
use primitives::NativeOrEncoded;
use runtime_primitives::{
	Justification,
	generic::{BlockId, SignedBlock},
};
use consensus::{
	Error as ConsensusError, ErrorKind as ConsensusErrorKind, ImportBlock,
	ImportResult, BlockOrigin, ForkChoiceStrategy,
	well_known_cache_keys::Id as CacheKeyId,
	SelectChain, self,
};
use runtime_primitives::traits::{
	Block as BlockT, Header as HeaderT, Zero, As, NumberFor, CurrentHeight,
	BlockNumberToHash, ApiRef, ProvideRuntimeApi, Digest, DigestItem
};
use runtime_primitives::BuildStorage;
use crate::runtime_api::{
	CallRuntimeAt, ConstructRuntimeApi, Core as CoreApi, ProofRecorder,
	InitializeBlock,
};
use primitives::{
	Blake2Hasher, H256, ChangesTrieConfiguration, convert_hash,
	NeverNativeValue, ExecutionContext
};
use primitives::storage::{StorageKey, StorageData};
use primitives::storage::well_known_keys;
use parity_codec::{Encode, Decode};
use state_machine::{
	DBValue, Backend as StateBackend, CodeExecutor, ChangesTrieAnchorBlockId,
	ExecutionStrategy, ExecutionManager, prove_read, prove_child_read,
	ChangesTrieRootsStorage, ChangesTrieStorage,
	key_changes, key_changes_proof, OverlayedChanges, NeverOffchainExt,
};
use hash_db::Hasher;

use crate::backend::{self, BlockImportOperation, PrunableStateChangesTrieStorage};
use crate::blockchain::{
	self, Info as ChainInfo, Backend as ChainBackend,
	HeaderBackend as ChainHeaderBackend, ProvideCache, Cache,
};
use crate::call_executor::{CallExecutor, LocalCallExecutor};
use executor::{RuntimeVersion, RuntimeInfo};
use crate::notifications::{StorageNotifications, StorageEventStream};
use crate::light::{call_executor::prove_execution, fetcher::ChangesProof};
use crate::cht;
use crate::error;
use crate::in_mem;
use crate::block_builder::{self, api::BlockBuilder as BlockBuilderAPI};
use crate::genesis;
use substrate_telemetry::{telemetry, SUBSTRATE_INFO};

use log::{info, trace, warn};

/// Type that implements `futures::Stream` of block import events.
pub type ImportNotifications<Block> = mpsc::UnboundedReceiver<BlockImportNotification<Block>>;

/// A stream of block finality notifications.
pub type FinalityNotifications<Block> = mpsc::UnboundedReceiver<FinalityNotification<Block>>;

type StorageUpdate<B, Block> = <<<B as backend::Backend<Block, Blake2Hasher>>::BlockImportOperation as BlockImportOperation<Block, Blake2Hasher>>::State as state_machine::Backend<Blake2Hasher>>::Transaction;
type ChangesUpdate = trie::MemoryDB<Blake2Hasher>;

/// Execution strategies settings.
#[derive(Debug, Clone)]
pub struct ExecutionStrategies {
	/// Execution strategy used when syncing.
	pub syncing: ExecutionStrategy,
	/// Execution strategy used when importing blocks.
	pub importing: ExecutionStrategy,
	/// Execution strategy used when constructing blocks.
	pub block_construction: ExecutionStrategy,
	/// Execution strategy used for offchain workers.
	pub offchain_worker: ExecutionStrategy,
	/// Execution strategy used in other cases.
	pub other: ExecutionStrategy,
}

impl Default for ExecutionStrategies {
	fn default() -> ExecutionStrategies {
		ExecutionStrategies {
			syncing: ExecutionStrategy::NativeElseWasm,
			importing: ExecutionStrategy::NativeElseWasm,
			block_construction: ExecutionStrategy::AlwaysWasm,
			offchain_worker: ExecutionStrategy::NativeWhenPossible,
			other: ExecutionStrategy::NativeElseWasm,
		}
	}
}

/// Substrate Client
pub struct Client<B, E, Block, RA> where Block: BlockT {
	backend: Arc<B>,
	executor: E,
	storage_notifications: Mutex<StorageNotifications<Block>>,
	import_notification_sinks: Mutex<Vec<mpsc::UnboundedSender<BlockImportNotification<Block>>>>,
	finality_notification_sinks: Mutex<Vec<mpsc::UnboundedSender<FinalityNotification<Block>>>>,
	import_lock: Arc<Mutex<()>>,
	// holds the block hash currently being imported. TODO: replace this with block queue
	importing_block: RwLock<Option<Block::Hash>>,
	execution_strategies: ExecutionStrategies,
	_phantom: PhantomData<RA>,
}

/// Client import operation, a wrapper for the backend.
pub struct ClientImportOperation<Block: BlockT, H: Hasher<Out=Block::Hash>, B: backend::Backend<Block, H>> {
	op: B::BlockImportOperation,
	notify_imported: Option<(Block::Hash, BlockOrigin, Block::Header, bool, Option<Vec<(Vec<u8>, Option<Vec<u8>>)>>)>,
	notify_finalized: Vec<Block::Hash>,
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

/// Fetch block body by ID.
pub trait BlockBody<Block: BlockT> {
	/// Get block body by ID. Returns `None` if the body is not stored.
	fn block_body(&self, id: &BlockId<Block>) -> error::Result<Option<Vec<<Block as BlockT>::Extrinsic>>>;
}

/// Client info
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
	/// Already in the blockchain and the state is available.
	InChainWithState,
	/// In the blockchain, but the state is not available.
	InChainPruned,
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

/// Create a client with the explicitly provided backend.
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
	Client::new(backend, call_executor, build_genesis_storage, Default::default())
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
		execution_strategies: ExecutionStrategies
	) -> error::Result<Self> {
		if backend.blockchain().header(BlockId::Number(Zero::zero()))?.is_none() {
			let (genesis_storage, children_genesis_storage) = build_genesis_storage.build_storage()?;
			let mut op = backend.begin_operation()?;
			backend.begin_state_operation(&mut op, BlockId::Hash(Default::default()))?;
			let state_root = op.reset_storage(genesis_storage, children_genesis_storage)?;
			let genesis_block = genesis::construct_genesis_block::<Block>(state_root.into());
			info!("Initializing Genesis block/state (state: {}, header-hash: {})", genesis_block.header().state_root(), genesis_block.header().hash());
			op.set_block_data(
				genesis_block.deconstruct().0,
				Some(vec![]),
				None,
				crate::backend::NewBlockState::Final
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
			execution_strategies,
			_phantom: Default::default(),
		})
	}

	/// Get a reference to the execution strategies.
	pub fn execution_strategies(&self) -> &ExecutionStrategies {
		&self.execution_strategies
	}

	/// Get a reference to the state at a given block.
	pub fn state_at(&self, block: &BlockId<Block>) -> error::Result<B::State> {
		self.backend.state_at(*block)
	}

	/// Expose backend reference. To be used in tests only
	#[doc(hidden)]
	#[deprecated(note="Rather than relying on `client` to provide this, access \
	to the backend should be handled at setup only - see #1134. This function \
	will be removed once that is in place.")]
	pub fn backend(&self) -> &Arc<B> {
		&self.backend
	}

	/// Expose reference to import lock
	#[doc(hidden)]
	#[deprecated(note="Rather than relying on `client` to provide this, access \
	to the backend should be handled at setup only - see #1134. This function \
	will be removed once that is in place.")]
	pub fn import_lock(&self) -> Arc<Mutex<()>> {
		self.import_lock.clone()
	}

	/// Return storage entry keys in state in a block of given hash with given prefix.
	pub fn storage_keys(&self, id: &BlockId<Block>, key_prefix: &StorageKey) -> error::Result<Vec<StorageKey>> {
		let keys = self.state_at(id)?.keys(&key_prefix.0).into_iter().map(StorageKey).collect();
		Ok(keys)
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

	/// Get the RuntimeVersion at a given block.
	pub fn runtime_version_at(&self, id: &BlockId<Block>) -> error::Result<RuntimeVersion> {
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

	/// Reads child storage value at a given block + storage_key + key, returning
	/// read proof.
	pub fn read_child_proof(
		&self,
		id: &BlockId<Block>,
		storage_key: &[u8],
		key: &[u8]
	) -> error::Result<Vec<Vec<u8>>> {
		self.state_at(id)
			.and_then(|state| prove_child_read(state, storage_key, key)
				.map(|(_, proof)| proof)
				.map_err(Into::into))
	}

	/// Execute a call to a contract on top of state in a block of given hash
	/// AND returning execution proof.
	///
	/// No changes are made.
	pub fn execution_proof(&self, id: &BlockId<Block>, method: &str, call_data: &[u8]) -> error::Result<(Vec<u8>, Vec<Vec<u8>>)> {
		let state = self.state_at(id)?;
		let header = self.prepare_environment_block(id)?;
		prove_execution(state, header, &self.executor, method, call_data)
	}

	/// Reads given header and generates CHT-based header proof.
	pub fn header_proof(&self, id: &BlockId<Block>) -> error::Result<(Block::Header, Vec<Vec<u8>>)> {
		self.header_proof_with_cht_size(id, cht::SIZE)
	}

	/// Get block hash by number.
	pub fn block_hash(&self, block_number: <<Block as BlockT>::Header as HeaderT>::Number) -> error::Result<Option<Block::Hash>> {
		self.backend.blockchain().hash(block_number)
	}

	/// Reads given header and generates CHT-based header proof for CHT of given size.
	pub fn header_proof_with_cht_size(&self, id: &BlockId<Block>, cht_size: u64) -> error::Result<(Block::Header, Vec<Vec<u8>>)> {
		let proof_error = || error::Error::Backend(format!("Failed to generate header proof for {:?}", id));
		let header = self.backend.blockchain().expect_header(*id)?;
		let block_num = *header.number();
		let cht_num = cht::block_to_cht_number(cht_size, block_num).ok_or_else(proof_error)?;
		let cht_start = cht::start_number(cht_size, cht_num);
		let headers = (cht_start.as_()..).map(|num| self.block_hash(As::sa(num)));
		let proof = cht::build_proof::<Block::Header, Blake2Hasher, _, _>(cht_size, cht_num, ::std::iter::once(block_num), headers)?;
		Ok((header, proof))
	}

	/// Get longest range within [first; last] that is possible to use in `key_changes`
	/// and `key_changes_proof` calls.
	/// Range could be shortened from the beginning if some changes tries have been pruned.
	/// Returns Ok(None) if changes trues are not supported.
	pub fn max_key_changes_range(
		&self,
		first: NumberFor<Block>,
		last: BlockId<Block>,
	) -> error::Result<Option<(NumberFor<Block>, BlockId<Block>)>> {
		let (config, storage) = match self.require_changes_trie().ok() {
			Some((config, storage)) => (config, storage),
			None => return Ok(None),
		};
 		let first = first.as_();
		let last_num = self.backend.blockchain().expect_block_number_from_id(&last)?.as_();
		if first > last_num {
			return Err(error::Error::ChangesTrieAccessFailed("Invalid changes trie range".into()));
		}
 		let finalized_number = self.backend.blockchain().info()?.finalized_number;
		let oldest = storage.oldest_changes_trie_block(&config, finalized_number.as_());
		let first = As::sa(::std::cmp::max(first, oldest));
		Ok(Some((first, last)))
	}

	/// Get pairs of (block, extrinsic) where key has been changed at given blocks range.
	/// Works only for runtimes that are supporting changes tries.
	pub fn key_changes(
		&self,
		first: NumberFor<Block>,
		last: BlockId<Block>,
		key: &StorageKey
	) -> error::Result<Vec<(NumberFor<Block>, u32)>> {
		let (config, storage) = self.require_changes_trie()?;
		let last_number = self.backend.blockchain().expect_block_number_from_id(&last)?.as_();
		let last_hash = self.backend.blockchain().expect_block_hash_from_id(&last)?;

		key_changes::<_, Blake2Hasher>(
			&config,
			&*storage,
			first.as_(),
			&ChangesTrieAnchorBlockId {
				hash: convert_hash(&last_hash),
				number: last_number,
			},
			self.backend.blockchain().info()?.best_number.as_(),
			&key.0)
		.and_then(|r| r.map(|r| r.map(|(block, tx)| (As::sa(block), tx))).collect::<Result<_, _>>())
		.map_err(|err| error::Error::ChangesTrieAccessFailed(err))
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
		key: &StorageKey
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
		key: &StorageKey,
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
			fn get(&self, key: &H256, prefix: &[u8]) -> Result<Option<DBValue>, String> {
				self.storage.get(key, prefix)
			}
		}

		let (config, storage) = self.require_changes_trie()?;
		let min_number = self.backend.blockchain().expect_block_number_from_id(&BlockId::Hash(min))?;

		let recording_storage = AccessedRootsRecorder::<Block> {
			storage,
			min: min_number.as_(),
			required_roots_proofs: Mutex::new(BTreeMap::new()),
		};

		let max_number = ::std::cmp::min(
			self.backend.blockchain().info()?.best_number,
			self.backend.blockchain().expect_block_number_from_id(&BlockId::Hash(max))?,
		);

		// fetch key changes proof
		let first_number = self.backend.blockchain().expect_block_number_from_id(&BlockId::Hash(first))?.as_();
		let last_number = self.backend.blockchain().expect_block_number_from_id(&BlockId::Hash(last))?.as_();
		let key_changes_proof = key_changes_proof::<_, Blake2Hasher>(
			&config,
			&recording_storage,
			first_number,
			&ChangesTrieAnchorBlockId {
				hash: convert_hash(&last),
				number: last_number,
			},
			max_number.as_(),
			&key.0
		)
		.map_err(|err| error::Error::from(error::Error::ChangesTrieAccessFailed(err)))?;

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

	/// Returns changes trie configuration and storage or an error if it is not supported.
	fn require_changes_trie(&self) -> error::Result<(ChangesTrieConfiguration, &B::ChangesTrieStorage)> {
		let config = self.changes_trie_config()?;
		let storage = self.backend.changes_trie_storage();
		match (config, storage) {
			(Some(config), Some(storage)) => Ok((config, storage)),
			_ => Err(error::Error::ChangesTriesNotSupported.into()),
		}
	}

	/// Create a new block, built on the head of the chain.
	pub fn new_block(
		&self
	) -> error::Result<block_builder::BlockBuilder<Block, Self>> where
		E: Clone + Send + Sync,
		RA: Send + Sync,
		Self: ProvideRuntimeApi,
		<Self as ProvideRuntimeApi>::Api: BlockBuilderAPI<Block>
	{
		block_builder::BlockBuilder::new(self)
	}

	/// Create a new block, built on top of `parent`.
	pub fn new_block_at(
		&self, parent: &BlockId<Block>
	) -> error::Result<block_builder::BlockBuilder<Block, Self>> where
		E: Clone + Send + Sync,
		RA: Send + Sync,
		Self: ProvideRuntimeApi,
		<Self as ProvideRuntimeApi>::Api: BlockBuilderAPI<Block>
	{
		block_builder::BlockBuilder::at_block(parent, &self, false)
	}

	/// Create a new block, built on top of `parent` with proof recording enabled.
	///
	/// While proof recording is enabled, all accessed trie nodes are saved.
	/// These recorded trie nodes can be used by a third party to proof the
	/// output of this block builder without having access to the full storage.
	pub fn new_block_at_with_proof_recording(
		&self, parent: &BlockId<Block>
	) -> error::Result<block_builder::BlockBuilder<Block, Self>> where
		E: Clone + Send + Sync,
		RA: Send + Sync,
		Self: ProvideRuntimeApi,
		<Self as ProvideRuntimeApi>::Api: BlockBuilderAPI<Block>
	{
		block_builder::BlockBuilder::at_block(parent, &self, true)
	}

	/// Lock the import lock, and run operations inside.
	pub fn lock_import_and_run<R, Err, F>(&self, f: F) -> Result<R, Err> where
		F: FnOnce(&mut ClientImportOperation<Block, Blake2Hasher, B>) -> Result<R, Err>,
		Err: From<error::Error>,
	{
		let inner = || {
			let _import_lock = self.import_lock.lock();

			let mut op = ClientImportOperation {
				op: self.backend.begin_operation()?,
				notify_imported: None,
				notify_finalized: Vec::new(),
			};

			let r = f(&mut op)?;

			let ClientImportOperation { op, notify_imported, notify_finalized } = op;
			self.backend.commit_operation(op)?;
			self.notify_finalized(notify_finalized)?;

			if let Some(notify_imported) = notify_imported {
				self.notify_imported(notify_imported)?;
			}

			Ok(r)
		};

		let result = inner();
		*self.importing_block.write() = None;

		result
	}

	/// Set a block as best block.
	pub fn set_head(
		&self,
		id: BlockId<Block>
	) -> error::Result<()> {
		self.lock_import_and_run(|operation| {
			self.apply_head(operation, id)
		})
	}

	/// Set a block as best block, and apply it to an operation.
	pub fn apply_head(
		&self,
		operation: &mut ClientImportOperation<Block, Blake2Hasher, B>,
		id: BlockId<Block>,
	) -> error::Result<()> {
		operation.op.mark_head(id)
	}

	/// Apply a checked and validated block to an operation. If a justification is provided
	/// then `finalized` *must* be true.
	pub fn apply_block(
		&self,
		operation: &mut ClientImportOperation<Block, Blake2Hasher, B>,
		import_block: ImportBlock<Block>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> error::Result<ImportResult> where
		E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone,
	{
		let ImportBlock {
			origin,
			header,
			justification,
			post_digests,
			body,
			finalized,
			auxiliary,
			fork_choice,
		} = import_block;

		assert!(justification.is_some() && finalized || justification.is_none());

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
		let height: u64 = import_headers.post().number().as_();

		*self.importing_block.write() = Some(hash);

		let result = self.execute_and_import_block(
			operation,
			origin,
			hash,
			import_headers,
			justification,
			body,
			new_cache,
			finalized,
			auxiliary,
			fork_choice,
		);

		telemetry!(SUBSTRATE_INFO; "block.import";
			"height" => height,
			"best" => ?hash,
			"origin" => ?origin
		);

		result
	}

	fn execute_and_import_block(
		&self,
		operation: &mut ClientImportOperation<Block, Blake2Hasher, B>,
		origin: BlockOrigin,
		hash: Block::Hash,
		import_headers: PrePostHeader<Block::Header>,
		justification: Option<Justification>,
		body: Option<Vec<Block::Extrinsic>>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
		finalized: bool,
		aux: Vec<(Vec<u8>, Option<Vec<u8>>)>,
		fork_choice: ForkChoiceStrategy,
	) -> error::Result<ImportResult> where
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

		self.backend.begin_state_operation(&mut operation.op, BlockId::Hash(parent_hash))?;

		// ensure parent block is finalized to maintain invariant that
		// finality is called sequentially.
		if finalized {
			self.apply_finality_with_block_hash(operation, parent_hash, None, last_best, make_notifications)?;
		}

		// FIXME #1232: correct path logic for when to execute this function
		let (storage_update,changes_update,storage_changes) = self.block_execution(&operation.op, &import_headers, origin, hash, body.clone())?;

		let is_new_best = finalized || match fork_choice {
			ForkChoiceStrategy::LongestChain => import_headers.post().number() > &last_best_number,
			ForkChoiceStrategy::Custom(v) => v,
		};
		let leaf_state = if finalized {
			crate::backend::NewBlockState::Final
		} else if is_new_best {
			crate::backend::NewBlockState::Best
		} else {
			crate::backend::NewBlockState::Normal
		};

		trace!("Imported {}, (#{}), best={}, origin={:?}", hash, import_headers.post().number(), is_new_best, origin);

		operation.op.set_block_data(
			import_headers.post().clone(),
			body,
			justification,
			leaf_state,
		)?;

		operation.op.update_cache(new_cache);
		if let Some(storage_update) = storage_update {
			operation.op.update_db_storage(storage_update)?;
		}
		if let Some(storage_changes) = storage_changes.clone() {
			operation.op.update_storage(storage_changes)?;
		}
		if let Some(Some(changes_update)) = changes_update {
			operation.op.update_changes_trie(changes_update)?;
		}

		operation.op.insert_aux(aux)?;

		if make_notifications {
			if finalized {
				operation.notify_finalized.push(hash);
			}

			operation.notify_imported = Some((hash, origin, import_headers.into_post(), is_new_best, storage_changes));
		}

		Ok(ImportResult::imported())
	}

	fn block_execution(
		&self,
		transaction: &B::BlockImportOperation,
		import_headers: &PrePostHeader<Block::Header>,
		origin: BlockOrigin,
		hash: Block::Hash,
		body: Option<Vec<Block::Extrinsic>>,
	) -> error::Result<(
		Option<StorageUpdate<B, Block>>,
		Option<Option<ChangesUpdate>>,
		Option<Vec<(Vec<u8>, Option<Vec<u8>>)>>,
	)>
		where
			E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone,
	{
		match transaction.state()? {
			Some(transaction_state) => {
				let mut overlay = Default::default();
				let get_execution_manager = |execution_strategy: ExecutionStrategy| {
					match execution_strategy {
						ExecutionStrategy::NativeElseWasm => ExecutionManager::NativeElseWasm,
						ExecutionStrategy::AlwaysWasm => ExecutionManager::AlwaysWasm,
						ExecutionStrategy::NativeWhenPossible => ExecutionManager::NativeWhenPossible,
						ExecutionStrategy::Both => ExecutionManager::Both(|wasm_result, native_result| {
							let header = import_headers.post();
							warn!("Consensus error between wasm and native block execution at block {}", hash);
							warn!("   Header {:?}", header);
							warn!("   Native result {:?}", native_result);
							warn!("   Wasm result {:?}", wasm_result);
							telemetry!(SUBSTRATE_INFO; "block.execute.consensus_failure";
								"hash" => ?hash,
								"origin" => ?origin,
								"header" => ?header
							);
							wasm_result
						}),
					}
				};
				let (_, storage_update, changes_update) = self.executor.call_at_state::<_, _, _, NeverNativeValue, fn() -> _>(
					transaction_state,
					&mut overlay,
					"Core_execute_block",
					&<Block as BlockT>::new(import_headers.pre().clone(), body.unwrap_or_default()).encode(),
					match origin {
						BlockOrigin::NetworkInitialSync => get_execution_manager(self.execution_strategies().syncing),
						_ => get_execution_manager(self.execution_strategies().importing),
					},
					None,
					NeverOffchainExt::new(),
				)?;

				overlay.commit_prospective();

				Ok((Some(storage_update), Some(changes_update), Some(overlay.into_committed().collect())))
			},
			None => Ok((None, None, None))
		}
	}

	fn apply_finality_with_block_hash(
		&self,
		operation: &mut ClientImportOperation<Block, Blake2Hasher, B>,
		block: Block::Hash,
		justification: Option<Justification>,
		best_block: Block::Hash,
		notify: bool,
	) -> error::Result<()> {
		// find tree route from last finalized to given block.
		let last_finalized = self.backend.blockchain().last_finalized()?;

		if block == last_finalized {
			warn!("Possible safety violation: attempted to re-finalize last finalized block {:?} ", last_finalized);
			return Ok(());
		}

		let route_from_finalized = crate::blockchain::tree_route(
			self.backend.blockchain(),
			BlockId::Hash(last_finalized),
			BlockId::Hash(block),
		)?;

		if let Some(retracted) = route_from_finalized.retracted().get(0) {
			warn!("Safety violation: attempted to revert finalized block {:?} which is not in the \
				same chain as last finalized {:?}", retracted, last_finalized);

			return Err(error::Error::NotInFinalizedChain);
		}

		let route_from_best = crate::blockchain::tree_route(
			self.backend.blockchain(),
			BlockId::Hash(best_block),
			BlockId::Hash(block),
		)?;

		// if the block is not a direct ancestor of the current best chain,
		// then some other block is the common ancestor.
		if route_from_best.common_block().hash != block {
			// FIXME: #1442 reorganize best block to be the best chain containing
			// `block`.
		}

		let enacted = route_from_finalized.enacted();
		assert!(enacted.len() > 0);
		for finalize_new in &enacted[..enacted.len() - 1] {
			operation.op.mark_finalized(BlockId::Hash(finalize_new.hash), None)?;
		}

		assert_eq!(enacted.last().map(|e| e.hash), Some(block));
		operation.op.mark_finalized(BlockId::Hash(block), justification)?;

		if notify {
			// sometimes when syncing, tons of blocks can be finalized at once.
			// we'll send notifications spuriously in that case.
			const MAX_TO_NOTIFY: usize = 256;
			let enacted = route_from_finalized.enacted();
			let start = enacted.len() - ::std::cmp::min(enacted.len(), MAX_TO_NOTIFY);
			for finalized in &enacted[start..] {
				operation.notify_finalized.push(finalized.hash);
			}
		}

		Ok(())
	}

	fn notify_finalized(
		&self,
		notify_finalized: Vec<Block::Hash>,
	) -> error::Result<()> {
		let mut sinks = self.finality_notification_sinks.lock();

		for finalized_hash in notify_finalized {
			let header = self.header(&BlockId::Hash(finalized_hash))?
				.expect("header already known to exist in DB because it is indicated in the tree route; qed");

			telemetry!(SUBSTRATE_INFO; "notify.finalized";
				"height" => format!("{}", header.number()),
				"best" => ?finalized_hash,
			);

			let notification = FinalityNotification {
				header,
				hash: finalized_hash,
			};

			sinks.retain(|sink| sink.unbounded_send(notification.clone()).is_ok());
		}

		Ok(())
	}

	fn notify_imported(
		&self,
		notify_import: (Block::Hash, BlockOrigin, Block::Header, bool, Option<Vec<(Vec<u8>, Option<Vec<u8>>)>>),
	) -> error::Result<()> {
		let (hash, origin, header, is_new_best, storage_changes) = notify_import;

		if let Some(storage_changes) = storage_changes {
			// TODO [ToDr] How to handle re-orgs? Should we re-emit all storage changes?
			self.storage_notifications.lock()
				.trigger(&hash, storage_changes.into_iter());
		}

		let notification = BlockImportNotification::<Block> {
			hash,
			origin,
			header,
			is_new_best,
		};

		self.import_notification_sinks.lock()
			.retain(|sink| sink.unbounded_send(notification.clone()).is_ok());

		Ok(())
	}

	/// Apply auxiliary data insertion into an operation.
	pub fn apply_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
		D: IntoIterator<Item=&'a &'b [u8]>,
	>(
		&self,
		operation: &mut ClientImportOperation<Block, Blake2Hasher, B>,
		insert: I,
		delete: D
	) -> error::Result<()> {
		operation.op.insert_aux(
			insert.into_iter()
				.map(|(k, v)| (k.to_vec(), Some(v.to_vec())))
				.chain(delete.into_iter().map(|k| (k.to_vec(), None)))
		)
	}

	/// Mark all blocks up to given as finalized in operation. If a
	/// justification is provided it is stored with the given finalized
	/// block (any other finalized blocks are left unjustified).
	pub fn apply_finality(
		&self,
		operation: &mut ClientImportOperation<Block, Blake2Hasher, B>,
		id: BlockId<Block>,
		justification: Option<Justification>,
		notify: bool,
	) -> error::Result<()> {
		let last_best = self.backend.blockchain().info()?.best_hash;
		let to_finalize_hash = self.backend.blockchain().expect_block_hash_from_id(&id)?;
		self.apply_finality_with_block_hash(operation, to_finalize_hash, justification, last_best, notify)
	}

	/// Finalize a block. This will implicitly finalize all blocks up to it and
	/// fire finality notifications.
	///
	/// Pass a flag to indicate whether finality notifications should be propagated.
	/// This is usually tied to some synchronization state, where we don't send notifications
	/// while performing major synchronization work.
	pub fn finalize_block(&self, id: BlockId<Block>, justification: Option<Justification>, notify: bool) -> error::Result<()> {
		self.lock_import_and_run(|operation| {
			let last_best = self.backend.blockchain().info()?.best_hash;
			let to_finalize_hash = self.backend.blockchain().expect_block_hash_from_id(&id)?;
			self.apply_finality_with_block_hash(operation, to_finalize_hash, justification, last_best, notify)
		})
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
		// this can probably be implemented more efficiently
		if let BlockId::Hash(ref h) = id {
			if self.importing_block.read().as_ref().map_or(false, |importing| h == importing) {
				return Ok(BlockStatus::Queued);
			}
		}
		let hash_and_number = match id.clone() {
			BlockId::Hash(hash) => self.backend.blockchain().number(hash)?.map(|n| (hash, n)),
			BlockId::Number(n) => self.backend.blockchain().hash(n)?.map(|hash| (hash, n)),
		};
		match hash_and_number {
			Some((hash, number)) => {
				if self.backend.have_state_at(&hash, number) {
					Ok(BlockStatus::InChainWithState)
				} else {
					Ok(BlockStatus::InChainPruned)
				}
			}
			None => Ok(BlockStatus::Unknown),
		}
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
			(Some(header), Some(extrinsics), justification) =>
				Some(SignedBlock { block: Block::new(header, extrinsics), justification }),
			_ => None,
		})
	}

	/// Gets the uncles of the block with `target_hash` going back `max_generation` ancestors.
	pub fn uncles(&self, target_hash: Block::Hash, max_generation: NumberFor<Block>) -> error::Result<Vec<Block::Hash>> {
		let load_header = |id: Block::Hash| -> error::Result<Block::Header> {
			match self.backend.blockchain().header(BlockId::Hash(id))? {
				Some(hdr) => Ok(hdr),
				None => Err(Error::UnknownBlock(format!("Unknown block {:?}", id))),
			}
		};

		let genesis_hash = self.backend.blockchain().info()?.genesis_hash;
		if genesis_hash == target_hash { return Ok(Vec::new()); }

		let mut current_hash = target_hash;
		let mut current = load_header(current_hash)?;
		let mut ancestor_hash = *current.parent_hash();
		let mut ancestor = load_header(ancestor_hash)?;
		let mut uncles = Vec::new();

		for _generation in 0..max_generation.as_() {
			let children = self.backend.blockchain().children(ancestor_hash)?;
			uncles.extend(children.into_iter().filter(|h| h != &current_hash));
			current_hash = ancestor_hash;
			if genesis_hash == current_hash { break; }
			current = ancestor;
			ancestor_hash = *current.parent_hash();
			ancestor = load_header(ancestor_hash)?;
		}

		Ok(uncles)
	}

	fn changes_trie_config(&self) -> Result<Option<ChangesTrieConfiguration>, Error> {
		Ok(self.backend.state_at(BlockId::Number(self.backend.blockchain().info()?.best_number))?
			.storage(well_known_keys::CHANGES_TRIE_CONFIG)
			.map_err(|e| error::Error::from_state(Box::new(e)))?
			.and_then(|c| Decode::decode(&mut &*c)))
	}

	/// Prepare in-memory header that is used in execution environment.
	fn prepare_environment_block(&self, parent: &BlockId<Block>) -> error::Result<Block::Header> {
		Ok(<<Block as BlockT>::Header as HeaderT>::new(
			self.backend.blockchain().expect_block_number_from_id(parent)? + As::sa(1),
			Default::default(),
			Default::default(),
			self.backend.blockchain().expect_block_hash_from_id(&parent)?,
			Default::default(),
		))
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

impl<B, E, Block, RA> ProvideCache<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	Block: BlockT<Hash=H256>,
{
	fn cache(&self) -> Option<Arc<Cache<Block>>> {
		self.backend.blockchain().cache()
	}
}

impl<B, E, Block, RA> ProvideRuntimeApi for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Clone + Send + Sync,
	Block: BlockT<Hash=H256>,
	RA: ConstructRuntimeApi<Block, Self>
{
	type Api = <RA as ConstructRuntimeApi<Block, Self>>::RuntimeApi;

	fn runtime_api<'a>(&'a self) -> ApiRef<'a, Self::Api> {
		RA::construct_runtime_api(self)
	}
}

impl<B, E, Block, RA> CallRuntimeAt<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Clone + Send + Sync,
	Block: BlockT<Hash=H256>,
{
	fn call_api_at<
		'a,
		R: Encode + Decode + PartialEq,
		NC: FnOnce() -> result::Result<R, &'static str> + UnwindSafe,
		C: CoreApi<Block>,
	>(
		&self,
		core_api: &C,
		at: &BlockId<Block>,
		function: &'static str,
		args: Vec<u8>,
		changes: &RefCell<OverlayedChanges>,
		initialize_block: InitializeBlock<'a, Block>,
		native_call: Option<NC>,
		context: ExecutionContext,
		recorder: &Option<Rc<RefCell<ProofRecorder<Block>>>>,
	) -> error::Result<NativeOrEncoded<R>> {
		let manager = match context {
			ExecutionContext::BlockConstruction =>
				self.execution_strategies.block_construction.get_manager(),
			ExecutionContext::Syncing =>
				self.execution_strategies.syncing.get_manager(),
			ExecutionContext::Importing =>
				self.execution_strategies.importing.get_manager(),
			ExecutionContext::OffchainWorker(_) =>
				self.execution_strategies.offchain_worker.get_manager(),
			ExecutionContext::Other =>
				self.execution_strategies.other.get_manager(),
		};

		let mut offchain_extensions = match context {
			ExecutionContext::OffchainWorker(ext) => Some(ext),
			_ => None,
		};

		self.executor.contextual_call::<_, _, fn(_,_) -> _,_,_>(
			|| core_api.initialize_block(at, &self.prepare_environment_block(at)?),
			at,
			function,
			&args,
			changes,
			initialize_block,
			manager,
			native_call,
			offchain_extensions.as_mut(),
			recorder,
		)
	}

	fn runtime_version_at(&self, at: &BlockId<Block>) -> error::Result<RuntimeVersion> {
		self.runtime_version_at(at)
	}
}

impl<B, E, Block, RA> consensus::BlockImport<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Clone + Send + Sync,
	Block: BlockT<Hash=H256>,
{
	type Error = ConsensusError;

	/// Import a checked and validated block. If a justification is provided in
	/// `ImportBlock` then `finalized` *must* be true.
	fn import_block(
		&self,
		import_block: ImportBlock<Block>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		self.lock_import_and_run(|operation| {
			self.apply_block(operation, import_block, new_cache)
		}).map_err(|e| ConsensusErrorKind::ClientImport(e.to_string()).into())
	}

	/// Check block preconditions.
	fn check_block(
		&self,
		hash: Block::Hash,
		parent_hash: Block::Hash,
	) -> Result<ImportResult, Self::Error> {
		match self.block_status(&BlockId::Hash(parent_hash))
			.map_err(|e| ConsensusError::from(ConsensusErrorKind::ClientImport(e.to_string())))?
		{
			BlockStatus::InChainWithState | BlockStatus::Queued => {},
			BlockStatus::Unknown | BlockStatus::InChainPruned => return Ok(ImportResult::UnknownParent),
			BlockStatus::KnownBad => return Ok(ImportResult::KnownBad),
		}

		match self.block_status(&BlockId::Hash(hash))
			.map_err(|e| ConsensusError::from(ConsensusErrorKind::ClientImport(e.to_string())))?
		{
			BlockStatus::InChainWithState | BlockStatus::Queued => return Ok(ImportResult::AlreadyInChain),
			BlockStatus::Unknown | BlockStatus::InChainPruned => {},
			BlockStatus::KnownBad => return Ok(ImportResult::KnownBad),
		}

		Ok(ImportResult::imported())
	}
}

impl<B, E, Block, RA> CurrentHeight for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
	Block: BlockT<Hash=H256>,
{
	type BlockNumber = <Block::Header as HeaderT>::Number;
	fn current_height(&self) -> Self::BlockNumber {
		self.backend.blockchain().info().map(|i| i.best_number).unwrap_or_else(|_| Zero::zero())
	}
}

impl<B, E, Block, RA> BlockNumberToHash for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
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

/// Implement Longest Chain Select implementation
/// where 'longest' is defined as the highest number of blocks
pub struct LongestChain<B, Block> {
	backend: Arc<B>,
	import_lock: Arc<Mutex<()>>,
	_phantom: PhantomData<Block>
}

impl<B, Block> Clone for LongestChain<B, Block> {
	fn clone(&self) -> Self {
		let backend = self.backend.clone();
		let import_lock = self.import_lock.clone();
		LongestChain {
			backend,
			import_lock,
			_phantom: Default::default()
		}
	}
}

impl<B, Block> LongestChain<B, Block>
where
	B: backend::Backend<Block, Blake2Hasher>,
	Block: BlockT<Hash=H256>,
{
	/// Instantiate a new LongestChain for Backend B
	pub fn new(backend: Arc<B>, import_lock: Arc<Mutex<()>>) -> Self {
		LongestChain {
			backend,
			import_lock,
			_phantom: Default::default()
		}
	}

	fn best_block_header(&self) -> error::Result<<Block as BlockT>::Header> {
		let info : ChainInfo<Block> = match self.backend.blockchain().info() {
			Ok(i) => i,
			Err(e) => return Err(error::Error::from_blockchain(Box::new(e)))
		};
		Ok(self.backend.blockchain().header(BlockId::Hash(info.best_hash))?
			.expect("Best block header must always exist"))
	}

	/// Get the most recent block hash of the best (longest) chains
	/// that contain block with the given `target_hash`.
	///
	/// The search space is always limited to blocks which are in the finalized
	/// chain or descendents of it.
	///
	/// If `maybe_max_block_number` is `Some(max_block_number)`
	/// the search is limited to block `numbers <= max_block_number`.
	/// in other words as if there were no blocks greater `max_block_number`.
	/// Returns `Ok(None)` if `target_hash` is not found in search space.
	/// TODO: document time complexity of this, see [#1444](https://github.com/paritytech/substrate/issues/1444)
	fn best_containing(
		&self,
		target_hash: Block::Hash,
		maybe_max_number: Option<NumberFor<Block>>
	) -> error::Result<Option<Block::Hash>> {
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
				// if no block at the given max depth exists fallback to the best block
				if let Some(max_number) = maybe_max_number {
					if let Some(header) = self.backend.blockchain().hash(max_number)? {
						return Ok(Some(header));
					}
				}

				return Ok(Some(info.best_hash));
			} else if info.finalized_number >= *target_header.number() {
				// header is on a dead fork.
				return Ok(None);
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

				let current_header = self.backend.blockchain().header(BlockId::Hash(current_hash.clone()))?
					.ok_or_else(|| error::Error::from(format!("failed to get header for hash {}", current_hash)))?;

				// stop search in this chain once we go below the target's block number
				if current_header.number() < target_header.number() {
					break;
				}

				current_hash = *current_header.parent_hash();
			}
		}

		// header may be on a dead fork -- the only leaves that are considered are
		// those which can still be finalized.
		//
		// FIXME #1558 only issue this warning when not on a dead fork
		warn!(
			"Block {:?} exists in chain but not found when following all \
			leaves backwards. Number limit = {:?}",
			target_hash,
			maybe_max_number,
		);

		Ok(None)
	}

	fn leaves(&self) -> Result<Vec<<Block as BlockT>::Hash>, error::Error> {
		self.backend.blockchain().leaves()
	}
}

impl<B, Block> SelectChain<Block> for LongestChain<B, Block>
where
	B: backend::Backend<Block, Blake2Hasher>,
	Block: BlockT<Hash=H256>,
{

	fn leaves(&self) -> Result<Vec<<Block as BlockT>::Hash>, ConsensusError> {
		LongestChain::leaves(self)
			.map_err(|e| ConsensusErrorKind::ChainLookup(e.to_string()).into())
	}

	fn best_chain(&self)
		-> Result<<Block as BlockT>::Header, ConsensusError>
	{
		LongestChain::best_block_header(&self)
			.map_err(|e| ConsensusErrorKind::ChainLookup(e.to_string()).into())
	}

	fn finality_target(
		&self,
		target_hash: Block::Hash,
		maybe_max_number: Option<NumberFor<Block>>
	) -> Result<Option<Block::Hash>, ConsensusError> {
		LongestChain::best_containing(self, target_hash, maybe_max_number)
			.map_err(|e| ConsensusErrorKind::ChainLookup(e.to_string()).into())
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

impl<B, E, Block, RA> backend::AuxStore for Client<B, E, Block, RA>
	where
		B: backend::Backend<Block, Blake2Hasher>,
		E: CallExecutor<Block, Blake2Hasher>,
		Block: BlockT<Hash=H256>,
{
	/// Insert auxiliary data into key-value store.
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
		D: IntoIterator<Item=&'a &'b [u8]>,
	>(&self, insert: I, delete: D) -> error::Result<()> {
		// Import is locked here because we may have other block import
		// operations that tries to set aux data. Note that for consensus
		// layer, one can always use atomic operations to make sure
		// import is only locked once.
		self.lock_import_and_run(|operation| {
			self.apply_aux(operation, insert, delete)
		})
	}
	/// Query auxiliary data from key-value store.
	fn get_aux(&self, key: &[u8]) -> error::Result<Option<Vec<u8>>> {
		crate::backend::AuxStore::get_aux(&*self.backend, key)
	}
}
#[cfg(test)]
pub(crate) mod tests {
	use std::collections::HashMap;
	use super::*;
	use primitives::blake2_256;
	use runtime_primitives::traits::DigestItem as DigestItemT;
	use runtime_primitives::generic::DigestItem;
	use test_client::{self, TestClient, AccountKeyring};
	use consensus::{BlockOrigin, SelectChain};
	use test_client::client::backend::Backend as TestBackend;
	use test_client::BlockBuilderExt;
	use test_client::runtime::{self, Block, Transfer, RuntimeApi, TestAPI};

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
			vec![(AccountKeyring::Alice, AccountKeyring::Dave), (AccountKeyring::Bob, AccountKeyring::Dave)],
			vec![(AccountKeyring::Charlie, AccountKeyring::Eve)],
			vec![],
			vec![(AccountKeyring::Alice, AccountKeyring::Dave)],
		];

		// prepare client ang import blocks
		let mut local_roots = Vec::new();
		let remote_client = test_client::new_with_changes_trie();
		let mut nonces: HashMap<_, u64> = Default::default();
		for (i, block_transfers) in blocks_transfers.into_iter().enumerate() {
			let mut builder = remote_client.new_block().unwrap();
			for (from, to) in block_transfers {
				builder.push_transfer(Transfer {
					from: from.into(),
					to: to.into(),
					amount: 1,
					nonce: *nonces.entry(from).and_modify(|n| { *n = *n + 1 }).or_default(),
				}).unwrap();
			}
			remote_client.import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();

			let header = remote_client.header(&BlockId::Number(i as u64 + 1)).unwrap().unwrap();
			let trie_root = header.digest().log(DigestItem::as_changes_trie_root)
				.map(|root| H256::from_slice(root.as_ref()))
				.unwrap();
			local_roots.push(trie_root);
		}

		// prepare test cases
		let alice = blake2_256(&runtime::system::balance_of_key(AccountKeyring::Alice.into())).to_vec();
		let bob = blake2_256(&runtime::system::balance_of_key(AccountKeyring::Bob.into())).to_vec();
		let charlie = blake2_256(&runtime::system::balance_of_key(AccountKeyring::Charlie.into())).to_vec();
		let dave = blake2_256(&runtime::system::balance_of_key(AccountKeyring::Dave.into())).to_vec();
		let eve = blake2_256(&runtime::system::balance_of_key(AccountKeyring::Eve.into())).to_vec();
		let ferdie = blake2_256(&runtime::system::balance_of_key(AccountKeyring::Ferdie.into())).to_vec();
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
	fn client_initializes_from_genesis_ok() {
		let client = test_client::new();

		assert_eq!(
			client.runtime_api().balance_of(
				&BlockId::Number(client.info().unwrap().chain.best_number),
				AccountKeyring::Alice.into()
			).unwrap(),
			1000
		);
		assert_eq!(
			client.runtime_api().balance_of(
				&BlockId::Number(client.info().unwrap().chain.best_number),
				AccountKeyring::Ferdie.into()
			).unwrap(),
			0
		);
	}

	#[test]
	fn block_builder_works_with_no_transactions() {
		let client = test_client::new();

		let builder = client.new_block().unwrap();

		client.import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();

		assert_eq!(client.info().unwrap().chain.best_number, 1);
	}

	#[test]
	fn block_builder_works_with_transactions() {
		let client = test_client::new();

		let mut builder = client.new_block().unwrap();

		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 42,
			nonce: 0,
		}).unwrap();

		client.import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();

		assert_eq!(client.info().unwrap().chain.best_number, 1);
		assert!(client.state_at(&BlockId::Number(1)).unwrap().pairs() != client.state_at(&BlockId::Number(0)).unwrap().pairs());
		assert_eq!(
			client.runtime_api().balance_of(
				&BlockId::Number(client.info().unwrap().chain.best_number),
				AccountKeyring::Alice.into()
			).unwrap(),
			958
		);
		assert_eq!(
			client.runtime_api().balance_of(
				&BlockId::Number(client.info().unwrap().chain.best_number),
				AccountKeyring::Ferdie.into()
			).unwrap(),
			42
		);
	}

	#[test]
	fn block_builder_does_not_include_invalid() {
		let client = test_client::new();

		let mut builder = client.new_block().unwrap();

		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 42,
			nonce: 0,
		}).unwrap();

		assert!(builder.push_transfer(Transfer {
			from: AccountKeyring::Eve.into(),
			to: AccountKeyring::Alice.into(),
			amount: 42,
			nonce: 0,
		}).is_err());

		client.import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();

		assert_eq!(client.info().unwrap().chain.best_number, 1);
		assert!(client.state_at(&BlockId::Number(1)).unwrap().pairs() != client.state_at(&BlockId::Number(0)).unwrap().pairs());
		assert_eq!(client.body(&BlockId::Number(1)).unwrap().unwrap().len(), 1)
	}

	#[test]
	fn best_containing_with_genesis_block() {
		// block tree:
		// G

		let client = test_client::new();

		let genesis_hash = client.info().unwrap().chain.genesis_hash;
		let longest_chain_select = test_client::client::LongestChain::new(
			client.backend().clone(),
			client.import_lock()
		);


		assert_eq!(genesis_hash.clone(), longest_chain_select.finality_target(
			genesis_hash.clone(), None).unwrap().unwrap());
	}

	#[test]
	fn best_containing_with_hash_not_found() {
		// block tree:
		// G

		let client = test_client::new();

		let uninserted_block = client.new_block().unwrap().bake().unwrap();
		let backend = client.backend().as_in_memory();
		let longest_chain_select = test_client::client::LongestChain::new(
				Arc::new(backend),
				client.import_lock());

		assert_eq!(None, longest_chain_select.finality_target(
			uninserted_block.hash().clone(), None).unwrap());
	}

	#[test]
	fn uncles_with_only_ancestors() {
		// block tree:
		// G -> A1 -> A2
		let client = test_client::new();

		// G -> A1
		let a1 = client.new_block().unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block().unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a2.clone()).unwrap();
		let v: Vec<H256> = Vec::new();
		assert_eq!(v, client.uncles(a2.hash(), 3).unwrap());
	}

	#[test]
	fn uncles_with_multiple_forks() {
		// block tree:
		// G -> A1 -> A2 -> A3 -> A4 -> A5
		//      A1 -> B2 -> B3 -> B4
		//	          B2 -> C3
		//	    A1 -> D2
		let client = test_client::new();

		// G -> A1
		let a1 = client.new_block().unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block_at(&BlockId::Hash(a1.hash())).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		// A2 -> A3
		let a3 = client.new_block_at(&BlockId::Hash(a2.hash())).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a3.clone()).unwrap();

		// A3 -> A4
		let a4 = client.new_block_at(&BlockId::Hash(a3.hash())).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a4.clone()).unwrap();

		// A4 -> A5
		let a5 = client.new_block_at(&BlockId::Hash(a4.hash())).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a5.clone()).unwrap();

		// A1 -> B2
		let mut builder = client.new_block_at(&BlockId::Hash(a1.hash())).unwrap();
		// this push is required as otherwise B2 has the same hash as A2 and won't get imported
		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 41,
			nonce: 0,
		}).unwrap();
		let b2 = builder.bake().unwrap();
		client.import(BlockOrigin::Own, b2.clone()).unwrap();

		// B2 -> B3
		let b3 = client.new_block_at(&BlockId::Hash(b2.hash())).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, b3.clone()).unwrap();

		// B3 -> B4
		let b4 = client.new_block_at(&BlockId::Hash(b3.hash())).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, b4.clone()).unwrap();

		// // B2 -> C3
		let mut builder = client.new_block_at(&BlockId::Hash(b2.hash())).unwrap();
		// this push is required as otherwise C3 has the same hash as B3 and won't get imported
		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 1,
		}).unwrap();
		let c3 = builder.bake().unwrap();
		client.import(BlockOrigin::Own, c3.clone()).unwrap();

		// A1 -> D2
		let mut builder = client.new_block_at(&BlockId::Hash(a1.hash())).unwrap();
		// this push is required as otherwise D2 has the same hash as B2 and won't get imported
		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 0,
		}).unwrap();
		let d2 = builder.bake().unwrap();
		client.import(BlockOrigin::Own, d2.clone()).unwrap();

		let genesis_hash = client.info().unwrap().chain.genesis_hash;

		let uncles1 = client.uncles(a4.hash(), 10).unwrap();
		assert_eq!(vec![b2.hash(), d2.hash()], uncles1);

		let uncles2 = client.uncles(a4.hash(), 0).unwrap();
		assert_eq!(0, uncles2.len());

		let uncles3 = client.uncles(a1.hash(), 10).unwrap();
		assert_eq!(0, uncles3.len());

		let uncles4 = client.uncles(genesis_hash, 10).unwrap();
		assert_eq!(0, uncles4.len());

		let uncles5 = client.uncles(d2.hash(), 10).unwrap();
		assert_eq!(vec![a2.hash(), b2.hash()], uncles5);

		let uncles6 = client.uncles(b3.hash(), 1).unwrap();
		assert_eq!(vec![c3.hash()], uncles6);
	}

	#[test]
	fn best_containing_on_longest_chain_with_single_chain_3_blocks() {
		// block tree:
		// G -> A1 -> A2

		let client = test_client::new();

		// G -> A1
		let a1 = client.new_block().unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block().unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		let genesis_hash = client.info().unwrap().chain.genesis_hash;

		let longest_chain_select = test_client::client::LongestChain::new(
				Arc::new(client.backend().as_in_memory()),
				client.import_lock());

		assert_eq!(a2.hash(), longest_chain_select.finality_target(
			genesis_hash, None).unwrap().unwrap());
		assert_eq!(a2.hash(), longest_chain_select.finality_target(
			a1.hash(), None).unwrap().unwrap());
		assert_eq!(a2.hash(), longest_chain_select.finality_target(
			a2.hash(), None).unwrap().unwrap());
	}

	#[test]
	fn best_containing_on_longest_chain_with_multiple_forks() {
		// block tree:
		// G -> A1 -> A2 -> A3 -> A4 -> A5
		//      A1 -> B2 -> B3 -> B4
		//	          B2 -> C3
		//	    A1 -> D2
		let client = test_client::new();

		// G -> A1
		let a1 = client.new_block().unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block_at(&BlockId::Hash(a1.hash())).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		// A2 -> A3
		let a3 = client.new_block_at(&BlockId::Hash(a2.hash())).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a3.clone()).unwrap();

		// A3 -> A4
		let a4 = client.new_block_at(&BlockId::Hash(a3.hash())).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a4.clone()).unwrap();

		// A4 -> A5
		let a5 = client.new_block_at(&BlockId::Hash(a4.hash())).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a5.clone()).unwrap();

		// A1 -> B2
		let mut builder = client.new_block_at(&BlockId::Hash(a1.hash())).unwrap();
		// this push is required as otherwise B2 has the same hash as A2 and won't get imported
		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 41,
			nonce: 0,
		}).unwrap();
		let b2 = builder.bake().unwrap();
		client.import(BlockOrigin::Own, b2.clone()).unwrap();

		// B2 -> B3
		let b3 = client.new_block_at(&BlockId::Hash(b2.hash())).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, b3.clone()).unwrap();

		// B3 -> B4
		let b4 = client.new_block_at(&BlockId::Hash(b3.hash())).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, b4.clone()).unwrap();

		// // B2 -> C3
		let mut builder = client.new_block_at(&BlockId::Hash(b2.hash())).unwrap();
		// this push is required as otherwise C3 has the same hash as B3 and won't get imported
		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 1,
		}).unwrap();
		let c3 = builder.bake().unwrap();
		client.import(BlockOrigin::Own, c3.clone()).unwrap();

		// A1 -> D2
		let mut builder = client.new_block_at(&BlockId::Hash(a1.hash())).unwrap();
		// this push is required as otherwise D2 has the same hash as B2 and won't get imported
		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 0,
		}).unwrap();
		let d2 = builder.bake().unwrap();
		client.import(BlockOrigin::Own, d2.clone()).unwrap();

		assert_eq!(client.info().unwrap().chain.best_hash, a5.hash());

		let genesis_hash = client.info().unwrap().chain.genesis_hash;
		let longest_chain_select = test_client::client::LongestChain::new(
				Arc::new(client.backend().as_in_memory()),
				client.import_lock());

		let leaves = longest_chain_select.leaves().unwrap();

		assert!(leaves.contains(&a5.hash()));
		assert!(leaves.contains(&b4.hash()));
		assert!(leaves.contains(&c3.hash()));
		assert!(leaves.contains(&d2.hash()));
		assert_eq!(leaves.len(), 4);

		// search without restriction

		assert_eq!(a5.hash(), longest_chain_select.finality_target(
			genesis_hash, None).unwrap().unwrap());
		assert_eq!(a5.hash(), longest_chain_select.finality_target(
			a1.hash(), None).unwrap().unwrap());
		assert_eq!(a5.hash(), longest_chain_select.finality_target(
			a2.hash(), None).unwrap().unwrap());
		assert_eq!(a5.hash(), longest_chain_select.finality_target(
			a3.hash(), None).unwrap().unwrap());
		assert_eq!(a5.hash(), longest_chain_select.finality_target(
			a4.hash(), None).unwrap().unwrap());
		assert_eq!(a5.hash(), longest_chain_select.finality_target(
			a5.hash(), None).unwrap().unwrap());

		assert_eq!(b4.hash(), longest_chain_select.finality_target(
			b2.hash(), None).unwrap().unwrap());
		assert_eq!(b4.hash(), longest_chain_select.finality_target(
			b3.hash(), None).unwrap().unwrap());
		assert_eq!(b4.hash(), longest_chain_select.finality_target(
			b4.hash(), None).unwrap().unwrap());

		assert_eq!(c3.hash(), longest_chain_select.finality_target(
			c3.hash(), None).unwrap().unwrap());

		assert_eq!(d2.hash(), longest_chain_select.finality_target(
			d2.hash(), None).unwrap().unwrap());


		// search only blocks with number <= 5. equivalent to without restriction for this scenario

		assert_eq!(a5.hash(), longest_chain_select.finality_target(
			genesis_hash, Some(5)).unwrap().unwrap());
		assert_eq!(a5.hash(), longest_chain_select.finality_target(
			a1.hash(), Some(5)).unwrap().unwrap());
		assert_eq!(a5.hash(), longest_chain_select.finality_target(
			a2.hash(), Some(5)).unwrap().unwrap());
		assert_eq!(a5.hash(), longest_chain_select.finality_target(
			a3.hash(), Some(5)).unwrap().unwrap());
		assert_eq!(a5.hash(), longest_chain_select.finality_target(
			a4.hash(), Some(5)).unwrap().unwrap());
		assert_eq!(a5.hash(), longest_chain_select.finality_target(
			a5.hash(), Some(5)).unwrap().unwrap());

		assert_eq!(b4.hash(), longest_chain_select.finality_target(
			b2.hash(), Some(5)).unwrap().unwrap());
		assert_eq!(b4.hash(), longest_chain_select.finality_target(
			b3.hash(), Some(5)).unwrap().unwrap());
		assert_eq!(b4.hash(), longest_chain_select.finality_target(
			b4.hash(), Some(5)).unwrap().unwrap());

		assert_eq!(c3.hash(), longest_chain_select.finality_target(
			c3.hash(), Some(5)).unwrap().unwrap());

		assert_eq!(d2.hash(), longest_chain_select.finality_target(
			d2.hash(), Some(5)).unwrap().unwrap());


		// search only blocks with number <= 4

		assert_eq!(a4.hash(), longest_chain_select.finality_target(
			genesis_hash, Some(4)).unwrap().unwrap());
		assert_eq!(a4.hash(), longest_chain_select.finality_target(
			a1.hash(), Some(4)).unwrap().unwrap());
		assert_eq!(a4.hash(), longest_chain_select.finality_target(
			a2.hash(), Some(4)).unwrap().unwrap());
		assert_eq!(a4.hash(), longest_chain_select.finality_target(
			a3.hash(), Some(4)).unwrap().unwrap());
		assert_eq!(a4.hash(), longest_chain_select.finality_target(
			a4.hash(), Some(4)).unwrap().unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			a5.hash(), Some(4)).unwrap());

		assert_eq!(b4.hash(), longest_chain_select.finality_target(
			b2.hash(), Some(4)).unwrap().unwrap());
		assert_eq!(b4.hash(), longest_chain_select.finality_target(
			b3.hash(), Some(4)).unwrap().unwrap());
		assert_eq!(b4.hash(), longest_chain_select.finality_target(
			b4.hash(), Some(4)).unwrap().unwrap());

		assert_eq!(c3.hash(), longest_chain_select.finality_target(
			c3.hash(), Some(4)).unwrap().unwrap());

		assert_eq!(d2.hash(), longest_chain_select.finality_target(
			d2.hash(), Some(4)).unwrap().unwrap());


		// search only blocks with number <= 3

		assert_eq!(a3.hash(), longest_chain_select.finality_target(
			genesis_hash, Some(3)).unwrap().unwrap());
		assert_eq!(a3.hash(), longest_chain_select.finality_target(
			a1.hash(), Some(3)).unwrap().unwrap());
		assert_eq!(a3.hash(), longest_chain_select.finality_target(
			a2.hash(), Some(3)).unwrap().unwrap());
		assert_eq!(a3.hash(), longest_chain_select.finality_target(
			a3.hash(), Some(3)).unwrap().unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			a4.hash(), Some(3)).unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			a5.hash(), Some(3)).unwrap());

		assert_eq!(b3.hash(), longest_chain_select.finality_target(
			b2.hash(), Some(3)).unwrap().unwrap());
		assert_eq!(b3.hash(), longest_chain_select.finality_target(
			b3.hash(), Some(3)).unwrap().unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			b4.hash(), Some(3)).unwrap());

		assert_eq!(c3.hash(), longest_chain_select.finality_target(
			c3.hash(), Some(3)).unwrap().unwrap());

		assert_eq!(d2.hash(), longest_chain_select.finality_target(
			d2.hash(), Some(3)).unwrap().unwrap());


		// search only blocks with number <= 2

		assert_eq!(a2.hash(), longest_chain_select.finality_target(
			genesis_hash, Some(2)).unwrap().unwrap());
		assert_eq!(a2.hash(), longest_chain_select.finality_target(
			a1.hash(), Some(2)).unwrap().unwrap());
		assert_eq!(a2.hash(), longest_chain_select.finality_target(
			a2.hash(), Some(2)).unwrap().unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			a3.hash(), Some(2)).unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			a4.hash(), Some(2)).unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			a5.hash(), Some(2)).unwrap());

		assert_eq!(b2.hash(), longest_chain_select.finality_target(
			b2.hash(), Some(2)).unwrap().unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			b3.hash(), Some(2)).unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			b4.hash(), Some(2)).unwrap());

		assert_eq!(None, longest_chain_select.finality_target(
			c3.hash(), Some(2)).unwrap());

		assert_eq!(d2.hash(), longest_chain_select.finality_target(
			d2.hash(), Some(2)).unwrap().unwrap());


		// search only blocks with number <= 1

		assert_eq!(a1.hash(), longest_chain_select.finality_target(
			genesis_hash, Some(1)).unwrap().unwrap());
		assert_eq!(a1.hash(), longest_chain_select.finality_target(
			a1.hash(), Some(1)).unwrap().unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			a2.hash(), Some(1)).unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			a3.hash(), Some(1)).unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			a4.hash(), Some(1)).unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			a5.hash(), Some(1)).unwrap());

		assert_eq!(None, longest_chain_select.finality_target(
			b2.hash(), Some(1)).unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			b3.hash(), Some(1)).unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			b4.hash(), Some(1)).unwrap());

		assert_eq!(None, longest_chain_select.finality_target(
			c3.hash(), Some(1)).unwrap());

		assert_eq!(None, longest_chain_select.finality_target(
			d2.hash(), Some(1)).unwrap());

		// search only blocks with number <= 0

		assert_eq!(genesis_hash, longest_chain_select.finality_target(
			genesis_hash, Some(0)).unwrap().unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			a1.hash(), Some(0)).unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			a2.hash(), Some(0)).unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			a3.hash(), Some(0)).unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			a4.hash(), Some(0)).unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			a5.hash(), Some(0)).unwrap());

		assert_eq!(None, longest_chain_select.finality_target(
			b2.hash(), Some(0)).unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			b3.hash(), Some(0)).unwrap());
		assert_eq!(None, longest_chain_select.finality_target(
			b4.hash(), Some(0)).unwrap());

		assert_eq!(None, longest_chain_select.finality_target(
			c3.hash().clone(), Some(0)).unwrap());

		assert_eq!(None, longest_chain_select.finality_target(
			d2.hash().clone(), Some(0)).unwrap());
	}

	#[test]
	fn best_containing_on_longest_chain_with_max_depth_higher_than_best() {
		// block tree:
		// G -> A1 -> A2

		let client = test_client::new();

		// G -> A1
		let a1 = client.new_block().unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block().unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		let genesis_hash = client.info().unwrap().chain.genesis_hash;
		let longest_chain_select = test_client::client::LongestChain::new(
			Arc::new(client.backend().as_in_memory()),
			client.import_lock()
		);

		assert_eq!(a2.hash(), longest_chain_select.finality_target(
			genesis_hash, Some(10)).unwrap().unwrap());
	}

	#[test]
	fn key_changes_works() {
		let (client, _, test_cases) = prepare_client_with_key_changes();

		for (index, (begin, end, key, expected_result)) in test_cases.into_iter().enumerate() {
			let end = client.block_hash(end).unwrap().unwrap();
			let actual_result = client.key_changes(begin, BlockId::Hash(end), &StorageKey(key)).unwrap();
			match actual_result == expected_result {
				true => (),
				false => panic!(format!("Failed test {}: actual = {:?}, expected = {:?}",
					index, actual_result, expected_result)),
			}
		}
	}

	#[test]
	fn import_with_justification() {
		use test_client::blockchain::Backend;

		let client = test_client::new();

		// G -> A1
		let a1 = client.new_block().unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block_at(&BlockId::Hash(a1.hash())).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		// A2 -> A3
		let justification = vec![1, 2, 3];
		let a3 = client.new_block_at(&BlockId::Hash(a2.hash())).unwrap().bake().unwrap();
		client.import_justified(BlockOrigin::Own, a3.clone(), justification.clone()).unwrap();

		assert_eq!(
			client.backend().blockchain().last_finalized().unwrap(),
			a3.hash(),
		);

		assert_eq!(
			client.backend().blockchain().justification(BlockId::Hash(a3.hash())).unwrap(),
			Some(justification),
		);

		assert_eq!(
			client.backend().blockchain().justification(BlockId::Hash(a1.hash())).unwrap(),
			None,
		);

		assert_eq!(
			client.backend().blockchain().justification(BlockId::Hash(a2.hash())).unwrap(),
			None,
		);
	}
}
