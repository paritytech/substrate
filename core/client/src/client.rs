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
use log::{info, trace, warn};
use futures03::channel::mpsc;
use parking_lot::{Mutex, RwLock};
use codec::{Encode, Decode};
use hash_db::{Hasher, Prefix};
use primitives::{
	Blake2Hasher, H256, ChangesTrieConfiguration, convert_hash, NeverNativeValue, ExecutionContext,
	NativeOrEncoded, storage::{StorageKey, StorageData, well_known_keys},
	offchain::{OffchainExt, self}, traits::CodeExecutor,
};
use substrate_telemetry::{telemetry, SUBSTRATE_INFO};
use sr_primitives::{
	Justification, BuildStorage,
	generic::{BlockId, SignedBlock, DigestItem},
	traits::{
		Block as BlockT, Header as HeaderT, Zero, NumberFor,
		ApiRef, ProvideRuntimeApi, SaturatedConversion, One, DigestFor,
	},
};
use state_machine::{
	DBValue, Backend as StateBackend, ChangesTrieAnchorBlockId, ExecutionStrategy, ExecutionManager,
	prove_read, prove_child_read, ChangesTrieRootsStorage, ChangesTrieStorage,
	ChangesTrieTransaction, ChangesTrieConfigurationRange, key_changes, key_changes_proof,
	OverlayedChanges, BackendTrustLevel,
};
use executor::{RuntimeVersion, RuntimeInfo};
use consensus::{
	Error as ConsensusError, BlockStatus, BlockImportParams, BlockCheckParams,
	ImportResult, BlockOrigin, ForkChoiceStrategy,
	SelectChain, self,
};
use header_metadata::{HeaderMetadata, CachedHeaderMetadata};

use crate::{
	runtime_api::{
		CallRuntimeAt, ConstructRuntimeApi, Core as CoreApi, ProofRecorder,
		InitializeBlock,
	},
	backend::{
		self, BlockImportOperation, PrunableStateChangesTrieStorage,
		ClientImportOperation, Finalizer, ImportSummary,
	},
	blockchain::{
		self, Info as ChainInfo, Backend as ChainBackend,
		HeaderBackend as ChainHeaderBackend, ProvideCache, Cache,
		well_known_cache_keys::Id as CacheKeyId,
	},
	call_executor::{CallExecutor, LocalCallExecutor},
	notifications::{StorageNotifications, StorageEventStream},
	light::{call_executor::prove_execution, fetcher::ChangesProof},
	block_builder::{self, api::BlockBuilder as BlockBuilderAPI},
	error::Error,
	cht, error, in_mem, genesis
};

/// Type that implements `futures::Stream` of block import events.
pub type ImportNotifications<Block> = mpsc::UnboundedReceiver<BlockImportNotification<Block>>;

/// A stream of block finality notifications.
pub type FinalityNotifications<Block> = mpsc::UnboundedReceiver<FinalityNotification<Block>>;

type StorageUpdate<B, Block> = <
	<
		<B as backend::Backend<Block, Blake2Hasher>>::BlockImportOperation
			as BlockImportOperation<Block, Blake2Hasher>
	>::State as state_machine::Backend<Blake2Hasher>>::Transaction;
type ChangesUpdate<Block> = ChangesTrieTransaction<Blake2Hasher, NumberFor<Block>>;

/// Expected hashes of blocks at given heights.
///
/// This may be used as chain spec extension to filter out known, unwanted forks.
pub type ForkBlocks<Block> = Option<HashMap<NumberFor<Block>, <Block as BlockT>::Hash>>;

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
	// holds the block hash currently being imported. TODO: replace this with block queue
	importing_block: RwLock<Option<Block::Hash>>,
	fork_blocks: ForkBlocks<Block>,
	execution_strategies: ExecutionStrategies,
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
	fn storage_changes_notification_stream(
		&self,
		filter_keys: Option<&[StorageKey]>,
		child_filter_keys: Option<&[(StorageKey, Option<Vec<StorageKey>>)]>,
	) -> error::Result<StorageEventStream<Block::Hash>>;
}

/// Fetch block body by ID.
pub trait BlockBody<Block: BlockT> {
	/// Get block body by ID. Returns `None` if the body is not stored.
	fn block_body(&self,
		id: &BlockId<Block>
	) -> error::Result<Option<Vec<<Block as BlockT>::Extrinsic>>>;
}

/// Provide a list of potential uncle headers for a given block.
pub trait ProvideUncles<Block: BlockT> {
	/// Gets the uncles of the block with `target_hash` going back `max_generation` ancestors.
	fn uncles(&self, target_hash: Block::Hash, max_generation: NumberFor<Block>)
		-> error::Result<Vec<Block::Header>>;
}

/// Client info
#[derive(Debug)]
pub struct ClientInfo<Block: BlockT> {
	/// Best block hash.
	pub chain: ChainInfo<Block>,
	/// State Cache Size currently used by the backend
	pub used_state_cache_size: Option<usize>,
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
	/// List of retracted blocks ordered by block number.
	pub retracted: Vec<Block::Hash>,
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
	keystore: Option<primitives::traits::BareCryptoStorePtr>,
) -> error::Result<Client<
	in_mem::Backend<Block, Blake2Hasher>,
	LocalCallExecutor<in_mem::Backend<Block, Blake2Hasher>, E>,
	Block,
	RA
>> where
	E: CodeExecutor + RuntimeInfo,
	S: BuildStorage,
	Block: BlockT<Hash=H256>,
{
	new_with_backend(Arc::new(in_mem::Backend::new()), executor, genesis_storage, keystore)
}

/// Create a client with the explicitly provided backend.
/// This is useful for testing backend implementations.
pub fn new_with_backend<B, E, Block, S, RA>(
	backend: Arc<B>,
	executor: E,
	build_genesis_storage: S,
	keystore: Option<primitives::traits::BareCryptoStorePtr>,
) -> error::Result<Client<B, LocalCallExecutor<B, E>, Block, RA>>
	where
		E: CodeExecutor + RuntimeInfo,
		S: BuildStorage,
		Block: BlockT<Hash=H256>,
		B: backend::LocalBackend<Block, Blake2Hasher>
{
	let call_executor = LocalCallExecutor::new(backend.clone(), executor, keystore);
	Client::new(backend, call_executor, build_genesis_storage, Default::default(), Default::default())
}

/// Figure out the block type for a given type (for now, just a `Client`).
pub trait BlockOf {
	/// The type of the block.
	type Type: BlockT<Hash=H256>;
}

impl<B, E, Block, RA> BlockOf for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
	Block: BlockT<Hash=H256>,
{
	type Type = Block;
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
		fork_blocks: ForkBlocks<Block>,
		execution_strategies: ExecutionStrategies
	) -> error::Result<Self> {
		if backend.blockchain().header(BlockId::Number(Zero::zero()))?.is_none() {
			let (genesis_storage, children_genesis_storage) = build_genesis_storage.build_storage()?;
			let mut op = backend.begin_operation()?;
			backend.begin_state_operation(&mut op, BlockId::Hash(Default::default()))?;
			let state_root = op.reset_storage(genesis_storage, children_genesis_storage)?;
			let genesis_block = genesis::construct_genesis_block::<Block>(state_root.into());
			info!("Initializing Genesis block/state (state: {}, header-hash: {})",
				genesis_block.header().state_root(),
				genesis_block.header().hash()
			);
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
			importing_block: Default::default(),
			fork_blocks,
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

	/// Given a `BlockId` and a key prefix, return the matching child storage keys in that block.
	pub fn storage_keys(&self, id: &BlockId<Block>, key_prefix: &StorageKey) -> error::Result<Vec<StorageKey>> {
		let keys = self.state_at(id)?.keys(&key_prefix.0).into_iter().map(StorageKey).collect();
		Ok(keys)
	}

	/// Given a `BlockId` and a key, return the value under the key in that block.
	pub fn storage(&self, id: &BlockId<Block>, key: &StorageKey) -> error::Result<Option<StorageData>> {
		Ok(self.state_at(id)?
			.storage(&key.0).map_err(|e| error::Error::from_state(Box::new(e)))?
			.map(StorageData)
		)
	}

	/// Given a `BlockId` and a key, return the value under the hash in that block.
	pub fn storage_hash(&self, id: &BlockId<Block>, key: &StorageKey)
		-> error::Result<Option<Block::Hash>> {
		Ok(self.state_at(id)?
			.storage_hash(&key.0).map_err(|e| error::Error::from_state(Box::new(e)))?
		)
	}

	/// Given a `BlockId`, a key prefix, and a child storage key, return the matching child storage keys.
	pub fn child_storage_keys(
		&self,
		id: &BlockId<Block>,
		child_storage_key: &StorageKey,
		key_prefix: &StorageKey
	) -> error::Result<Vec<StorageKey>> {
		let keys = self.state_at(id)?
			.child_keys(&child_storage_key.0, &key_prefix.0)
			.into_iter()
			.map(StorageKey)
			.collect();
		Ok(keys)
	}

	/// Given a `BlockId`, a key and a child storage key, return the value under the key in that block.
	pub fn child_storage(
		&self,
		id: &BlockId<Block>,
		child_storage_key: &StorageKey,
		key: &StorageKey
	) -> error::Result<Option<StorageData>> {
		Ok(self.state_at(id)?
			.child_storage(&child_storage_key.0, &key.0).map_err(|e| error::Error::from_state(Box::new(e)))?
			.map(StorageData))
	}

	/// Given a `BlockId`, a key and a child storage key, return the hash under the key in that block.
	pub fn child_storage_hash(
		&self,
		id: &BlockId<Block>,
		child_storage_key: &StorageKey,
		key: &StorageKey
	) -> error::Result<Option<Block::Hash>> {
		Ok(self.state_at(id)?
			.child_storage_hash(&child_storage_key.0, &key.0).map_err(|e| error::Error::from_state(Box::new(e)))?
		)
	}

	/// Get the code at a given block.
	pub fn code_at(&self, id: &BlockId<Block>) -> error::Result<Vec<u8>> {
		Ok(self.storage(id, &StorageKey(well_known_keys::CODE.to_vec()))?
			.expect("None is returned if there's no value stored for the given key;\
				':code' key is always defined; qed").0)
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
	pub fn read_proof<I>(&self, id: &BlockId<Block>, keys: I) -> error::Result<Vec<Vec<u8>>> where
		I: IntoIterator,
		I::Item: AsRef<[u8]>,
	{
		self.state_at(id)
			.and_then(|state| prove_read(state, keys)
				.map_err(Into::into))
	}

	/// Reads child storage value at a given block + storage_key + key, returning
	/// read proof.
	pub fn read_child_proof<I>(
		&self,
		id: &BlockId<Block>,
		storage_key: &[u8],
		keys: I,
	) -> error::Result<Vec<Vec<u8>>> where
		I: IntoIterator,
		I::Item: AsRef<[u8]>,
	{
		self.state_at(id)
			.and_then(|state| prove_child_read(state, storage_key, keys)
				.map_err(Into::into))
	}

	/// Execute a call to a contract on top of state in a block of given hash
	/// AND returning execution proof.
	///
	/// No changes are made.
	pub fn execution_proof(&self,
		id: &BlockId<Block>,
		method: &str,
		call_data: &[u8]
	) -> error::Result<(Vec<u8>, Vec<Vec<u8>>)> {
		let state = self.state_at(id)?;
		let header = self.prepare_environment_block(id)?;
		prove_execution(state, header, &self.executor, method, call_data)
	}

	/// Reads given header and generates CHT-based header proof.
	pub fn header_proof(&self, id: &BlockId<Block>) -> error::Result<(Block::Header, Vec<Vec<u8>>)> {
		self.header_proof_with_cht_size(id, cht::size())
	}

	/// Get block hash by number.
	pub fn block_hash(&self,
		block_number: <<Block as BlockT>::Header as HeaderT>::Number
	) -> error::Result<Option<Block::Hash>> {
		self.backend.blockchain().hash(block_number)
	}

	/// Reads given header and generates CHT-based header proof for CHT of given size.
	pub fn header_proof_with_cht_size(
		&self,
		id: &BlockId<Block>,
		cht_size: NumberFor<Block>,
	) -> error::Result<(Block::Header, Vec<Vec<u8>>)> {
		let proof_error = || error::Error::Backend(format!("Failed to generate header proof for {:?}", id));
		let header = self.backend.blockchain().expect_header(*id)?;
		let block_num = *header.number();
		let cht_num = cht::block_to_cht_number(cht_size, block_num).ok_or_else(proof_error)?;
		let cht_start = cht::start_number(cht_size, cht_num);
		let mut current_num = cht_start;
		let cht_range = ::std::iter::from_fn(|| {
			let old_current_num = current_num;
			current_num = current_num + One::one();
			Some(old_current_num)
		});
		let headers = cht_range.map(|num| self.block_hash(num));
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
		let last_num = self.backend.blockchain().expect_block_number_from_id(&last)?;
		if first > last_num {
			return Err(error::Error::ChangesTrieAccessFailed("Invalid changes trie range".into()));
		}
		let finalized_number = self.backend.blockchain().info().finalized_number;
		let oldest = storage.oldest_changes_trie_block(&config, finalized_number);
		let first = ::std::cmp::max(first, oldest);
		Ok(Some((first, last)))
	}

	/// Get pairs of (block, extrinsic) where key has been changed at given blocks range.
	/// Works only for runtimes that are supporting changes tries.
	///
	/// Changes are returned in descending order (i.e. last block comes first).
	pub fn key_changes(
		&self,
		first: NumberFor<Block>,
		last: BlockId<Block>,
		storage_key: Option<&StorageKey>,
		key: &StorageKey
	) -> error::Result<Vec<(NumberFor<Block>, u32)>> {
		let (config, storage) = self.require_changes_trie()?;
		let last_number = self.backend.blockchain().expect_block_number_from_id(&last)?;
		let last_hash = self.backend.blockchain().expect_block_hash_from_id(&last)?;

		// FIXME: remove this in https://github.com/paritytech/substrate/pull/3201
		let config_range = ChangesTrieConfigurationRange {
			config: &config,
			zero: Zero::zero(),
			end: None,
		};

		key_changes::<Blake2Hasher, _>(
			config_range,
			&*storage,
			first,
			&ChangesTrieAnchorBlockId {
				hash: convert_hash(&last_hash),
				number: last_number,
			},
			self.backend.blockchain().info().best_number,
			storage_key.as_ref().map(|sk| sk.0.as_slice()),
			&key.0)
		.and_then(|r| r.map(|r| r.map(|(block, tx)| (block, tx))).collect::<Result<_, _>>())
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
		storage_key: Option<&StorageKey>,
		key: &StorageKey,
	) -> error::Result<ChangesProof<Block::Header>> {
		self.key_changes_proof_with_cht_size(
			first,
			last,
			min,
			max,
			storage_key,
			key,
			cht::size(),
		)
	}

	/// Does the same work as `key_changes_proof`, but assumes that CHTs are of passed size.
	pub fn key_changes_proof_with_cht_size(
		&self,
		first: Block::Hash,
		last: Block::Hash,
		min: Block::Hash,
		max: Block::Hash,
		storage_key: Option<&StorageKey>,
		key: &StorageKey,
		cht_size: NumberFor<Block>,
	) -> error::Result<ChangesProof<Block::Header>> {
		struct AccessedRootsRecorder<'a, Block: BlockT> {
			storage: &'a dyn ChangesTrieStorage<Blake2Hasher, NumberFor<Block>>,
			min: NumberFor<Block>,
			required_roots_proofs: Mutex<BTreeMap<NumberFor<Block>, H256>>,
		};

		impl<'a, Block: BlockT> ChangesTrieRootsStorage<Blake2Hasher, NumberFor<Block>> for AccessedRootsRecorder<'a, Block> {
			fn build_anchor(&self, hash: H256) -> Result<ChangesTrieAnchorBlockId<H256, NumberFor<Block>>, String> {
				self.storage.build_anchor(hash)
			}

			fn root(
				&self,
				anchor: &ChangesTrieAnchorBlockId<H256, NumberFor<Block>>,
				block: NumberFor<Block>,
			) -> Result<Option<H256>, String> {
				let root = self.storage.root(anchor, block)?;
				if block < self.min {
					if let Some(ref root) = root {
						self.required_roots_proofs.lock().insert(
							block,
							root.clone()
						);
					}
				}
				Ok(root)
			}
		}

		impl<'a, Block: BlockT> ChangesTrieStorage<Blake2Hasher, NumberFor<Block>> for AccessedRootsRecorder<'a, Block> {
			fn as_roots_storage(&self) -> &dyn state_machine::ChangesTrieRootsStorage<Blake2Hasher, NumberFor<Block>> {
				self
			}

			fn with_cached_changed_keys(
				&self,
				root: &H256,
				functor: &mut dyn FnMut(&HashMap<Option<Vec<u8>>, HashSet<Vec<u8>>>),
			) -> bool {
				self.storage.with_cached_changed_keys(root, functor)
			}

			fn get(&self, key: &H256, prefix: Prefix) -> Result<Option<DBValue>, String> {
				self.storage.get(key, prefix)
			}
		}

		let (config, storage) = self.require_changes_trie()?;
		let min_number = self.backend.blockchain().expect_block_number_from_id(&BlockId::Hash(min))?;

		let recording_storage = AccessedRootsRecorder::<Block> {
			storage,
			min: min_number,
			required_roots_proofs: Mutex::new(BTreeMap::new()),
		};

		let max_number = ::std::cmp::min(
			self.backend.blockchain().info().best_number,
			self.backend.blockchain().expect_block_number_from_id(&BlockId::Hash(max))?,
		);

		// FIXME: remove this in https://github.com/paritytech/substrate/pull/3201
		let config_range = ChangesTrieConfigurationRange {
			config: &config,
			zero: Zero::zero(),
			end: None,
		};

		// fetch key changes proof
		let first_number = self.backend.blockchain()
			.expect_block_number_from_id(&BlockId::Hash(first))?;
		let last_number = self.backend.blockchain()
			.expect_block_number_from_id(&BlockId::Hash(last))?;
		let key_changes_proof = key_changes_proof::<Blake2Hasher, _>(
			config_range,
			&recording_storage,
			first_number,
			&ChangesTrieAnchorBlockId {
				hash: convert_hash(&last),
				number: last_number,
			},
			max_number,
			storage_key.as_ref().map(|sk| sk.0.as_slice()),
			&key.0,
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
		cht_size: NumberFor<Block>,
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
		cht_size: NumberFor<Block>,
		cht_num: NumberFor<Block>,
		blocks: Vec<NumberFor<Block>>
	) -> error::Result<Vec<Vec<u8>>> {
		let cht_start = cht::start_number(cht_size, cht_num);
		let mut current_num = cht_start;
		let cht_range = ::std::iter::from_fn(|| {
			let old_current_num = current_num;
			current_num = current_num + One::one();
			Some(old_current_num)
		});
		let roots = cht_range
			.map(|num| self.header(&BlockId::Number(num))
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
		&self,
		inherent_digests: DigestFor<Block>,
	) -> error::Result<block_builder::BlockBuilder<Block, Self>> where
		E: Clone + Send + Sync,
		RA: Send + Sync,
		Self: ProvideRuntimeApi,
		<Self as ProvideRuntimeApi>::Api: BlockBuilderAPI<Block>
	{
		block_builder::BlockBuilder::new(self, inherent_digests)
	}

	/// Create a new block, built on top of `parent`.
	pub fn new_block_at(
		&self,
		parent: &BlockId<Block>,
		inherent_digests: DigestFor<Block>,
	) -> error::Result<block_builder::BlockBuilder<Block, Self>> where
		E: Clone + Send + Sync,
		RA: Send + Sync,
		Self: ProvideRuntimeApi,
		<Self as ProvideRuntimeApi>::Api: BlockBuilderAPI<Block>
	{
		block_builder::BlockBuilder::at_block(parent, &self, false, inherent_digests)
	}

	/// Create a new block, built on top of `parent` with proof recording enabled.
	///
	/// While proof recording is enabled, all accessed trie nodes are saved.
	/// These recorded trie nodes can be used by a third party to proof the
	/// output of this block builder without having access to the full storage.
	pub fn new_block_at_with_proof_recording(
		&self,
		parent: &BlockId<Block>,
		inherent_digests: DigestFor<Block>,
	) -> error::Result<block_builder::BlockBuilder<Block, Self>> where
		E: Clone + Send + Sync,
		RA: Send + Sync,
		Self: ProvideRuntimeApi,
		<Self as ProvideRuntimeApi>::Api: BlockBuilderAPI<Block>
	{
		block_builder::BlockBuilder::at_block(parent, &self, true, inherent_digests)
	}

	/// Lock the import lock, and run operations inside.
	pub fn lock_import_and_run<R, Err, F>(&self, f: F) -> Result<R, Err> where
		F: FnOnce(&mut ClientImportOperation<Block, Blake2Hasher, B>) -> Result<R, Err>,
		Err: From<error::Error>,
	{
		let inner = || {
			let _import_lock = self.backend.get_import_lock().lock();

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

	/// Apply a checked and validated block to an operation. If a justification is provided
	/// then `finalized` *must* be true.
	fn apply_block(
		&self,
		operation: &mut ClientImportOperation<Block, Blake2Hasher, B>,
		import_block: BlockImportParams<Block>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> error::Result<ImportResult> where
		E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone,
	{
		let BlockImportParams {
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
		let height = (*import_headers.post().number()).saturated_into::<u64>();

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

		if let Ok(ImportResult::Imported(ref aux)) = result {
			if aux.is_new_best {
				telemetry!(SUBSTRATE_INFO; "block.import";
					"height" => height,
					"best" => ?hash,
					"origin" => ?origin
				);
			}
		}

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

		let info = self.backend.blockchain().info();

		// the block is lower than our last finalized block so it must revert
		// finality, refusing import.
		if *import_headers.post().number() <= info.finalized_number {
			return Err(error::Error::NotInFinalizedChain);
		}

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
			self.apply_finality_with_block_hash(operation, parent_hash, None, info.best_hash, make_notifications)?;
		}

		// FIXME #1232: correct path logic for when to execute this function
		let (storage_update, changes_update, storage_changes) = self.block_execution(
			&operation.op,
			&import_headers,
			origin,
			hash,
			body.clone(),
		)?;

		let is_new_best = finalized || match fork_choice {
			ForkChoiceStrategy::LongestChain => import_headers.post().number() > &info.best_number,
			ForkChoiceStrategy::Custom(v) => v,
		};

		let leaf_state = if finalized {
			crate::backend::NewBlockState::Final
		} else if is_new_best {
			crate::backend::NewBlockState::Best
		} else {
			crate::backend::NewBlockState::Normal
		};

		let retracted = if is_new_best {
			let route_from_best = header_metadata::tree_route(
				self.backend.blockchain(),
				info.best_hash,
				parent_hash,
			)?;
			route_from_best.retracted().iter().rev().map(|e| e.hash.clone()).collect()
		} else {
			Vec::default()
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
			operation.op.update_storage(storage_changes.0, storage_changes.1)?;
		}
		if let Some(Some(changes_update)) = changes_update {
			operation.op.update_changes_trie(changes_update)?;
		}

		operation.op.insert_aux(aux)?;

		if make_notifications {
			if finalized {
				operation.notify_finalized.push(hash);
			}

			operation.notify_imported = Some(ImportSummary {
				hash,
				origin,
				header: import_headers.into_post(),
				is_new_best,
				storage_changes,
				retracted,
			})
		}

		Ok(ImportResult::imported(is_new_best))
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
		Option<Option<ChangesUpdate<Block>>>,
		Option<(
			Vec<(Vec<u8>, Option<Vec<u8>>)>,
			Vec<(Vec<u8>, Vec<(Vec<u8>, Option<Vec<u8>>)>)>
		)>
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
						ExecutionStrategy::AlwaysWasm => ExecutionManager::AlwaysWasm(BackendTrustLevel::Trusted),
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

				let encoded_block = <Block as BlockT>::encode_from(
					import_headers.pre(),
					&body.unwrap_or_default()
				);

				let (_, storage_update, changes_update) = self.executor
					.call_at_state::<_, _, NeverNativeValue, fn() -> _>(
						transaction_state,
						&mut overlay,
						"Core_execute_block",
						&encoded_block,
						match origin {
							BlockOrigin::NetworkInitialSync => get_execution_manager(
								self.execution_strategies().syncing,
							),
							_ => get_execution_manager(self.execution_strategies().importing),
						},
						None,
						None,
					)?;

				overlay.commit_prospective();

				let (top, children) = overlay.into_committed();
				let children = children.map(|(sk, it)| (sk, it.collect())).collect();
				if import_headers.post().state_root() != &storage_update.1 {
					return Err(error::Error::InvalidStateRoot);
				}

				Ok((Some(storage_update.0), Some(changes_update), Some((top.collect(), children))))
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

		let route_from_finalized = header_metadata::tree_route(self.backend.blockchain(), last_finalized, block)?;

		if let Some(retracted) = route_from_finalized.retracted().get(0) {
			warn!("Safety violation: attempted to revert finalized block {:?} which is not in the \
				same chain as last finalized {:?}", retracted, last_finalized);

			return Err(error::Error::NotInFinalizedChain);
		}

		let route_from_best = header_metadata::tree_route(self.backend.blockchain(), best_block, block)?;

		// if the block is not a direct ancestor of the current best chain,
		// then some other block is the common ancestor.
		if route_from_best.common_block().hash != block {
			// NOTE: we're setting the finalized block as best block, this might
			// be slightly inaccurate since we might have a "better" block
			// further along this chain, but since best chain selection logic is
			// pluggable we cannot make a better choice here. usages that need
			// an accurate "best" block need to go through `SelectChain`
			// instead.
			operation.op.mark_head(BlockId::Hash(block))?;
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

	fn notify_imported(&self, notify_import: ImportSummary<Block>) -> error::Result<()> {
		if let Some(storage_changes) = notify_import.storage_changes {
			// TODO [ToDr] How to handle re-orgs? Should we re-emit all storage changes?
			self.storage_notifications.lock()
				.trigger(
					&notify_import.hash,
					storage_changes.0.into_iter(),
					storage_changes.1.into_iter().map(|(sk, v)| (sk, v.into_iter())),
				);
		}

		let notification = BlockImportNotification::<Block> {
			hash: notify_import.hash,
			origin: notify_import.origin,
			header: notify_import.header,
			is_new_best: notify_import.is_new_best,
			retracted: notify_import.retracted,
		};

		self.import_notification_sinks.lock()
			.retain(|sink| sink.unbounded_send(notification.clone()).is_ok());

		Ok(())
	}

	/// Attempts to revert the chain by `n` blocks. Returns the number of blocks that were
	/// successfully reverted.
	pub fn revert(&self, n: NumberFor<Block>) -> error::Result<NumberFor<Block>> {
		Ok(self.backend.revert(n)?)
	}

	/// Get blockchain info.
	pub fn info(&self) -> ClientInfo<Block> {
		let info = self.backend.blockchain().info();
		ClientInfo {
			chain: info,
			used_state_cache_size: self.backend.used_state_cache_size(),
		}
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
				None => Err(Error::UnknownBlock(format!("{:?}", id))),
			}
		};

		let genesis_hash = self.backend.blockchain().info().genesis_hash;
		if genesis_hash == target_hash { return Ok(Vec::new()); }

		let mut current_hash = target_hash;
		let mut current = load_header(current_hash)?;
		let mut ancestor_hash = *current.parent_hash();
		let mut ancestor = load_header(ancestor_hash)?;
		let mut uncles = Vec::new();

		for _generation in 0..max_generation.saturated_into() {
			let children = self.backend.blockchain().children(ancestor_hash)?;
			uncles.extend(children.into_iter().filter(|h| h != &current_hash));
			current_hash = ancestor_hash;
			if genesis_hash == current_hash { break; }
			current = ancestor;
			ancestor_hash = *current.parent_hash();
			ancestor = load_header(ancestor_hash)?;
		}
		trace!("Collected {} uncles", uncles.len());
		Ok(uncles)
	}

	fn changes_trie_config(&self) -> Result<Option<ChangesTrieConfiguration>, Error> {
		Ok(self.backend.state_at(BlockId::Number(self.backend.blockchain().info().best_number))?
			.storage(well_known_keys::CHANGES_TRIE_CONFIG)
			.map_err(|e| error::Error::from_state(Box::new(e)))?
			.and_then(|c| Decode::decode(&mut &*c).ok()))
	}

	/// Prepare in-memory header that is used in execution environment.
	fn prepare_environment_block(&self, parent: &BlockId<Block>) -> error::Result<Block::Header> {
		let parent_header = self.backend.blockchain().expect_header(*parent)?;
		Ok(<<Block as BlockT>::Header as HeaderT>::new(
			self.backend.blockchain().expect_block_number_from_id(parent)? + One::one(),
			Default::default(),
			Default::default(),
			parent_header.hash(),
			Default::default(),
		))
	}
}

impl<B, E, Block, RA> HeaderMetadata<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
	Block: BlockT<Hash=H256>,
{
	type Error = error::Error;

	fn header_metadata(&self, hash: Block::Hash) -> Result<CachedHeaderMetadata<Block>, Self::Error> {
		self.backend.blockchain().header_metadata(hash)
	}

	fn insert_header_metadata(&self, hash: Block::Hash, metadata: CachedHeaderMetadata<Block>) {
		self.backend.blockchain().insert_header_metadata(hash, metadata)
	}

	fn remove_header_metadata(&self, hash: Block::Hash) {
		self.backend.blockchain().remove_header_metadata(hash)
	}
}

impl<B, E, Block, RA> ProvideUncles<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
	Block: BlockT<Hash=H256>,
{
	fn uncles(&self, target_hash: Block::Hash, max_generation: NumberFor<Block>) -> error::Result<Vec<Block::Header>> {
		Ok(Client::uncles(self, target_hash, max_generation)?
			.into_iter()
			.filter_map(|hash| Client::header(self, &BlockId::Hash(hash)).unwrap_or(None))
			.collect()
		)
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

	fn info(&self) -> blockchain::Info<Block> {
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

impl<B, E, Block, RA> ChainHeaderBackend<Block> for &Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync,
	Block: BlockT<Hash=H256>,
	RA: Send + Sync,
{
	fn header(&self, id: BlockId<Block>) -> error::Result<Option<Block::Header>> {
		(**self).backend.blockchain().header(id)
	}

	fn info(&self) -> blockchain::Info<Block> {
		(**self).backend.blockchain().info()
	}

	fn status(&self, id: BlockId<Block>) -> error::Result<blockchain::BlockStatus> {
		(**self).status(id)
	}

	fn number(&self, hash: Block::Hash) -> error::Result<Option<<<Block as BlockT>::Header as HeaderT>::Number>> {
		(**self).number(hash)
	}

	fn hash(&self, number: NumberFor<Block>) -> error::Result<Option<Block::Hash>> {
		(**self).hash(number)
	}
}

impl<B, E, Block, RA> ProvideCache<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	Block: BlockT<Hash=H256>,
{
	fn cache(&self) -> Option<Arc<dyn Cache<Block>>> {
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
		NC: FnOnce() -> result::Result<R, String> + UnwindSafe,
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
			ExecutionContext::OffchainCall(Some((_, capabilities))) if capabilities.has_all() =>
				self.execution_strategies.offchain_worker.get_manager(),
			ExecutionContext::OffchainCall(_) =>
				self.execution_strategies.other.get_manager(),
		};

		let capabilities = context.capabilities();
		let offchain_extensions = if let ExecutionContext::OffchainCall(Some(ext)) = context {
			Some(OffchainExt::new(offchain::LimitedExternalities::new(capabilities, ext.0)))
		} else {
			None
		};

		self.executor.contextual_call::<_, fn(_,_) -> _,_,_>(
			|| core_api.initialize_block(at, &self.prepare_environment_block(at)?),
			at,
			function,
			&args,
			changes,
			initialize_block,
			manager,
			native_call,
			offchain_extensions,
			recorder,
			capabilities.has(offchain::Capability::Keystore),
		)
	}

	fn runtime_version_at(&self, at: &BlockId<Block>) -> error::Result<RuntimeVersion> {
		self.runtime_version_at(at)
	}
}

/// NOTE: only use this implementation when you are sure there are NO consensus-level BlockImport
/// objects. Otherwise, importing blocks directly into the client would be bypassing
/// important verification work.
impl<'a, B, E, Block, RA> consensus::BlockImport<Block> for &'a Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Clone + Send + Sync,
	Block: BlockT<Hash=H256>,
{
	type Error = ConsensusError;

	/// Import a checked and validated block. If a justification is provided in
	/// `BlockImportParams` then `finalized` *must* be true.
	///
	/// NOTE: only use this implementation when there are NO consensus-level BlockImport
	/// objects. Otherwise, importing blocks directly into the client would be bypassing
	/// important verification work.
	///
	/// If you are not sure that there are no BlockImport objects provided by the consensus
	/// algorithm, don't use this function.
	fn import_block(
		&mut self,
		import_block: BlockImportParams<Block>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		self.lock_import_and_run(|operation| {
			self.apply_block(operation, import_block, new_cache)
		}).map_err(|e| {
			warn!("Block import error:\n{:?}", e);
			ConsensusError::ClientImport(e.to_string()).into()
		})
	}

	/// Check block preconditions.
	fn check_block(
		&mut self,
		block: BlockCheckParams<Block>,
	) -> Result<ImportResult, Self::Error> {
		let BlockCheckParams { hash, number, parent_hash } = block;

		if let Some(h) = self.fork_blocks.as_ref().and_then(|x| x.get(&number)) {
			if &hash != h  {
				trace!(
					"Rejecting block from known invalid fork. Got {:?}, expected: {:?} at height {}",
					hash,
					h,
					number
				);
				return Ok(ImportResult::KnownBad);
			}
		}

		match self.block_status(&BlockId::Hash(parent_hash))
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
		{
			BlockStatus::InChainWithState | BlockStatus::Queued => {},
			BlockStatus::Unknown | BlockStatus::InChainPruned => return Ok(ImportResult::UnknownParent),
			BlockStatus::KnownBad => return Ok(ImportResult::KnownBad),
		}

		match self.block_status(&BlockId::Hash(hash))
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
		{
			BlockStatus::InChainWithState | BlockStatus::Queued => return Ok(ImportResult::AlreadyInChain),
			BlockStatus::Unknown | BlockStatus::InChainPruned => {},
			BlockStatus::KnownBad => return Ok(ImportResult::KnownBad),
		}


		Ok(ImportResult::imported(false))
	}
}

impl<B, E, Block, RA> consensus::BlockImport<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher> + Clone + Send + Sync,
	Block: BlockT<Hash=H256>,
{
	type Error = ConsensusError;

	fn import_block(
		&mut self,
		import_block: BlockImportParams<Block>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		(&*self).import_block(import_block, new_cache)
	}

	fn check_block(
		&mut self,
		block: BlockCheckParams<Block>,
	) -> Result<ImportResult, Self::Error> {
		(&*self).check_block(block)
	}
}

impl<B, E, Block, RA> Finalizer<Block, Blake2Hasher, B> for Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
	Block: BlockT<Hash=H256>,
{
	fn apply_finality(
		&self,
		operation: &mut ClientImportOperation<Block, Blake2Hasher, B>,
		id: BlockId<Block>,
		justification: Option<Justification>,
		notify: bool,
	) -> error::Result<()> {
		let last_best = self.backend.blockchain().info().best_hash;
		let to_finalize_hash = self.backend.blockchain().expect_block_hash_from_id(&id)?;
		self.apply_finality_with_block_hash(operation, to_finalize_hash, justification, last_best, notify)
	}

	fn finalize_block(&self, id: BlockId<Block>, justification: Option<Justification>, notify: bool) -> error::Result<()> {
		self.lock_import_and_run(|operation| {
			self.apply_finality(operation, id, justification, notify)
		})
	}
}

impl<B, E, Block, RA> Finalizer<Block, Blake2Hasher, B> for &Client<B, E, Block, RA> where
	B: backend::Backend<Block, Blake2Hasher>,
	E: CallExecutor<Block, Blake2Hasher>,
	Block: BlockT<Hash=H256>,
{
	fn apply_finality(
		&self,
		operation: &mut ClientImportOperation<Block, Blake2Hasher, B>,
		id: BlockId<Block>,
		justification: Option<Justification>,
		notify: bool,
	) -> error::Result<()> {
		(**self).apply_finality(operation, id, justification, notify)
	}

	fn finalize_block(&self, id: BlockId<Block>, justification: Option<Justification>, notify: bool) -> error::Result<()> {
		(**self).finalize_block(id, justification, notify)
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
	fn storage_changes_notification_stream(
		&self,
		filter_keys: Option<&[StorageKey]>,
		child_filter_keys: Option<&[(StorageKey, Option<Vec<StorageKey>>)]>,
	) -> error::Result<StorageEventStream<Block::Hash>> {
		Ok(self.storage_notifications.lock().listen(filter_keys, child_filter_keys))
	}
}

/// Implement Longest Chain Select implementation
/// where 'longest' is defined as the highest number of blocks
pub struct LongestChain<B, Block> {
	backend: Arc<B>,
	_phantom: PhantomData<Block>
}

impl<B, Block> Clone for LongestChain<B, Block> {
	fn clone(&self) -> Self {
		let backend = self.backend.clone();
		LongestChain {
			backend,
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
	pub fn new(backend: Arc<B>) -> Self {
		LongestChain {
			backend,
			_phantom: Default::default()
		}
	}

	fn best_block_header(&self) -> error::Result<<Block as BlockT>::Header> {
		let info = self.backend.blockchain().info();
		let import_lock = self.backend.get_import_lock();
		let best_hash = self.backend.blockchain().best_containing(info.best_hash, None, import_lock)?
			.unwrap_or(info.best_hash);

		Ok(self.backend.blockchain().header(BlockId::Hash(best_hash))?
			.expect("given block hash was fetched from block in db; qed"))
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
			.map_err(|e| ConsensusError::ChainLookup(e.to_string()).into())
	}

	fn best_chain(&self)
		-> Result<<Block as BlockT>::Header, ConsensusError>
	{
		LongestChain::best_block_header(&self)
			.map_err(|e| ConsensusError::ChainLookup(e.to_string()).into())
	}

	fn finality_target(
		&self,
		target_hash: Block::Hash,
		maybe_max_number: Option<NumberFor<Block>>
	) -> Result<Option<Block::Hash>, ConsensusError> {
		let import_lock = self.backend.get_import_lock();
		self.backend.blockchain().best_containing(target_hash, maybe_max_number, import_lock)
			.map_err(|e| ConsensusError::ChainLookup(e.to_string()).into())
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
			apply_aux(operation, insert, delete)
		})
	}
	/// Query auxiliary data from key-value store.
	fn get_aux(&self, key: &[u8]) -> error::Result<Option<Vec<u8>>> {
		crate::backend::AuxStore::get_aux(&*self.backend, key)
	}
}


impl<B, E, Block, RA> backend::AuxStore for &Client<B, E, Block, RA>
	where
		B: backend::Backend<Block, Blake2Hasher>,
		E: CallExecutor<Block, Blake2Hasher>,
		Block: BlockT<Hash=H256>,
{

	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
		D: IntoIterator<Item=&'a &'b [u8]>,
	>(&self, insert: I, delete: D) -> error::Result<()> {
		(**self).insert_aux(insert, delete)
	}

	fn get_aux(&self, key: &[u8]) -> error::Result<Option<Vec<u8>>> {
		(**self).get_aux(key)
	}
}

/// Helper function to apply auxiliary data insertion into an operation.
pub fn apply_aux<'a, 'b: 'a, 'c: 'a, B, Block, H, D, I>(
	operation: &mut ClientImportOperation<Block, H, B>,
	insert: I,
	delete: D
) -> error::Result<()>
where
	Block: BlockT,
	H: Hasher<Out=Block::Hash>,
	B: backend::Backend<Block, H>,
	I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
	D: IntoIterator<Item=&'a &'b [u8]>,
{
	operation.op.insert_aux(
		insert.into_iter()
			.map(|(k, v)| (k.to_vec(), Some(v.to_vec())))
			.chain(delete.into_iter().map(|k| (k.to_vec(), None)))
	)
}

/// Utility methods for the client.
pub mod utils {
	use super::*;
	use crate::error;
	use primitives::H256;
	use std::borrow::Borrow;

	/// Returns a function for checking block ancestry, the returned function will
	/// return `true` if the given hash (second parameter) is a descendent of the
	/// base (first parameter). If the `current` parameter is defined, it should
	/// represent the current block `hash` and its `parent hash`, if given the
	/// function that's returned will assume that `hash` isn't part of the local DB
	/// yet, and all searches in the DB will instead reference the parent.
	pub fn is_descendent_of<'a, Block: BlockT<Hash=H256>, T, H: Borrow<H256> + 'a>(
		client: &'a T,
		current: Option<(H, H)>,
	) -> impl Fn(&H256, &H256) -> Result<bool, error::Error> + 'a
		where T: ChainHeaderBackend<Block> + HeaderMetadata<Block, Error=error::Error>,
	{
		move |base, hash| {
			if base == hash { return Ok(false); }

			let current = current.as_ref().map(|(c, p)| (c.borrow(), p.borrow()));

			let mut hash = hash;
			if let Some((current_hash, current_parent_hash)) = current {
				if base == current_hash { return Ok(false); }
				if hash == current_hash {
					if base == current_parent_hash {
						return Ok(true);
					} else {
						hash = current_parent_hash;
					}
				}
			}

			let ancestor = header_metadata::lowest_common_ancestor(client, *hash, *base)?;

			Ok(ancestor.hash == *base)
		}
	}
}

impl<BE, E, B, RA> consensus::block_validation::Chain<B> for Client<BE, E, B, RA>
	where BE: backend::Backend<B, Blake2Hasher>,
		  E: CallExecutor<B, Blake2Hasher>,
		  B: BlockT<Hash = H256>
{
	fn block_status(&self, id: &BlockId<B>) -> Result<BlockStatus, Box<dyn std::error::Error + Send>> {
		Client::block_status(self, id).map_err(|e| Box::new(e) as Box<_>)
	}
}

#[cfg(test)]
pub(crate) mod tests {
	use std::collections::HashMap;
	use super::*;
	use primitives::blake2_256;
	use sr_primitives::DigestItem;
	use consensus::{BlockOrigin, SelectChain};
	use test_client::{
		prelude::*,
		client_db::{Backend, DatabaseSettings, DatabaseSettingsSrc, PruningMode},
		runtime::{self, Block, Transfer, RuntimeApi, TestAPI},
	};

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
		let remote_client = TestClientBuilder::new().set_support_changes_trie(true).build();
		let mut nonces: HashMap<_, u64> = Default::default();
		for (i, block_transfers) in blocks_transfers.into_iter().enumerate() {
			let mut builder = remote_client.new_block(Default::default()).unwrap();
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
				&BlockId::Number(client.info().chain.best_number),
				AccountKeyring::Alice.into()
			).unwrap(),
			1000
		);
		assert_eq!(
			client.runtime_api().balance_of(
				&BlockId::Number(client.info().chain.best_number),
				AccountKeyring::Ferdie.into()
			).unwrap(),
			0
		);
	}

	#[test]
	fn block_builder_works_with_no_transactions() {
		let client = test_client::new();

		let builder = client.new_block(Default::default()).unwrap();

		client.import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();

		assert_eq!(client.info().chain.best_number, 1);
	}

	#[test]
	fn block_builder_works_with_transactions() {
		let client = test_client::new();

		let mut builder = client.new_block(Default::default()).unwrap();

		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 42,
			nonce: 0,
		}).unwrap();

		client.import(BlockOrigin::Own, builder.bake().unwrap()).unwrap();

		assert_eq!(client.info().chain.best_number, 1);
		assert_ne!(
			client.state_at(&BlockId::Number(1)).unwrap().pairs(),
			client.state_at(&BlockId::Number(0)).unwrap().pairs()
		);
		assert_eq!(
			client.runtime_api().balance_of(
				&BlockId::Number(client.info().chain.best_number),
				AccountKeyring::Alice.into()
			).unwrap(),
			958
		);
		assert_eq!(
			client.runtime_api().balance_of(
				&BlockId::Number(client.info().chain.best_number),
				AccountKeyring::Ferdie.into()
			).unwrap(),
			42
		);
	}

	#[test]
	fn block_builder_does_not_include_invalid() {
		let client = test_client::new();

		let mut builder = client.new_block(Default::default()).unwrap();

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

		assert_eq!(client.info().chain.best_number, 1);
		assert_ne!(
			client.state_at(&BlockId::Number(1)).unwrap().pairs(),
			client.state_at(&BlockId::Number(0)).unwrap().pairs()
		);
		assert_eq!(client.body(&BlockId::Number(1)).unwrap().unwrap().len(), 1)
	}

	#[test]
	fn best_containing_with_genesis_block() {
		// block tree:
		// G

		let (client, longest_chain_select) = TestClientBuilder::new().build_with_longest_chain();

		let genesis_hash = client.info().chain.genesis_hash;

		assert_eq!(
			genesis_hash.clone(),
			longest_chain_select.finality_target(genesis_hash.clone(), None).unwrap().unwrap()
		);
	}

	#[test]
	fn best_containing_with_hash_not_found() {
		// block tree:
		// G

		let (client, longest_chain_select) = TestClientBuilder::new().build_with_longest_chain();

		let uninserted_block = client.new_block(Default::default()).unwrap().bake().unwrap();

		assert_eq!(
			None,
			longest_chain_select.finality_target(uninserted_block.hash().clone(), None).unwrap()
		);
	}

	#[test]
	fn uncles_with_only_ancestors() {
		// block tree:
		// G -> A1 -> A2
		let client = test_client::new();

		// G -> A1
		let a1 = client.new_block(Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block(Default::default()).unwrap().bake().unwrap();
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
		let a1 = client.new_block(Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block_at(&BlockId::Hash(a1.hash()), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		// A2 -> A3
		let a3 = client.new_block_at(&BlockId::Hash(a2.hash()), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a3.clone()).unwrap();

		// A3 -> A4
		let a4 = client.new_block_at(&BlockId::Hash(a3.hash()), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a4.clone()).unwrap();

		// A4 -> A5
		let a5 = client.new_block_at(&BlockId::Hash(a4.hash()), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a5.clone()).unwrap();

		// A1 -> B2
		let mut builder = client.new_block_at(&BlockId::Hash(a1.hash()), Default::default()).unwrap();
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
		let b3 = client.new_block_at(&BlockId::Hash(b2.hash()), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, b3.clone()).unwrap();

		// B3 -> B4
		let b4 = client.new_block_at(&BlockId::Hash(b3.hash()), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, b4.clone()).unwrap();

		// // B2 -> C3
		let mut builder = client.new_block_at(&BlockId::Hash(b2.hash()), Default::default()).unwrap();
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
		let mut builder = client.new_block_at(&BlockId::Hash(a1.hash()), Default::default()).unwrap();
		// this push is required as otherwise D2 has the same hash as B2 and won't get imported
		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 0,
		}).unwrap();
		let d2 = builder.bake().unwrap();
		client.import(BlockOrigin::Own, d2.clone()).unwrap();

		let genesis_hash = client.info().chain.genesis_hash;

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

		let (client, longest_chain_select) = TestClientBuilder::new().build_with_longest_chain();

		// G -> A1
		let a1 = client.new_block(Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block(Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		let genesis_hash = client.info().chain.genesis_hash;

		assert_eq!(a2.hash(), longest_chain_select.finality_target(genesis_hash, None).unwrap().unwrap());
		assert_eq!(a2.hash(), longest_chain_select.finality_target(a1.hash(), None).unwrap().unwrap());
		assert_eq!(a2.hash(), longest_chain_select.finality_target(a2.hash(), None).unwrap().unwrap());
	}

	#[test]
	fn best_containing_on_longest_chain_with_multiple_forks() {
		// block tree:
		// G -> A1 -> A2 -> A3 -> A4 -> A5
		//      A1 -> B2 -> B3 -> B4
		//	          B2 -> C3
		//	    A1 -> D2
		let (client, longest_chain_select) = TestClientBuilder::new().build_with_longest_chain();

		// G -> A1
		let a1 = client.new_block(Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block_at(&BlockId::Hash(a1.hash()), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		// A2 -> A3
		let a3 = client.new_block_at(&BlockId::Hash(a2.hash()), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a3.clone()).unwrap();

		// A3 -> A4
		let a4 = client.new_block_at(&BlockId::Hash(a3.hash()), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a4.clone()).unwrap();

		// A4 -> A5
		let a5 = client.new_block_at(&BlockId::Hash(a4.hash()), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a5.clone()).unwrap();

		// A1 -> B2
		let mut builder = client.new_block_at(&BlockId::Hash(a1.hash()), Default::default()).unwrap();
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
		let b3 = client.new_block_at(&BlockId::Hash(b2.hash()), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, b3.clone()).unwrap();

		// B3 -> B4
		let b4 = client.new_block_at(&BlockId::Hash(b3.hash()), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, b4.clone()).unwrap();

		// // B2 -> C3
		let mut builder = client.new_block_at(&BlockId::Hash(b2.hash()), Default::default()).unwrap();
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
		let mut builder = client.new_block_at(&BlockId::Hash(a1.hash()), Default::default()).unwrap();
		// this push is required as otherwise D2 has the same hash as B2 and won't get imported
		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 0,
		}).unwrap();
		let d2 = builder.bake().unwrap();
		client.import(BlockOrigin::Own, d2.clone()).unwrap();

		assert_eq!(client.info().chain.best_hash, a5.hash());

		let genesis_hash = client.info().chain.genesis_hash;
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

		let (client, longest_chain_select) = TestClientBuilder::new().build_with_longest_chain();

		// G -> A1
		let a1 = client.new_block(Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block(Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		let genesis_hash = client.info().chain.genesis_hash;

		assert_eq!(a2.hash(), longest_chain_select.finality_target(genesis_hash, Some(10)).unwrap().unwrap());
	}

	#[test]
	fn key_changes_works() {
		let (client, _, test_cases) = prepare_client_with_key_changes();

		for (index, (begin, end, key, expected_result)) in test_cases.into_iter().enumerate() {
			let end = client.block_hash(end).unwrap().unwrap();
			let actual_result = client.key_changes(
				begin,
				BlockId::Hash(end),
				None,
				&StorageKey(key),
			).unwrap();
			match actual_result == expected_result {
				true => (),
				false => panic!(format!("Failed test {}: actual = {:?}, expected = {:?}",
					index, actual_result, expected_result)),
			}
		}
	}

	#[test]
	fn import_with_justification() {
		let client = test_client::new();

		// G -> A1
		let a1 = client.new_block(Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block_at(&BlockId::Hash(a1.hash()), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		// A2 -> A3
		let justification = vec![1, 2, 3];
		let a3 = client.new_block_at(&BlockId::Hash(a2.hash()), Default::default()).unwrap().bake().unwrap();
		client.import_justified(BlockOrigin::Own, a3.clone(), justification.clone()).unwrap();

		assert_eq!(
			client.info().chain.finalized_hash,
			a3.hash(),
		);

		assert_eq!(
			client.justification(&BlockId::Hash(a3.hash())).unwrap(),
			Some(justification),
		);

		assert_eq!(
			client.justification(&BlockId::Hash(a1.hash())).unwrap(),
			None,
		);

		assert_eq!(
			client.justification(&BlockId::Hash(a2.hash())).unwrap(),
			None,
		);
	}

	#[test]
	fn importing_diverged_finalized_block_should_trigger_reorg() {

		let client = test_client::new();

		// G -> A1 -> A2
		//   \
		//    -> B1
		let a1 = client.new_block_at(&BlockId::Number(0), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		let a2 = client.new_block_at(&BlockId::Hash(a1.hash()), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		let mut b1 = client.new_block_at(&BlockId::Number(0), Default::default()).unwrap();
		// needed to make sure B1 gets a different hash from A1
		b1.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 0,
		}).unwrap();
		// create but don't import B1 just yet
		let b1 = b1.bake().unwrap();

		// A2 is the current best since it's the longest chain
		assert_eq!(
			client.info().chain.best_hash,
			a2.hash(),
		);

		// importing B1 as finalized should trigger a re-org and set it as new best
		let justification = vec![1, 2, 3];
		client.import_justified(BlockOrigin::Own, b1.clone(), justification).unwrap();

		assert_eq!(
			client.info().chain.best_hash,
			b1.hash(),
		);

		assert_eq!(
			client.info().chain.finalized_hash,
			b1.hash(),
		);
	}

	#[test]
	fn finalizing_diverged_block_should_trigger_reorg() {

		let (client, select_chain) = TestClientBuilder::new().build_with_longest_chain();

		// G -> A1 -> A2
		//   \
		//    -> B1 -> B2
		let a1 = client.new_block_at(&BlockId::Number(0), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		let a2 = client.new_block_at(&BlockId::Hash(a1.hash()), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		let mut b1 = client.new_block_at(&BlockId::Number(0), Default::default()).unwrap();
		// needed to make sure B1 gets a different hash from A1
		b1.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 0,
		}).unwrap();
		let b1 = b1.bake().unwrap();
		client.import(BlockOrigin::Own, b1.clone()).unwrap();

		let b2 = client.new_block_at(&BlockId::Hash(b1.hash()), Default::default()).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, b2.clone()).unwrap();

		// A2 is the current best since it's the longest chain
		assert_eq!(
			client.info().chain.best_hash,
			a2.hash(),
		);

		// we finalize block B1 which is on a different branch from current best
		// which should trigger a re-org.
		client.finalize_block(BlockId::Hash(b1.hash()), None).unwrap();

		// B1 should now be the latest finalized
		assert_eq!(
			client.info().chain.finalized_hash,
			b1.hash(),
		);

		// and B1 should be the new best block (`finalize_block` as no way of
		// knowing about B2)
		assert_eq!(
			client.info().chain.best_hash,
			b1.hash(),
		);

		// `SelectChain` should report B2 as best block though
		assert_eq!(
			select_chain.best_chain().unwrap().hash(),
			b2.hash(),
		);

		// after we build B3 on top of B2 and import it
		// it should be the new best block,
		let b3 = client.new_block_at(
			&BlockId::Hash(b2.hash()),
			Default::default(),
		).unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, b3.clone()).unwrap();

		assert_eq!(
			client.info().chain.best_hash,
			b3.hash(),
		);
	}

	#[test]
	fn get_header_by_block_number_doesnt_panic() {
		let client = test_client::new();

		// backend uses u32 for block numbers, make sure we don't panic when
		// trying to convert
		let id = BlockId::<Block>::Number(72340207214430721);
		client.header(&id).expect_err("invalid block number overflows u32");
	}

	#[test]
	fn state_reverted_on_reorg() {
		let _ = env_logger::try_init();
		let client = test_client::new();

		let current_balance = ||
			client.runtime_api().balance_of(
				&BlockId::number(client.info().chain.best_number), AccountKeyring::Alice.into()
			).unwrap();

		// G -> A1 -> A2
		//   \
		//    -> B1
		let mut a1 = client.new_block_at(&BlockId::Number(0), Default::default()).unwrap();
		a1.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Bob.into(),
			amount: 10,
			nonce: 0,
		}).unwrap();
		let a1 = a1.bake().unwrap();
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		let mut b1 = client.new_block_at(&BlockId::Number(0), Default::default()).unwrap();
		b1.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 50,
			nonce: 0,
		}).unwrap();
		let b1 = b1.bake().unwrap();
		// Reorg to B1
		client.import_as_best(BlockOrigin::Own, b1.clone()).unwrap();

		assert_eq!(950, current_balance());
		let mut a2 = client.new_block_at(&BlockId::Hash(a1.hash()), Default::default()).unwrap();
		a2.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Charlie.into(),
			amount: 10,
			nonce: 1,
		}).unwrap();
		// Re-org to A2
		client.import_as_best(BlockOrigin::Own, a2.bake().unwrap()).unwrap();
		assert_eq!(980, current_balance());
	}

	#[test]
	fn doesnt_import_blocks_that_revert_finality() {
		let _ = env_logger::try_init();
		let tmp = tempfile::tempdir().unwrap();

		// we need to run with archive pruning to avoid pruning non-canonical
		// states
		let backend = Arc::new(Backend::new(
			DatabaseSettings {
				state_cache_size: 1 << 20,
				state_cache_child_ratio: None,
				pruning: PruningMode::ArchiveAll,
				source: DatabaseSettingsSrc::Path {
					path: tmp.path().into(),
					cache_size: None,
				}
			},
			u64::max_value(),
		).unwrap());

		let client = TestClientBuilder::with_backend(backend).build();

		//    -> C1
		//   /
		// G -> A1 -> A2
		//   \
		//    -> B1 -> B2 -> B3

		let a1 = client.new_block_at(&BlockId::Number(0), Default::default())
			.unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		let a2 = client.new_block_at(&BlockId::Hash(a1.hash()), Default::default())
			.unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		let mut b1 = client.new_block_at(&BlockId::Number(0), Default::default()).unwrap();

		// needed to make sure B1 gets a different hash from A1
		b1.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 0,
		}).unwrap();
		let b1 = b1.bake().unwrap();
		client.import(BlockOrigin::Own, b1.clone()).unwrap();

		let b2 = client.new_block_at(&BlockId::Hash(b1.hash()), Default::default())
			.unwrap().bake().unwrap();
		client.import(BlockOrigin::Own, b2.clone()).unwrap();

		// we will finalize A2 which should make it impossible to import a new
		// B3 at the same height but that doesnt't include it
		client.finalize_block(BlockId::Hash(a2.hash()), None).unwrap();

		let b3 = client.new_block_at(&BlockId::Hash(b2.hash()), Default::default())
			.unwrap().bake().unwrap();

		let import_err = client.import(BlockOrigin::Own, b3).err().unwrap();
		let expected_err = ConsensusError::ClientImport(
			error::Error::NotInFinalizedChain.to_string()
		);

		assert_eq!(
			import_err.to_string(),
			expected_err.to_string(),
		);

		// adding a C1 block which is lower than the last finalized should also
		// fail (with a cheaper check that doesn't require checking ancestry).
		let mut c1 = client.new_block_at(&BlockId::Number(0), Default::default()).unwrap();

		// needed to make sure C1 gets a different hash from A1 and B1
		c1.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 2,
			nonce: 0,
		}).unwrap();
		let c1 = c1.bake().unwrap();

		let import_err = client.import(BlockOrigin::Own, c1).err().unwrap();
		let expected_err = ConsensusError::ClientImport(
			error::Error::NotInFinalizedChain.to_string()
		);

		assert_eq!(
			import_err.to_string(),
			expected_err.to_string(),
		);
	}
}
