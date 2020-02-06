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

//! Substrate Client

use std::{
	marker::PhantomData, collections::{HashSet, BTreeMap, HashMap}, sync::Arc, panic::UnwindSafe,
	result,
};
use log::{info, trace, warn};
use futures::channel::mpsc;
use parking_lot::{Mutex, RwLock};
use codec::{Encode, Decode};
use hash_db::Prefix;
use sp_core::{
	ChangesTrieConfiguration, convert_hash, traits::CodeExecutor,
	NativeOrEncoded, storage::{StorageKey, StorageData, well_known_keys, ChildInfo},
};
use sc_telemetry::{telemetry, SUBSTRATE_INFO};
use sp_runtime::{
	Justification, BuildStorage,
	generic::{BlockId, SignedBlock, DigestItem},
	traits::{
		Block as BlockT, Header as HeaderT, Zero, NumberFor, HasherFor, SaturatedConversion, One,
		DigestFor,
	},
};
use sp_state_machine::{
	DBValue, Backend as StateBackend, ChangesTrieAnchorBlockId,
	prove_read, prove_child_read, ChangesTrieRootsStorage, ChangesTrieStorage,
	ChangesTrieConfigurationRange, key_changes, key_changes_proof, StorageProof,
	merge_storage_proofs,
};
use sc_executor::{RuntimeVersion, RuntimeInfo};
use sp_consensus::{
	Error as ConsensusError, BlockStatus, BlockImportParams, BlockCheckParams, ImportResult,
	BlockOrigin, ForkChoiceStrategy, SelectChain, RecordProof,
};
use sp_blockchain::{self as blockchain,
	Backend as ChainBackend,
	HeaderBackend as ChainHeaderBackend, ProvideCache, Cache,
	well_known_cache_keys::Id as CacheKeyId,
	HeaderMetadata, CachedHeaderMetadata,
};

use sp_api::{
	CallApiAt, ConstructRuntimeApi, Core as CoreApi, ApiExt, ApiRef, ProvideRuntimeApi,
	CallApiAtParams,
};
use sc_block_builder::BlockBuilderApi;

pub use sc_client_api::{
	backend::{
		self, BlockImportOperation, PrunableStateChangesTrieStorage,
		ClientImportOperation, Finalizer, ImportSummary, NewBlockState,
		changes_tries_state_at_block,
	},
	client::{
		ImportNotifications, FinalityNotification, FinalityNotifications, BlockImportNotification,
		ClientInfo, BlockchainEvents, BlockBody, ProvideUncles, BadBlocks, ForkBlocks,
		BlockOf,
	},
	execution_extensions::{ExecutionExtensions, ExecutionStrategies},
	notifications::{StorageNotifications, StorageEventStream},
	CallExecutor,
};
use sp_blockchain::Error;

use crate::{
	call_executor::LocalCallExecutor,
	light::{call_executor::prove_execution, fetcher::ChangesProof},
	in_mem, genesis, cht, block_rules::{BlockRules, LookupResult as BlockLookupResult},
};

/// Substrate Client
pub struct Client<B, E, Block, RA> where Block: BlockT {
	backend: Arc<B>,
	executor: E,
	storage_notifications: Mutex<StorageNotifications<Block>>,
	import_notification_sinks: Mutex<Vec<mpsc::UnboundedSender<BlockImportNotification<Block>>>>,
	finality_notification_sinks: Mutex<Vec<mpsc::UnboundedSender<FinalityNotification<Block>>>>,
	// holds the block hash currently being imported. TODO: replace this with block queue
	importing_block: RwLock<Option<Block::Hash>>,
	block_rules: BlockRules<Block>,
	execution_extensions: ExecutionExtensions<Block>,
	_phantom: PhantomData<RA>,
}

/// An `Iterator` that iterates keys in a given block under a prefix.
pub struct KeyIterator<'a, State, Block> {
	state: State,
	prefix: Option<&'a StorageKey>,
	current_key: Vec<u8>,
	_phantom: PhantomData<Block>,
}

impl <'a, State, Block> KeyIterator<'a, State, Block> {
	fn new(state: State, prefix: Option<&'a StorageKey>, current_key: Vec<u8>) -> Self {
		Self {
			state,
			prefix,
			current_key,
			_phantom: PhantomData,
		}
	}
}

impl<'a, State, Block> Iterator for KeyIterator<'a, State, Block> where
	Block: BlockT,
	State: StateBackend<HasherFor<Block>>,
{
	type Item = StorageKey;

	fn next(&mut self) -> Option<Self::Item> {
		let next_key = self.state
			.next_storage_key(&self.current_key)
			.ok()
			.flatten()?;
		if let Some(prefix) = self.prefix {
			if !next_key.starts_with(&prefix.0[..]) {
				return None;
			}
		}
		self.current_key = next_key.clone();
		Some(StorageKey(next_key))
	}
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
	genesis_storage: &S,
	keystore: Option<sp_core::traits::BareCryptoStorePtr>,
) -> sp_blockchain::Result<Client<
	in_mem::Backend<Block>,
	LocalCallExecutor<in_mem::Backend<Block>, E>,
	Block,
	RA
>> where
	E: CodeExecutor + RuntimeInfo,
	S: BuildStorage,
	Block: BlockT,
{
	new_with_backend(Arc::new(in_mem::Backend::new()), executor, genesis_storage, keystore)
}

/// Create a client with the explicitly provided backend.
/// This is useful for testing backend implementations.
pub fn new_with_backend<B, E, Block, S, RA>(
	backend: Arc<B>,
	executor: E,
	build_genesis_storage: &S,
	keystore: Option<sp_core::traits::BareCryptoStorePtr>,
) -> sp_blockchain::Result<Client<B, LocalCallExecutor<B, E>, Block, RA>>
	where
		E: CodeExecutor + RuntimeInfo,
		S: BuildStorage,
		Block: BlockT,
		B: backend::LocalBackend<Block> + 'static,
{
	let call_executor = LocalCallExecutor::new(backend.clone(), executor);
	let extensions = ExecutionExtensions::new(Default::default(), keystore);
	Client::new(
		backend,
		call_executor,
		build_genesis_storage,
		Default::default(),
		Default::default(),
		extensions,
	)
}

impl<B, E, Block, RA> BlockOf for Client<B, E, Block, RA> where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	type Type = Block;
}

impl<B, E, Block, RA> Client<B, E, Block, RA> where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	/// Creates new Substrate Client with given blockchain and code executor.
	pub fn new<S: BuildStorage>(
		backend: Arc<B>,
		executor: E,
		build_genesis_storage: &S,
		fork_blocks: ForkBlocks<Block>,
		bad_blocks: BadBlocks<Block>,
		execution_extensions: ExecutionExtensions<Block>,
	) -> sp_blockchain::Result<Self> {
		if backend.blockchain().header(BlockId::Number(Zero::zero()))?.is_none() {
			let genesis_storage = build_genesis_storage.build_storage()?;
			let mut op = backend.begin_operation()?;
			backend.begin_state_operation(&mut op, BlockId::Hash(Default::default()))?;
			let state_root = op.reset_storage(genesis_storage)?;
			let genesis_block = genesis::construct_genesis_block::<Block>(state_root.into());
			info!("Initializing Genesis block/state (state: {}, header-hash: {})",
				genesis_block.header().state_root(),
				genesis_block.header().hash()
			);
			op.set_block_data(
				genesis_block.deconstruct().0,
				Some(vec![]),
				None,
				NewBlockState::Final
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
			block_rules: BlockRules::new(fork_blocks, bad_blocks),
			execution_extensions,
			_phantom: Default::default(),
		})
	}

	/// Get a reference to the execution extensions.
	pub fn execution_extensions(&self) -> &ExecutionExtensions<Block> {
		&self.execution_extensions
	}

	/// Get a reference to the state at a given block.
	pub fn state_at(&self, block: &BlockId<Block>) -> sp_blockchain::Result<B::State> {
		self.backend.state_at(*block)
	}

	/// Given a `BlockId` and a key prefix, return the matching storage keys in that block.
	pub fn storage_keys(&self, id: &BlockId<Block>, key_prefix: &StorageKey) -> sp_blockchain::Result<Vec<StorageKey>> {
		let keys = self.state_at(id)?.keys(&key_prefix.0).into_iter().map(StorageKey).collect();
		Ok(keys)
	}

	/// Given a `BlockId` and a key prefix, return the matching child storage keys and values in that block.
	pub fn storage_pairs(&self, id: &BlockId<Block>, key_prefix: &StorageKey)
		-> sp_blockchain::Result<Vec<(StorageKey, StorageData)>>
	{
		let state = self.state_at(id)?;
		let keys = state
			.keys(&key_prefix.0)
			.into_iter()
			.map(|k| {
				let d = state.storage(&k).ok().flatten().unwrap_or_default();
				(StorageKey(k), StorageData(d))
			})
			.collect();
		Ok(keys)
	}

	/// Given a `BlockId` and a key prefix, return a `KeyIterator` iterates matching storage keys in that block.
	pub fn storage_keys_iter<'a>(
		&self,
		id: &BlockId<Block>,
		prefix: Option<&'a StorageKey>,
		start_key: Option<&StorageKey>
	) -> sp_blockchain::Result<KeyIterator<'a, B::State, Block>> {
		let state = self.state_at(id)?;
		let start_key = start_key
			.or(prefix)
			.map(|key| key.0.clone())
			.unwrap_or_else(Vec::new);
		Ok(KeyIterator::new(state, prefix, start_key))
	}

	/// Given a `BlockId` and a key, return the value under the key in that block.
	pub fn storage(&self, id: &BlockId<Block>, key: &StorageKey)
		-> sp_blockchain::Result<Option<StorageData>>
	{
		Ok(self.state_at(id)?
			.storage(&key.0).map_err(|e| sp_blockchain::Error::from_state(Box::new(e)))?
			.map(StorageData)
		)
	}

	/// Given a `BlockId` and a key, return the value under the hash in that block.
	pub fn storage_hash(&self, id: &BlockId<Block>, key: &StorageKey)
		-> sp_blockchain::Result<Option<Block::Hash>>
	{
		Ok(self.state_at(id)?
			.storage_hash(&key.0).map_err(|e| sp_blockchain::Error::from_state(Box::new(e)))?
		)
	}

	/// Given a `BlockId`, a key prefix, and a child storage key, return the matching child storage keys.
	pub fn child_storage_keys(
		&self,
		id: &BlockId<Block>,
		child_storage_key: &StorageKey,
		child_info: ChildInfo,
		key_prefix: &StorageKey
	) -> sp_blockchain::Result<Vec<StorageKey>> {
		let keys = self.state_at(id)?
			.child_keys(&child_storage_key.0, child_info, &key_prefix.0)
			.into_iter()
			.map(StorageKey)
			.collect();
		Ok(keys)
	}

	/// Given a `BlockId`, a key and a child storage key, return the value under the key in that block.
	pub fn child_storage(
		&self,
		id: &BlockId<Block>,
		storage_key: &StorageKey,
		child_info: ChildInfo,
		key: &StorageKey
	) -> sp_blockchain::Result<Option<StorageData>> {
		Ok(self.state_at(id)?
			.child_storage(&storage_key.0, child_info, &key.0)
			.map_err(|e| sp_blockchain::Error::from_state(Box::new(e)))?
			.map(StorageData))
	}

	/// Given a `BlockId`, a key and a child storage key, return the hash under the key in that block.
	pub fn child_storage_hash(
		&self,
		id: &BlockId<Block>,
		storage_key: &StorageKey,
		child_info: ChildInfo,
		key: &StorageKey
	) -> sp_blockchain::Result<Option<Block::Hash>> {
		Ok(self.state_at(id)?
			.child_storage_hash(&storage_key.0, child_info, &key.0)
			.map_err(|e| sp_blockchain::Error::from_state(Box::new(e)))?
		)
	}

	/// Get the code at a given block.
	pub fn code_at(&self, id: &BlockId<Block>) -> sp_blockchain::Result<Vec<u8>> {
		Ok(self.storage(id, &StorageKey(well_known_keys::CODE.to_vec()))?
			.expect("None is returned if there's no value stored for the given key;\
				':code' key is always defined; qed").0)
	}

	/// Get the RuntimeVersion at a given block.
	pub fn runtime_version_at(&self, id: &BlockId<Block>) -> sp_blockchain::Result<RuntimeVersion> {
		self.executor.runtime_version(id)
	}

	/// Get call executor reference.
	pub fn executor(&self) -> &E {
		&self.executor
	}

	/// Reads storage value at a given block + key, returning read proof.
	pub fn read_proof<I>(&self, id: &BlockId<Block>, keys: I) -> sp_blockchain::Result<StorageProof> where
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
		child_info: ChildInfo,
		keys: I,
	) -> sp_blockchain::Result<StorageProof> where
		I: IntoIterator,
		I::Item: AsRef<[u8]>,
	{
		self.state_at(id)
			.and_then(|state| prove_child_read(state, storage_key, child_info, keys)
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
	) -> sp_blockchain::Result<(Vec<u8>, StorageProof)> {
		let state = self.state_at(id)?;
		let header = self.prepare_environment_block(id)?;
		prove_execution(state, header, &self.executor, method, call_data)
	}

	/// Reads given header and generates CHT-based header proof.
	pub fn header_proof(&self, id: &BlockId<Block>) -> sp_blockchain::Result<(Block::Header, StorageProof)> {
		self.header_proof_with_cht_size(id, cht::size())
	}

	/// Get block hash by number.
	pub fn block_hash(&self,
		block_number: <<Block as BlockT>::Header as HeaderT>::Number
	) -> sp_blockchain::Result<Option<Block::Hash>> {
		self.backend.blockchain().hash(block_number)
	}

	/// Reads given header and generates CHT-based header proof for CHT of given size.
	pub fn header_proof_with_cht_size(
		&self,
		id: &BlockId<Block>,
		cht_size: NumberFor<Block>,
	) -> sp_blockchain::Result<(Block::Header, StorageProof)> {
		let proof_error = || sp_blockchain::Error::Backend(format!("Failed to generate header proof for {:?}", id));
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
		let proof = cht::build_proof::<Block::Header, HasherFor<Block>, _, _>(
			cht_size,
			cht_num,
			std::iter::once(block_num),
			headers,
		)?;
		Ok((header, proof))
	}

	/// Get longest range within [first; last] that is possible to use in `key_changes`
	/// and `key_changes_proof` calls.
	/// Range could be shortened from the beginning if some changes tries have been pruned.
	/// Returns Ok(None) if changes tries are not supported.
	pub fn max_key_changes_range(
		&self,
		first: NumberFor<Block>,
		last: BlockId<Block>,
	) -> sp_blockchain::Result<Option<(NumberFor<Block>, BlockId<Block>)>> {
		let last_number = self.backend.blockchain().expect_block_number_from_id(&last)?;
		let last_hash = self.backend.blockchain().expect_block_hash_from_id(&last)?;
		if first > last_number {
			return Err(sp_blockchain::Error::ChangesTrieAccessFailed("Invalid changes trie range".into()));
		}

		let (storage, configs) = match self.require_changes_trie(first, last_hash, false).ok() {
			Some((storage, configs)) => (storage, configs),
			None => return Ok(None),
		};

		let first_available_changes_trie = configs.last().map(|config| config.0);
		match first_available_changes_trie {
			Some(first_available_changes_trie) => {
				let oldest_unpruned = storage.oldest_pruned_digest_range_end();
				let first = std::cmp::max(first_available_changes_trie, oldest_unpruned);
				Ok(Some((first, last)))
			},
			None => Ok(None)
		}
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
	) -> sp_blockchain::Result<Vec<(NumberFor<Block>, u32)>> {
		let last_number = self.backend.blockchain().expect_block_number_from_id(&last)?;
		let last_hash = self.backend.blockchain().expect_block_hash_from_id(&last)?;
		let (storage, configs) = self.require_changes_trie(first, last_hash, true)?;

		let mut result = Vec::new();
		let best_number = self.backend.blockchain().info().best_number;
		for (config_zero, config_end, config) in configs {
			let range_first = ::std::cmp::max(first, config_zero + One::one());
			let range_anchor = match config_end {
				Some((config_end_number, config_end_hash)) => if last_number > config_end_number {
					ChangesTrieAnchorBlockId { hash: config_end_hash, number: config_end_number }
				} else {
					ChangesTrieAnchorBlockId { hash: convert_hash(&last_hash), number: last_number }
				},
				None => ChangesTrieAnchorBlockId { hash: convert_hash(&last_hash), number: last_number },
			};

			let config_range = ChangesTrieConfigurationRange {
				config: &config,
				zero: config_zero.clone(),
				end: config_end.map(|(config_end_number, _)| config_end_number),
			};
			let result_range: Vec<(NumberFor<Block>, u32)> = key_changes::<HasherFor<Block>, _>(
				config_range,
				storage.storage(),
				range_first,
				&range_anchor,
				best_number,
				storage_key.as_ref().map(|x| &x.0[..]),
				&key.0)
			.and_then(|r| r.map(|r| r.map(|(block, tx)| (block, tx))).collect::<Result<_, _>>())
			.map_err(|err| sp_blockchain::Error::ChangesTrieAccessFailed(err))?;
			result.extend(result_range);
		}

		Ok(result)
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
	) -> sp_blockchain::Result<ChangesProof<Block::Header>> {
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
	) -> sp_blockchain::Result<ChangesProof<Block::Header>> {
		struct AccessedRootsRecorder<'a, Block: BlockT> {
			storage: &'a dyn ChangesTrieStorage<HasherFor<Block>, NumberFor<Block>>,
			min: NumberFor<Block>,
			required_roots_proofs: Mutex<BTreeMap<NumberFor<Block>, Block::Hash>>,
		};

		impl<'a, Block: BlockT> ChangesTrieRootsStorage<HasherFor<Block>, NumberFor<Block>> for
			AccessedRootsRecorder<'a, Block>
		{
			fn build_anchor(&self, hash: Block::Hash)
				-> Result<ChangesTrieAnchorBlockId<Block::Hash, NumberFor<Block>>, String>
			{
				self.storage.build_anchor(hash)
			}

			fn root(
				&self,
				anchor: &ChangesTrieAnchorBlockId<Block::Hash, NumberFor<Block>>,
				block: NumberFor<Block>,
			) -> Result<Option<Block::Hash>, String> {
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

		impl<'a, Block: BlockT> ChangesTrieStorage<HasherFor<Block>, NumberFor<Block>> for
			AccessedRootsRecorder<'a, Block>
		{
			fn as_roots_storage(&self)
				-> &dyn sp_state_machine::ChangesTrieRootsStorage<HasherFor<Block>, NumberFor<Block>>
			{
				self
			}

			fn with_cached_changed_keys(
				&self,
				root: &Block::Hash,
				functor: &mut dyn FnMut(&HashMap<Option<Vec<u8>>, HashSet<Vec<u8>>>),
			) -> bool {
				self.storage.with_cached_changed_keys(root, functor)
			}

			fn get(&self, key: &Block::Hash, prefix: Prefix) -> Result<Option<DBValue>, String> {
				self.storage.get(key, prefix)
			}
		}

		let first_number = self.backend.blockchain()
			.expect_block_number_from_id(&BlockId::Hash(first))?;
		let (storage, configs) = self.require_changes_trie(first_number, last, true)?;
		let min_number = self.backend.blockchain().expect_block_number_from_id(&BlockId::Hash(min))?;

		let recording_storage = AccessedRootsRecorder::<Block> {
			storage: storage.storage(),
			min: min_number,
			required_roots_proofs: Mutex::new(BTreeMap::new()),
		};

		let max_number = std::cmp::min(
			self.backend.blockchain().info().best_number,
			self.backend.blockchain().expect_block_number_from_id(&BlockId::Hash(max))?,
		);

		// fetch key changes proof
		let mut proof = Vec::new();
		for (config_zero, config_end, config) in configs {
			let last_number = self.backend.blockchain()
				.expect_block_number_from_id(&BlockId::Hash(last))?;
			let config_range = ChangesTrieConfigurationRange {
				config: &config,
				zero: config_zero,
				end: config_end.map(|(config_end_number, _)| config_end_number),
			};
			let proof_range = key_changes_proof::<HasherFor<Block>, _>(
				config_range,
				&recording_storage,
				first_number,
				&ChangesTrieAnchorBlockId {
					hash: convert_hash(&last),
					number: last_number,
				},
				max_number,
				storage_key.as_ref().map(|x| &x.0[..]),
				&key.0,
			)
			.map_err(|err| sp_blockchain::Error::ChangesTrieAccessFailed(err))?;
			proof.extend(proof_range);
		}

		// now gather proofs for all changes tries roots that were touched during key_changes_proof
		// execution AND are unknown (i.e. replaced with CHT) to the requester
		let roots = recording_storage.required_roots_proofs.into_inner();
		let roots_proof = self.changes_trie_roots_proof(cht_size, roots.keys().cloned())?;

		Ok(ChangesProof {
			max_block: max_number,
			proof,
			roots: roots.into_iter().map(|(n, h)| (n, convert_hash(&h))).collect(),
			roots_proof,
		})
	}

	/// Generate CHT-based proof for roots of changes tries at given blocks.
	fn changes_trie_roots_proof<I: IntoIterator<Item=NumberFor<Block>>>(
		&self,
		cht_size: NumberFor<Block>,
		blocks: I
	) -> sp_blockchain::Result<StorageProof> {
		// most probably we have touched several changes tries that are parts of the single CHT
		// => GroupBy changes tries by CHT number and then gather proof for the whole group at once
		let mut proofs = Vec::new();

		cht::for_each_cht_group::<Block::Header, _, _, _>(cht_size, blocks, |_, cht_num, cht_blocks| {
			let cht_proof = self.changes_trie_roots_proof_at_cht(cht_size, cht_num, cht_blocks)?;
			proofs.push(cht_proof);
			Ok(())
		}, ())?;

		Ok(merge_storage_proofs(proofs))
	}

	/// Generates CHT-based proof for roots of changes tries at given blocks (that are part of single CHT).
	fn changes_trie_roots_proof_at_cht(
		&self,
		cht_size: NumberFor<Block>,
		cht_num: NumberFor<Block>,
		blocks: Vec<NumberFor<Block>>
	) -> sp_blockchain::Result<StorageProof> {
		let cht_start = cht::start_number(cht_size, cht_num);
		let mut current_num = cht_start;
		let cht_range = ::std::iter::from_fn(|| {
			let old_current_num = current_num;
			current_num = current_num + One::one();
			Some(old_current_num)
		});
		let roots = cht_range
			.map(|num| self.header(&BlockId::Number(num))
			.map(|block|
				block.and_then(|block| block.digest().log(DigestItem::as_changes_trie_root).cloned()))
			);
		let proof = cht::build_proof::<Block::Header, HasherFor<Block>, _, _>(
			cht_size,
			cht_num,
			blocks,
			roots,
		)?;
		Ok(proof)
	}

	/// Returns changes trie storage and all configurations that have been active in the range [first; last].
	///
	/// Configurations are returned in descending order (and obviously never overlap).
	/// If fail_if_disabled is false, returns maximal consequent configurations ranges, starting from last and
	/// stopping on either first, or when CT have been disabled.
	/// If fail_if_disabled is true, fails when there's a subrange where CT have been disabled
	/// inside first..last blocks range.
	fn require_changes_trie(
		&self,
		first: NumberFor<Block>,
		last: Block::Hash,
		fail_if_disabled: bool,
	) -> sp_blockchain::Result<(
		&dyn PrunableStateChangesTrieStorage<Block>,
		Vec<(NumberFor<Block>, Option<(NumberFor<Block>, Block::Hash)>, ChangesTrieConfiguration)>,
	)> {
		let storage = match self.backend.changes_trie_storage() {
			Some(storage) => storage,
			None => return Err(sp_blockchain::Error::ChangesTriesNotSupported),
		};

		let mut configs = Vec::with_capacity(1);
		let mut current = last;
		loop {
			let config_range = storage.configuration_at(&BlockId::Hash(current))?;
			match config_range.config {
				Some(config) => configs.push((config_range.zero.0, config_range.end, config)),
				None if !fail_if_disabled => return Ok((storage, configs)),
				None => return Err(sp_blockchain::Error::ChangesTriesNotSupported),
			}

			if config_range.zero.0 < first {
				break;
			}

			current = *self.backend.blockchain().expect_header(BlockId::Hash(config_range.zero.1))?.parent_hash();
		}

		Ok((storage, configs))
	}

	/// Create a new block, built on the head of the chain.
	pub fn new_block(
		&self,
		inherent_digests: DigestFor<Block>,
	) -> sp_blockchain::Result<sc_block_builder::BlockBuilder<Block, Self, B>> where
		E: Clone + Send + Sync,
		RA: Send + Sync,
		Self: ProvideRuntimeApi<Block>,
		<Self as ProvideRuntimeApi<Block>>::Api: BlockBuilderApi<Block, Error = Error> +
			ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>
	{
		let info = self.chain_info();
		sc_block_builder::BlockBuilder::new(
			self,
			info.best_hash,
			info.best_number,
			RecordProof::No,
			inherent_digests,
			&self.backend,
		)
	}

	/// Create a new block, built on top of `parent`.
	///
	/// When proof recording is enabled, all accessed trie nodes are saved.
	/// These recorded trie nodes can be used by a third party to proof the
	/// output of this block builder without having access to the full storage.
	pub fn new_block_at<R: Into<RecordProof>>(
		&self,
		parent: &BlockId<Block>,
		inherent_digests: DigestFor<Block>,
		record_proof: R,
	) -> sp_blockchain::Result<sc_block_builder::BlockBuilder<Block, Self, B>> where
		E: Clone + Send + Sync,
		RA: Send + Sync,
		Self: ProvideRuntimeApi<Block>,
		<Self as ProvideRuntimeApi<Block>>::Api: BlockBuilderApi<Block, Error = Error> +
			ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>
	{
		sc_block_builder::BlockBuilder::new(
			self,
			self.expect_block_hash_from_id(parent)?,
			self.expect_block_number_from_id(parent)?,
			record_proof.into(),
			inherent_digests,
			&self.backend
		)
	}

	/// Lock the import lock, and run operations inside.
	pub fn lock_import_and_run<R, Err, F>(&self, f: F) -> Result<R, Err> where
		F: FnOnce(&mut ClientImportOperation<Block, B>) -> Result<R, Err>,
		Err: From<sp_blockchain::Error>,
	{
		let inner = || {
			let _import_lock = self.backend.get_import_lock().write();

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
		operation: &mut ClientImportOperation<Block, B>,
		import_block: BlockImportParams<Block, backend::TransactionFor<B, Block>>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> sp_blockchain::Result<ImportResult> where
		Self: ProvideRuntimeApi<Block>,
		<Self as ProvideRuntimeApi<Block>>::Api: CoreApi<Block, Error = Error> +
			ApiExt<Block, StateBackend = B::State>,
	{
		let BlockImportParams {
			origin,
			header,
			justification,
			post_digests,
			body,
			storage_changes,
			finalized,
			auxiliary,
			fork_choice,
			intermediates,
			import_existing,
			..
		} = import_block;

		assert!(justification.is_some() && finalized || justification.is_none());

		if !intermediates.is_empty() {
			return Err(Error::IncompletePipeline)
		}

		let fork_choice = fork_choice.ok_or(Error::IncompletePipeline)?;

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
			storage_changes,
			new_cache,
			finalized,
			auxiliary,
			fork_choice,
			import_existing,
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
		operation: &mut ClientImportOperation<Block, B>,
		origin: BlockOrigin,
		hash: Block::Hash,
		import_headers: PrePostHeader<Block::Header>,
		justification: Option<Justification>,
		body: Option<Vec<Block::Extrinsic>>,
		storage_changes: Option<sp_api::StorageChanges<backend::StateBackendFor<B, Block>, Block>>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
		finalized: bool,
		aux: Vec<(Vec<u8>, Option<Vec<u8>>)>,
		fork_choice: ForkChoiceStrategy,
		import_existing: bool,
	) -> sp_blockchain::Result<ImportResult> where
		Self: ProvideRuntimeApi<Block>,
		<Self as ProvideRuntimeApi<Block>>::Api: CoreApi<Block, Error = Error> +
				ApiExt<Block, StateBackend = B::State>,
	{
		let parent_hash = import_headers.post().parent_hash().clone();
		let status = self.backend.blockchain().status(BlockId::Hash(hash))?;
		match (import_existing, status) {
			(false, blockchain::BlockStatus::InChain) => return Ok(ImportResult::AlreadyInChain),
			(false, blockchain::BlockStatus::Unknown) => {},
			(true, blockchain::BlockStatus::InChain) =>  {},
			(true, blockchain::BlockStatus::Unknown) =>
				return Err(Error::UnknownBlock(format!("{:?}", hash))),
		}

		let info = self.backend.blockchain().info();

		// the block is lower than our last finalized block so it must revert
		// finality, refusing import.
		if *import_headers.post().number() <= info.finalized_number {
			return Err(sp_blockchain::Error::NotInFinalizedChain);
		}

		// this is a fairly arbitrary choice of where to draw the line on making notifications,
		// but the general goal is to only make notifications when we are already fully synced
		// and get a new chain head.
		let make_notifications = match origin {
			BlockOrigin::NetworkBroadcast | BlockOrigin::Own | BlockOrigin::ConsensusBroadcast => true,
			BlockOrigin::Genesis | BlockOrigin::NetworkInitialSync | BlockOrigin::File => false,
		};

		let storage_changes = match storage_changes {
			Some(storage_changes) => {
				self.backend.begin_state_operation(&mut operation.op, BlockId::Hash(parent_hash))?;

				// ensure parent block is finalized to maintain invariant that
				// finality is called sequentially.
				if finalized {
					self.apply_finality_with_block_hash(
						operation,
						parent_hash,
						None,
						info.best_hash,
						make_notifications,
					)?;
				}

				operation.op.update_cache(new_cache);

				let (main_sc, child_sc, tx, _, changes_trie_tx) = storage_changes.into_inner();

				operation.op.update_db_storage(tx)?;
				operation.op.update_storage(main_sc.clone(), child_sc.clone())?;

				if let Some(changes_trie_transaction) = changes_trie_tx {
					operation.op.update_changes_trie(changes_trie_transaction)?;
				}

				Some((main_sc, child_sc))
			},
			None => None,
		};

		let is_new_best = finalized || match fork_choice {
			ForkChoiceStrategy::LongestChain => import_headers.post().number() > &info.best_number,
			ForkChoiceStrategy::Custom(v) => v,
		};

		let leaf_state = if finalized {
			NewBlockState::Final
		} else if is_new_best {
			NewBlockState::Best
		} else {
			NewBlockState::Normal
		};

		let retracted = if is_new_best {
			let route_from_best = sp_blockchain::tree_route(
				self.backend.blockchain(),
				info.best_hash,
				parent_hash,
			)?;
			route_from_best.retracted().iter().rev().map(|e| e.hash.clone()).collect()
		} else {
			Vec::default()
		};

		trace!(
			"Imported {}, (#{}), best={}, origin={:?}",
			hash,
			import_headers.post().number(),
			is_new_best,
			origin,
		);

		operation.op.set_block_data(
			import_headers.post().clone(),
			body,
			justification,
			leaf_state,
		)?;

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

	/// Prepares the storage changes for a block.
	///
	/// It checks if the state should be enacted and if the `import_block` maybe already provides
	/// the required storage changes. If the state should be enacted and the storage changes are not
	/// provided, the block is re-executed to get the storage changes.
	fn prepare_block_storage_changes(
		&self,
		import_block: &mut BlockImportParams<Block, backend::TransactionFor<B, Block>>,
	) -> sp_blockchain::Result<Option<ImportResult>>
		where
			Self: ProvideRuntimeApi<Block>,
			<Self as ProvideRuntimeApi<Block>>::Api: CoreApi<Block, Error = Error> +
				ApiExt<Block, StateBackend = B::State>,
	{
		let parent_hash = import_block.header.parent_hash();
		let at = BlockId::Hash(*parent_hash);
		let enact_state = match self.block_status(&at)? {
			BlockStatus::Unknown => return Ok(Some(ImportResult::UnknownParent)),
			BlockStatus::InChainWithState | BlockStatus::Queued => true,
			BlockStatus::InChainPruned if import_block.allow_missing_state => false,
			BlockStatus::InChainPruned => return Ok(Some(ImportResult::MissingState)),
			BlockStatus::KnownBad => return Ok(Some(ImportResult::KnownBad)),
		};

		match (enact_state, &mut import_block.storage_changes, &mut import_block.body) {
			// We have storage changes and should enact the state, so we don't need to do anything
			// here
			(true, Some(_), _) => {},
			// We should enact state, but don't have any storage changes, so we need to execute the
			// block.
			(true, ref mut storage_changes @ None, Some(ref body)) => {
				let runtime_api = self.runtime_api();

				runtime_api.execute_block(
					&at,
					Block::new(import_block.header.clone(), body.clone()),
				)?;

				let state = self.backend.state_at(at)?;
				let changes_trie_state = changes_tries_state_at_block(
					&at,
					self.backend.changes_trie_storage(),
				)?;

				let gen_storage_changes = runtime_api.into_storage_changes(
					&state,
					changes_trie_state.as_ref(),
					*parent_hash,
				);

				{
					let _lock = self.backend.get_import_lock().read();
					self.backend.destroy_state(state)?;
				}

				// Make sure to consume the error, only after we have destroyed the state.
				let gen_storage_changes = gen_storage_changes?;

				if import_block.header.state_root()
					!= &gen_storage_changes.transaction_storage_root
				{
					return Err(Error::InvalidStateRoot)
				} else {
					**storage_changes = Some(gen_storage_changes);
				}
			},
			// No block body, no storage changes
			(true, None, None) => {},
			// We should not enact the state, so we set the storage changes to `None`.
			(false, changes, _) => {
				changes.take();
			}
		};

		Ok(None)
	}

	fn apply_finality_with_block_hash(
		&self,
		operation: &mut ClientImportOperation<Block, B>,
		block: Block::Hash,
		justification: Option<Justification>,
		best_block: Block::Hash,
		notify: bool,
	) -> sp_blockchain::Result<()> {
		// find tree route from last finalized to given block.
		let last_finalized = self.backend.blockchain().last_finalized()?;

		if block == last_finalized {
			warn!("Possible safety violation: attempted to re-finalize last finalized block {:?} ", last_finalized);
			return Ok(());
		}

		let route_from_finalized = sp_blockchain::tree_route(self.backend.blockchain(), last_finalized, block)?;

		if let Some(retracted) = route_from_finalized.retracted().get(0) {
			warn!("Safety violation: attempted to revert finalized block {:?} which is not in the \
				same chain as last finalized {:?}", retracted, last_finalized);

			return Err(sp_blockchain::Error::NotInFinalizedChain);
		}

		let route_from_best = sp_blockchain::tree_route(self.backend.blockchain(), best_block, block)?;

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
	) -> sp_blockchain::Result<()> {
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

	fn notify_imported(&self, notify_import: ImportSummary<Block>) -> sp_blockchain::Result<()> {
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

	/// Attempts to revert the chain by `n` blocks guaranteeing that no block is
	/// reverted past the last finalized block. Returns the number of blocks
	/// that were successfully reverted.
	pub fn revert(&self, n: NumberFor<Block>) -> sp_blockchain::Result<NumberFor<Block>> {
		Ok(self.backend.revert(n, false)?)
	}

	/// Attempts to revert the chain by `n` blocks disregarding finality. This
	/// method will revert any finalized blocks as requested and can potentially
	/// leave the node in an inconsistent state. Other modules in the system that
	/// persist data and that rely on finality (e.g. consensus parts) will be
	/// unaffected by the revert. Use this method with caution and making sure
	/// that no other data needs to be reverted for consistency aside from the
	/// block data.
	///
	/// Returns the number of blocks that were successfully reverted.
	pub fn unsafe_revert(&self, n: NumberFor<Block>) -> sp_blockchain::Result<NumberFor<Block>> {
		Ok(self.backend.revert(n, true)?)
	}

	/// Get usage info about current client.
	pub fn usage_info(&self) -> ClientInfo<Block> {
		ClientInfo {
			chain: self.chain_info(),
			usage: self.backend.usage_info(),
		}
	}

	/// Get blockchain info.
	pub fn chain_info(&self) -> blockchain::Info<Block> {
		self.backend.blockchain().info()
	}

	/// Get block status.
	pub fn block_status(&self, id: &BlockId<Block>) -> sp_blockchain::Result<BlockStatus> {
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
	pub fn header(&self, id: &BlockId<Block>) -> sp_blockchain::Result<Option<<Block as BlockT>::Header>> {
		self.backend.blockchain().header(*id)
	}

	/// Get block body by id.
	pub fn body(&self, id: &BlockId<Block>) -> sp_blockchain::Result<Option<Vec<<Block as BlockT>::Extrinsic>>> {
		self.backend.blockchain().body(*id)
	}

	/// Get block justification set by id.
	pub fn justification(&self, id: &BlockId<Block>) -> sp_blockchain::Result<Option<Justification>> {
		self.backend.blockchain().justification(*id)
	}

	/// Get full block by id.
	pub fn block(&self, id: &BlockId<Block>)
		-> sp_blockchain::Result<Option<SignedBlock<Block>>>
	{
		Ok(match (self.header(id)?, self.body(id)?, self.justification(id)?) {
			(Some(header), Some(extrinsics), justification) =>
				Some(SignedBlock { block: Block::new(header, extrinsics), justification }),
			_ => None,
		})
	}

	/// Gets the uncles of the block with `target_hash` going back `max_generation` ancestors.
	pub fn uncles(&self, target_hash: Block::Hash, max_generation: NumberFor<Block>) -> sp_blockchain::Result<Vec<Block::Hash>> {
		let load_header = |id: Block::Hash| -> sp_blockchain::Result<Block::Header> {
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

	/// Prepare in-memory header that is used in execution environment.
	fn prepare_environment_block(&self, parent: &BlockId<Block>) -> sp_blockchain::Result<Block::Header> {
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
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	type Error = sp_blockchain::Error;

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
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	fn uncles(&self, target_hash: Block::Hash, max_generation: NumberFor<Block>) -> sp_blockchain::Result<Vec<Block::Header>> {
		Ok(Client::uncles(self, target_hash, max_generation)?
			.into_iter()
			.filter_map(|hash| Client::header(self, &BlockId::Hash(hash)).unwrap_or(None))
			.collect()
		)
	}
}

impl<B, E, Block, RA> ChainHeaderBackend<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block>,
	E: CallExecutor<Block> + Send + Sync,
	Block: BlockT,
	RA: Send + Sync,
{
	fn header(&self, id: BlockId<Block>) -> sp_blockchain::Result<Option<Block::Header>> {
		self.backend.blockchain().header(id)
	}

	fn info(&self) -> blockchain::Info<Block> {
		self.backend.blockchain().info()
	}

	fn status(&self, id: BlockId<Block>) -> sp_blockchain::Result<blockchain::BlockStatus> {
		self.backend.blockchain().status(id)
	}

	fn number(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<<<Block as BlockT>::Header as HeaderT>::Number>> {
		self.backend.blockchain().number(hash)
	}

	fn hash(&self, number: NumberFor<Block>) -> sp_blockchain::Result<Option<Block::Hash>> {
		self.backend.blockchain().hash(number)
	}
}

impl<B, E, Block, RA> sp_runtime::traits::BlockIdTo<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block>,
	E: CallExecutor<Block> + Send + Sync,
	Block: BlockT,
	RA: Send + Sync,
{
	type Error = Error;

	fn to_hash(&self, block_id: &BlockId<Block>) -> sp_blockchain::Result<Option<Block::Hash>> {
		self.block_hash_from_id(block_id)
	}

	fn to_number(&self, block_id: &BlockId<Block>) -> sp_blockchain::Result<Option<NumberFor<Block>>> {
		self.block_number_from_id(block_id)
	}
}

impl<B, E, Block, RA> ChainHeaderBackend<Block> for &Client<B, E, Block, RA> where
	B: backend::Backend<Block>,
	E: CallExecutor<Block> + Send + Sync,
	Block: BlockT,
	RA: Send + Sync,
{
	fn header(&self, id: BlockId<Block>) -> sp_blockchain::Result<Option<Block::Header>> {
		(**self).backend.blockchain().header(id)
	}

	fn info(&self) -> blockchain::Info<Block> {
		(**self).backend.blockchain().info()
	}

	fn status(&self, id: BlockId<Block>) -> sp_blockchain::Result<blockchain::BlockStatus> {
		(**self).status(id)
	}

	fn number(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<<<Block as BlockT>::Header as HeaderT>::Number>> {
		(**self).number(hash)
	}

	fn hash(&self, number: NumberFor<Block>) -> sp_blockchain::Result<Option<Block::Hash>> {
		(**self).hash(number)
	}
}

impl<B, E, Block, RA> ProvideCache<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block>,
	Block: BlockT,
{
	fn cache(&self) -> Option<Arc<dyn Cache<Block>>> {
		self.backend.blockchain().cache()
	}
}

impl<B, E, Block, RA> ProvideRuntimeApi<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block>,
	E: CallExecutor<Block, Backend = B> + Send + Sync,
	Block: BlockT,
	RA: ConstructRuntimeApi<Block, Self>,
{
	type Api = <RA as ConstructRuntimeApi<Block, Self>>::RuntimeApi;

	fn runtime_api<'a>(&'a self) -> ApiRef<'a, Self::Api> {
		RA::construct_runtime_api(self)
	}
}

impl<B, E, Block, RA> CallApiAt<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block>,
	E: CallExecutor<Block, Backend = B> + Send + Sync,
	Block: BlockT,
{
	type Error = Error;
	type StateBackend = B::State;

	fn call_api_at<
		'a,
		R: Encode + Decode + PartialEq,
		NC: FnOnce() -> result::Result<R, String> + UnwindSafe,
		C: CoreApi<Block, Error = Error>,
	>(
		&self,
		params: CallApiAtParams<'a, Block, C, NC, B::State>,
	) -> sp_blockchain::Result<NativeOrEncoded<R>> {
		let core_api = params.core_api;
		let at = params.at;

		let (manager, extensions) = self.execution_extensions.manager_and_extensions(
			at,
			params.context,
		);

		self.executor.contextual_call::<_, fn(_,_) -> _,_,_>(
			|| core_api.initialize_block(at, &self.prepare_environment_block(at)?),
			at,
			params.function,
			&params.arguments,
			params.overlayed_changes,
			Some(params.storage_transaction_cache),
			params.initialize_block,
			manager,
			params.native_call,
			params.recorder,
			Some(extensions),
		)
	}

	fn runtime_version_at(&self, at: &BlockId<Block>) -> sp_blockchain::Result<RuntimeVersion> {
		self.runtime_version_at(at)
	}
}

/// NOTE: only use this implementation when you are sure there are NO consensus-level BlockImport
/// objects. Otherwise, importing blocks directly into the client would be bypassing
/// important verification work.
impl<B, E, Block, RA> sp_consensus::BlockImport<Block> for &Client<B, E, Block, RA> where
	B: backend::Backend<Block>,
	E: CallExecutor<Block> + Send + Sync,
	Block: BlockT,
	Client<B, E, Block, RA>: ProvideRuntimeApi<Block>,
	<Client<B, E, Block, RA> as ProvideRuntimeApi<Block>>::Api: CoreApi<Block, Error = Error> +
		ApiExt<Block, StateBackend = B::State>,
{
	type Error = ConsensusError;
	type Transaction = backend::TransactionFor<B, Block>;

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
		mut import_block: BlockImportParams<Block, backend::TransactionFor<B, Block>>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		if let Some(res) = self.prepare_block_storage_changes(&mut import_block).map_err(|e| {
			warn!("Block prepare storage changes error:\n{:?}", e);
			ConsensusError::ClientImport(e.to_string())
		})? {
			return Ok(res)
		}

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
		let BlockCheckParams { hash, number, parent_hash, allow_missing_state, import_existing } = block;

		// Check the block against white and black lists if any are defined
		// (i.e. fork blocks and bad blocks respectively)
		match self.block_rules.lookup(number, &hash) {
			BlockLookupResult::KnownBad => {
				trace!(
					"Rejecting known bad block: #{} {:?}",
					number,
					hash,
				);
				return Ok(ImportResult::KnownBad);
			},
			BlockLookupResult::Expected(expected_hash) => {
				trace!(
					"Rejecting block from known invalid fork. Got {:?}, expected: {:?} at height {}",
					hash,
					expected_hash,
					number
				);
				return Ok(ImportResult::KnownBad);
			},
			BlockLookupResult::NotSpecial => {}
		}

		// Own status must be checked first. If the block and ancestry is pruned
		// this function must return `AlreadyInChain` rather than `MissingState`
		match self.block_status(&BlockId::Hash(hash))
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
		{
			BlockStatus::InChainWithState | BlockStatus::Queued if !import_existing  => return Ok(ImportResult::AlreadyInChain),
			BlockStatus::InChainWithState | BlockStatus::Queued => {},
			BlockStatus::InChainPruned => return Ok(ImportResult::AlreadyInChain),
			BlockStatus::Unknown => {},
			BlockStatus::KnownBad => return Ok(ImportResult::KnownBad),
		}

		match self.block_status(&BlockId::Hash(parent_hash))
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
			{
				BlockStatus::InChainWithState | BlockStatus::Queued => {},
				BlockStatus::Unknown => return Ok(ImportResult::UnknownParent),
				BlockStatus::InChainPruned if allow_missing_state => {},
				BlockStatus::InChainPruned => return Ok(ImportResult::MissingState),
				BlockStatus::KnownBad => return Ok(ImportResult::KnownBad),
			}


		Ok(ImportResult::imported(false))
	}
}

impl<B, E, Block, RA> sp_consensus::BlockImport<Block> for Client<B, E, Block, RA> where
	B: backend::Backend<Block>,
	E: CallExecutor<Block> + Send + Sync,
	Block: BlockT,
	Self: ProvideRuntimeApi<Block>,
	<Self as ProvideRuntimeApi<Block>>::Api: CoreApi<Block, Error = Error> +
		ApiExt<Block, StateBackend = B::State>,
{
	type Error = ConsensusError;
	type Transaction = backend::TransactionFor<B, Block>;

	fn import_block(
		&mut self,
		import_block: BlockImportParams<Block, Self::Transaction>,
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

impl<B, E, Block, RA> Finalizer<Block, B> for Client<B, E, Block, RA> where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	fn apply_finality(
		&self,
		operation: &mut ClientImportOperation<Block, B>,
		id: BlockId<Block>,
		justification: Option<Justification>,
		notify: bool,
	) -> sp_blockchain::Result<()> {
		let last_best = self.backend.blockchain().info().best_hash;
		let to_finalize_hash = self.backend.blockchain().expect_block_hash_from_id(&id)?;
		self.apply_finality_with_block_hash(
			operation,
			to_finalize_hash,
			justification,
			last_best,
			notify,
		)
	}

	fn finalize_block(
		&self,
		id: BlockId<Block>,
		justification: Option<Justification>,
		notify: bool,
	) -> sp_blockchain::Result<()> {
		self.lock_import_and_run(|operation| {
			self.apply_finality(operation, id, justification, notify)
		})
	}
}


impl<B, E, Block, RA> Finalizer<Block, B> for &Client<B, E, Block, RA> where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	fn apply_finality(
		&self,
		operation: &mut ClientImportOperation<Block, B>,
		id: BlockId<Block>,
		justification: Option<Justification>,
		notify: bool,
	) -> sp_blockchain::Result<()> {
		(**self).apply_finality(operation, id, justification, notify)
	}

	fn finalize_block(
		&self,
		id: BlockId<Block>,
		justification: Option<Justification>,
		notify: bool,
	) -> sp_blockchain::Result<()> {
		(**self).finalize_block(id, justification, notify)
	}
}

impl<B, E, Block, RA> BlockchainEvents<Block> for Client<B, E, Block, RA>
where
	E: CallExecutor<Block>,
	Block: BlockT,
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
	) -> sp_blockchain::Result<StorageEventStream<Block::Hash>> {
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
	B: backend::Backend<Block>,
	Block: BlockT,
{
	/// Instantiate a new LongestChain for Backend B
	pub fn new(backend: Arc<B>) -> Self {
		LongestChain {
			backend,
			_phantom: Default::default()
		}
	}

	fn best_block_header(&self) -> sp_blockchain::Result<<Block as BlockT>::Header> {
		let info = self.backend.blockchain().info();
		let import_lock = self.backend.get_import_lock();
		let best_hash = self.backend.blockchain().best_containing(info.best_hash, None, import_lock)?
			.unwrap_or(info.best_hash);

		Ok(self.backend.blockchain().header(BlockId::Hash(best_hash))?
			.expect("given block hash was fetched from block in db; qed"))
	}

	fn leaves(&self) -> Result<Vec<<Block as BlockT>::Hash>, sp_blockchain::Error> {
		self.backend.blockchain().leaves()
	}
}

impl<B, Block> SelectChain<Block> for LongestChain<B, Block>
where
	B: backend::Backend<Block>,
	Block: BlockT,
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
		B: backend::Backend<Block>,
		E: CallExecutor<Block>,
		Block: BlockT,
{
	fn block_body(
		&self,
		id: &BlockId<Block>,
	) -> sp_blockchain::Result<Option<Vec<<Block as BlockT>::Extrinsic>>> {
		self.body(id)
	}
}

impl<B, E, Block, RA> backend::AuxStore for Client<B, E, Block, RA>
	where
		B: backend::Backend<Block>,
		E: CallExecutor<Block>,
		Block: BlockT,
		Self: ProvideRuntimeApi<Block>,
		<Self as ProvideRuntimeApi<Block>>::Api: CoreApi<Block, Error = Error>,
{
	/// Insert auxiliary data into key-value store.
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
		D: IntoIterator<Item=&'a &'b [u8]>,
	>(&self, insert: I, delete: D) -> sp_blockchain::Result<()> {
		// Import is locked here because we may have other block import
		// operations that tries to set aux data. Note that for consensus
		// layer, one can always use atomic operations to make sure
		// import is only locked once.
		self.lock_import_and_run(|operation| {
			apply_aux(operation, insert, delete)
		})
	}
	/// Query auxiliary data from key-value store.
	fn get_aux(&self, key: &[u8]) -> sp_blockchain::Result<Option<Vec<u8>>> {
		backend::AuxStore::get_aux(&*self.backend, key)
	}
}

impl<B, E, Block, RA> backend::AuxStore for &Client<B, E, Block, RA>
	where
		B: backend::Backend<Block>,
		E: CallExecutor<Block>,
		Block: BlockT,
		Client<B, E, Block, RA>: ProvideRuntimeApi<Block>,
		<Client<B, E, Block, RA> as ProvideRuntimeApi<Block>>::Api: CoreApi<Block, Error = Error>,
{
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
		D: IntoIterator<Item=&'a &'b [u8]>,
	>(&self, insert: I, delete: D) -> sp_blockchain::Result<()> {
		(**self).insert_aux(insert, delete)
	}

	fn get_aux(&self, key: &[u8]) -> sp_blockchain::Result<Option<Vec<u8>>> {
		(**self).get_aux(key)
	}
}


/// Helper function to apply auxiliary data insertion into an operation.
pub fn apply_aux<'a, 'b: 'a, 'c: 'a, B, Block, D, I>(
	operation: &mut ClientImportOperation<Block, B>,
	insert: I,
	delete: D,
) -> sp_blockchain::Result<()>
where
	Block: BlockT,
	B: backend::Backend<Block>,
	I: IntoIterator<Item=&'a(&'c [u8], &'c [u8])>,
	D: IntoIterator<Item=&'a &'b [u8]>,
{
	operation.op.insert_aux(
		insert.into_iter()
			.map(|(k, v)| (k.to_vec(), Some(v.to_vec())))
			.chain(delete.into_iter().map(|k| (k.to_vec(), None)))
	)
}

impl<BE, E, B, RA> sp_consensus::block_validation::Chain<B> for Client<BE, E, B, RA>
	where BE: backend::Backend<B>,
		  E: CallExecutor<B>,
		  B: BlockT
{
	fn block_status(
		&self,
		id: &BlockId<B>,
	) -> Result<BlockStatus, Box<dyn std::error::Error + Send>> {
		Client::block_status(self, id).map_err(|e| Box::new(e) as Box<_>)
	}
}

#[cfg(test)]
pub(crate) mod tests {
	use std::collections::HashMap;
	use super::*;
	use sp_core::{blake2_256, H256};
	use sp_runtime::DigestItem;
	use sp_consensus::{BlockOrigin, SelectChain, BlockImport};
	use substrate_test_runtime_client::{
		prelude::*,
		client_ext::ClientExt,
		sc_client_db::{Backend, DatabaseSettings, DatabaseSettingsSrc, PruningMode},
		runtime::{self, Block, Transfer, RuntimeApi, TestAPI},
	};
	use hex_literal::hex;

	/// Returns tuple, consisting of:
	/// 1) test client pre-filled with blocks changing balances;
	/// 2) roots of changes tries for these blocks
	/// 3) test cases in form (begin, end, key, vec![(block, extrinsic)]) that are required to pass
	pub fn prepare_client_with_key_changes() -> (
		substrate_test_runtime_client::sc_client::Client<substrate_test_runtime_client::Backend, substrate_test_runtime_client::Executor, Block, RuntimeApi>,
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
		let config = Some(ChangesTrieConfiguration::new(4, 2));
		let mut remote_client = TestClientBuilder::new().changes_trie_config(config).build();
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
			let block = builder.build().unwrap().block;
			remote_client.import(BlockOrigin::Own, block).unwrap();

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
		let client = substrate_test_runtime_client::new();

		assert_eq!(
			client.runtime_api().balance_of(
				&BlockId::Number(client.chain_info().best_number),
				AccountKeyring::Alice.into()
			).unwrap(),
			1000
		);
		assert_eq!(
			client.runtime_api().balance_of(
				&BlockId::Number(client.chain_info().best_number),
				AccountKeyring::Ferdie.into()
			).unwrap(),
			0
		);
	}

	#[test]
	fn block_builder_works_with_no_transactions() {
		let mut client = substrate_test_runtime_client::new();

		let block = client.new_block(Default::default()).unwrap().build().unwrap().block;

		client.import(BlockOrigin::Own, block).unwrap();

		assert_eq!(client.chain_info().best_number, 1);
	}

	#[test]
	fn block_builder_works_with_transactions() {
		let mut client = substrate_test_runtime_client::new();

		let mut builder = client.new_block(Default::default()).unwrap();

		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 42,
			nonce: 0,
		}).unwrap();

		let block = builder.build().unwrap().block;
		client.import(BlockOrigin::Own, block).unwrap();

		assert_eq!(client.chain_info().best_number, 1);
		assert_ne!(
			client.state_at(&BlockId::Number(1)).unwrap().pairs(),
			client.state_at(&BlockId::Number(0)).unwrap().pairs()
		);
		assert_eq!(
			client.runtime_api().balance_of(
				&BlockId::Number(client.chain_info().best_number),
				AccountKeyring::Alice.into()
			).unwrap(),
			958
		);
		assert_eq!(
			client.runtime_api().balance_of(
				&BlockId::Number(client.chain_info().best_number),
				AccountKeyring::Ferdie.into()
			).unwrap(),
			42
		);
	}

	#[test]
	fn block_builder_does_not_include_invalid() {
		let mut client = substrate_test_runtime_client::new();

		let mut builder = client.new_block(Default::default()).unwrap();

		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 42,
			nonce: 0,
		}).unwrap();

		assert!(
			builder.push_transfer(Transfer {
				from: AccountKeyring::Eve.into(),
				to: AccountKeyring::Alice.into(),
				amount: 42,
				nonce: 0,
			}).is_err()
		);

		let block = builder.build().unwrap().block;
		client.import(BlockOrigin::Own, block).unwrap();

		assert_eq!(client.chain_info().best_number, 1);
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

		let genesis_hash = client.chain_info().genesis_hash;

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

		let uninserted_block = client.new_block(Default::default()).unwrap().build().unwrap().block;

		assert_eq!(
			None,
			longest_chain_select.finality_target(uninserted_block.hash().clone(), None).unwrap()
		);
	}

	#[test]
	fn uncles_with_only_ancestors() {
		// block tree:
		// G -> A1 -> A2
		let mut client = substrate_test_runtime_client::new();

		// G -> A1
		let a1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block(Default::default()).unwrap().build().unwrap().block;
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
		let mut client = substrate_test_runtime_client::new();

		// G -> A1
		let a1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block_at(
			&BlockId::Hash(a1.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		// A2 -> A3
		let a3 = client.new_block_at(
			&BlockId::Hash(a2.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a3.clone()).unwrap();

		// A3 -> A4
		let a4 = client.new_block_at(
			&BlockId::Hash(a3.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a4.clone()).unwrap();

		// A4 -> A5
		let a5 = client.new_block_at(
			&BlockId::Hash(a4.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a5.clone()).unwrap();

		// A1 -> B2
		let mut builder = client.new_block_at(
			&BlockId::Hash(a1.hash()),
			Default::default(),
			false,
		).unwrap();
		// this push is required as otherwise B2 has the same hash as A2 and won't get imported
		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 41,
			nonce: 0,
		}).unwrap();
		let b2 = builder.build().unwrap().block;
		client.import(BlockOrigin::Own, b2.clone()).unwrap();

		// B2 -> B3
		let b3 = client.new_block_at(
			&BlockId::Hash(b2.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, b3.clone()).unwrap();

		// B3 -> B4
		let b4 = client.new_block_at(
			&BlockId::Hash(b3.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, b4.clone()).unwrap();

		// // B2 -> C3
		let mut builder = client.new_block_at(
			&BlockId::Hash(b2.hash()),
			Default::default(),
			false,
		).unwrap();
		// this push is required as otherwise C3 has the same hash as B3 and won't get imported
		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 1,
		}).unwrap();
		let c3 = builder.build().unwrap().block;
		client.import(BlockOrigin::Own, c3.clone()).unwrap();

		// A1 -> D2
		let mut builder = client.new_block_at(
			&BlockId::Hash(a1.hash()),
			Default::default(),
			false,
		).unwrap();
		// this push is required as otherwise D2 has the same hash as B2 and won't get imported
		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 0,
		}).unwrap();
		let d2 = builder.build().unwrap().block;
		client.import(BlockOrigin::Own, d2.clone()).unwrap();

		let genesis_hash = client.chain_info().genesis_hash;

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

		let (mut client, longest_chain_select) = TestClientBuilder::new().build_with_longest_chain();

		// G -> A1
		let a1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block(Default::default()).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		let genesis_hash = client.chain_info().genesis_hash;

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
		let (mut client, longest_chain_select) = TestClientBuilder::new().build_with_longest_chain();

		// G -> A1
		let a1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block_at(
			&BlockId::Hash(a1.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		// A2 -> A3
		let a3 = client.new_block_at(
			&BlockId::Hash(a2.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a3.clone()).unwrap();

		// A3 -> A4
		let a4 = client.new_block_at(
			&BlockId::Hash(a3.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a4.clone()).unwrap();

		// A4 -> A5
		let a5 = client.new_block_at(
			&BlockId::Hash(a4.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a5.clone()).unwrap();

		// A1 -> B2
		let mut builder = client.new_block_at(
			&BlockId::Hash(a1.hash()),
			Default::default(),
			false,
		).unwrap();
		// this push is required as otherwise B2 has the same hash as A2 and won't get imported
		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 41,
			nonce: 0,
		}).unwrap();
		let b2 = builder.build().unwrap().block;
		client.import(BlockOrigin::Own, b2.clone()).unwrap();

		// B2 -> B3
		let b3 = client.new_block_at(
			&BlockId::Hash(b2.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, b3.clone()).unwrap();

		// B3 -> B4
		let b4 = client.new_block_at(
			&BlockId::Hash(b3.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, b4.clone()).unwrap();

		// // B2 -> C3
		let mut builder = client.new_block_at(
			&BlockId::Hash(b2.hash()),
			Default::default(),
			false,
		).unwrap();
		// this push is required as otherwise C3 has the same hash as B3 and won't get imported
		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 1,
		}).unwrap();
		let c3 = builder.build().unwrap().block;
		client.import(BlockOrigin::Own, c3.clone()).unwrap();

		// A1 -> D2
		let mut builder = client.new_block_at(
			&BlockId::Hash(a1.hash()),
			Default::default(),
			false,
		).unwrap();
		// this push is required as otherwise D2 has the same hash as B2 and won't get imported
		builder.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 0,
		}).unwrap();
		let d2 = builder.build().unwrap().block;
		client.import(BlockOrigin::Own, d2.clone()).unwrap();

		assert_eq!(client.chain_info().best_hash, a5.hash());

		let genesis_hash = client.chain_info().genesis_hash;
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

		let (mut client, longest_chain_select) = TestClientBuilder::new().build_with_longest_chain();

		// G -> A1
		let a1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block(Default::default()).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		let genesis_hash = client.chain_info().genesis_hash;

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
		let mut client = substrate_test_runtime_client::new();

		// G -> A1
		let a1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		// A1 -> A2
		let a2 = client.new_block_at(
			&BlockId::Hash(a1.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		// A2 -> A3
		let justification = vec![1, 2, 3];
		let a3 = client.new_block_at(
			&BlockId::Hash(a2.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import_justified(BlockOrigin::Own, a3.clone(), justification.clone()).unwrap();

		assert_eq!(
			client.chain_info().finalized_hash,
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
		let mut client = substrate_test_runtime_client::new();

		// G -> A1 -> A2
		//   \
		//    -> B1
		let a1 = client.new_block_at(
			&BlockId::Number(0),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		let a2 = client.new_block_at(
			&BlockId::Hash(a1.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		let mut b1 = client.new_block_at(
			&BlockId::Number(0),
			Default::default(),
			false,
		).unwrap();
		// needed to make sure B1 gets a different hash from A1
		b1.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 0,
		}).unwrap();
		// create but don't import B1 just yet
		let b1 = b1.build().unwrap().block;

		// A2 is the current best since it's the longest chain
		assert_eq!(
			client.chain_info().best_hash,
			a2.hash(),
		);

		// importing B1 as finalized should trigger a re-org and set it as new best
		let justification = vec![1, 2, 3];
		client.import_justified(BlockOrigin::Own, b1.clone(), justification).unwrap();

		assert_eq!(
			client.chain_info().best_hash,
			b1.hash(),
		);

		assert_eq!(
			client.chain_info().finalized_hash,
			b1.hash(),
		);
	}

	#[test]
	fn finalizing_diverged_block_should_trigger_reorg() {

		let (mut client, select_chain) = TestClientBuilder::new().build_with_longest_chain();

		// G -> A1 -> A2
		//   \
		//    -> B1 -> B2
		let a1 = client.new_block_at(
			&BlockId::Number(0),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		let a2 = client.new_block_at(
			&BlockId::Hash(a1.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		let mut b1 = client.new_block_at(
			&BlockId::Number(0),
			Default::default(),
			false,
		).unwrap();
		// needed to make sure B1 gets a different hash from A1
		b1.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 0,
		}).unwrap();
		let b1 = b1.build().unwrap().block;
		client.import(BlockOrigin::Own, b1.clone()).unwrap();

		let b2 = client.new_block_at(
			&BlockId::Hash(b1.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, b2.clone()).unwrap();

		// A2 is the current best since it's the longest chain
		assert_eq!(
			client.chain_info().best_hash,
			a2.hash(),
		);

		// we finalize block B1 which is on a different branch from current best
		// which should trigger a re-org.
		ClientExt::finalize_block(&client, BlockId::Hash(b1.hash()), None).unwrap();

		// B1 should now be the latest finalized
		assert_eq!(
			client.chain_info().finalized_hash,
			b1.hash(),
		);

		// and B1 should be the new best block (`finalize_block` as no way of
		// knowing about B2)
		assert_eq!(
			client.chain_info().best_hash,
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
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, b3.clone()).unwrap();

		assert_eq!(
			client.chain_info().best_hash,
			b3.hash(),
		);
	}

	#[test]
	fn get_header_by_block_number_doesnt_panic() {
		let client = substrate_test_runtime_client::new();

		// backend uses u32 for block numbers, make sure we don't panic when
		// trying to convert
		let id = BlockId::<Block>::Number(72340207214430721);
		client.header(&id).expect_err("invalid block number overflows u32");
	}

	#[test]
	fn state_reverted_on_reorg() {
		let _ = env_logger::try_init();
		let mut client = substrate_test_runtime_client::new();

		let current_balance = |client: &substrate_test_runtime_client::TestClient|
			client.runtime_api().balance_of(
				&BlockId::number(client.chain_info().best_number), AccountKeyring::Alice.into()
			).unwrap();

		// G -> A1 -> A2
		//   \
		//    -> B1
		let mut a1 = client.new_block_at(
			&BlockId::Number(0),
			Default::default(),
			false,
		).unwrap();
		a1.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Bob.into(),
			amount: 10,
			nonce: 0,
		}).unwrap();
		let a1 = a1.build().unwrap().block;
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		let mut b1 = client.new_block_at(
			&BlockId::Number(0),
			Default::default(),
			false,
		).unwrap();
		b1.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 50,
			nonce: 0,
		}).unwrap();
		let b1 = b1.build().unwrap().block;
		// Reorg to B1
		client.import_as_best(BlockOrigin::Own, b1.clone()).unwrap();

		assert_eq!(950, current_balance(&client));
		let mut a2 = client.new_block_at(
			&BlockId::Hash(a1.hash()),
			Default::default(),
			false,
		).unwrap();
		a2.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Charlie.into(),
			amount: 10,
			nonce: 1,
		}).unwrap();
		let a2 = a2.build().unwrap().block;
		// Re-org to A2
		client.import_as_best(BlockOrigin::Own, a2).unwrap();
		assert_eq!(980, current_balance(&client));
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

		let mut client = TestClientBuilder::with_backend(backend).build();

		//    -> C1
		//   /
		// G -> A1 -> A2
		//   \
		//    -> B1 -> B2 -> B3

		let a1 = client.new_block_at(
			&BlockId::Number(0),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a1.clone()).unwrap();

		let a2 = client.new_block_at(
			&BlockId::Hash(a1.hash()),
			Default::default(),
			false,
		).unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, a2.clone()).unwrap();

		let mut b1 = client.new_block_at(&BlockId::Number(0), Default::default(), false).unwrap();

		// needed to make sure B1 gets a different hash from A1
		b1.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 0,
		}).unwrap();
		let b1 = b1.build().unwrap().block;
		client.import(BlockOrigin::Own, b1.clone()).unwrap();

		let b2 = client.new_block_at(&BlockId::Hash(b1.hash()), Default::default(), false)
			.unwrap().build().unwrap().block;
		client.import(BlockOrigin::Own, b2.clone()).unwrap();

		// prepare B3 before we finalize A2, because otherwise we won't be able to
		// read changes trie configuration after A2 is finalized
		let b3 = client.new_block_at(&BlockId::Hash(b2.hash()), Default::default(), false)
			.unwrap().build().unwrap().block;

		// we will finalize A2 which should make it impossible to import a new
		// B3 at the same height but that doesnt't include it
		ClientExt::finalize_block(&client, BlockId::Hash(a2.hash()), None).unwrap();

		let import_err = client.import(BlockOrigin::Own, b3).err().unwrap();
		let expected_err = ConsensusError::ClientImport(
			sp_blockchain::Error::NotInFinalizedChain.to_string()
		);

		assert_eq!(
			import_err.to_string(),
			expected_err.to_string(),
		);

		// adding a C1 block which is lower than the last finalized should also
		// fail (with a cheaper check that doesn't require checking ancestry).
		let mut c1 = client.new_block_at(&BlockId::Number(0), Default::default(), false).unwrap();

		// needed to make sure C1 gets a different hash from A1 and B1
		c1.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 2,
			nonce: 0,
		}).unwrap();
		let c1 = c1.build().unwrap().block;

		let import_err = client.import(BlockOrigin::Own, c1).err().unwrap();
		let expected_err = ConsensusError::ClientImport(
			sp_blockchain::Error::NotInFinalizedChain.to_string()
		);

		assert_eq!(
			import_err.to_string(),
			expected_err.to_string(),
		);
	}


	#[test]
	fn respects_block_rules() {

		fn run_test(
			record_only: bool,
			known_bad: &mut HashSet<H256>,
			fork_rules: &mut Vec<(u64, H256)>,
		) {
			let mut client = if record_only {
				TestClientBuilder::new().build()
			} else {
				TestClientBuilder::new()
					.set_block_rules(
						Some(fork_rules.clone()),
						Some(known_bad.clone()),
					)
					.build()
			};

			let block_ok = client.new_block_at(&BlockId::Number(0), Default::default(), false)
				.unwrap().build().unwrap().block;

			let params = BlockCheckParams {
				hash: block_ok.hash().clone(),
				number: 0,
				parent_hash: block_ok.header().parent_hash().clone(),
				allow_missing_state: false,
				import_existing: false,
			};
			assert_eq!(client.check_block(params).unwrap(), ImportResult::imported(false));

			// this is 0x0d6d6612a10485370d9e085aeea7ec427fb3f34d961c6a816cdbe5cde2278864
			let mut block_not_ok = client.new_block_at(&BlockId::Number(0), Default::default(), false)
				.unwrap();
			block_not_ok.push_storage_change(vec![0], Some(vec![1])).unwrap();
			let block_not_ok = block_not_ok.build().unwrap().block;

			let params = BlockCheckParams {
				hash: block_not_ok.hash().clone(),
				number: 0,
				parent_hash: block_not_ok.header().parent_hash().clone(),
				allow_missing_state: false,
				import_existing: false,
			};
			if record_only {
				known_bad.insert(block_not_ok.hash());
			} else {
				assert_eq!(client.check_block(params).unwrap(), ImportResult::KnownBad);
			}

			// Now going to the fork
			client.import_as_final(BlockOrigin::Own, block_ok).unwrap();

			// And check good fork
			let mut block_ok = client.new_block_at(&BlockId::Number(1), Default::default(), false)
				.unwrap();
			block_ok.push_storage_change(vec![0], Some(vec![2])).unwrap();
			let block_ok = block_ok.build().unwrap().block;

			let params = BlockCheckParams {
				hash: block_ok.hash().clone(),
				number: 1,
				parent_hash: block_ok.header().parent_hash().clone(),
				allow_missing_state: false,
				import_existing: false,
			};
			if record_only {
				fork_rules.push((1, block_ok.hash().clone()));
			}
			assert_eq!(client.check_block(params).unwrap(), ImportResult::imported(false));

			// And now try bad fork
			let mut block_not_ok = client.new_block_at(&BlockId::Number(1), Default::default(), false)
				.unwrap();
			block_not_ok.push_storage_change(vec![0], Some(vec![3])).unwrap();
			let block_not_ok = block_not_ok.build().unwrap().block;

			let params = BlockCheckParams {
				hash: block_not_ok.hash().clone(),
				number: 1,
				parent_hash: block_not_ok.header().parent_hash().clone(),
				allow_missing_state: false,
				import_existing: false,
			};

			if !record_only {
				assert_eq!(client.check_block(params).unwrap(), ImportResult::KnownBad);
			}
		}

		let mut known_bad = HashSet::new();
		let mut fork_rules = Vec::new();

		// records what bad_blocks and fork_blocks hashes should be
		run_test(true, &mut known_bad, &mut fork_rules);

		// enforces rules and actually makes assertions
		run_test(false, &mut known_bad, &mut fork_rules);
	}

	#[test]
	fn returns_status_for_pruned_blocks() {
		let _ = env_logger::try_init();
		let tmp = tempfile::tempdir().unwrap();

		// set to prune after 1 block
		// states
		let backend = Arc::new(Backend::new(
				DatabaseSettings {
					state_cache_size: 1 << 20,
					state_cache_child_ratio: None,
					pruning: PruningMode::keep_blocks(1),
					source: DatabaseSettingsSrc::Path {
						path: tmp.path().into(),
						cache_size: None,
					}
				},
				u64::max_value(),
		).unwrap());

		let mut client = TestClientBuilder::with_backend(backend).build();

		let a1 = client.new_block_at(&BlockId::Number(0), Default::default(), false)
			.unwrap().build().unwrap().block;

		let mut b1 = client.new_block_at(&BlockId::Number(0), Default::default(), false).unwrap();

		// b1 is created, but not imported
		b1.push_transfer(Transfer {
			from: AccountKeyring::Alice.into(),
			to: AccountKeyring::Ferdie.into(),
			amount: 1,
			nonce: 0,
		}).unwrap();
		let b1 = b1.build().unwrap().block;

		let check_block_a1 = BlockCheckParams {
			hash: a1.hash().clone(),
			number: 0,
			parent_hash: a1.header().parent_hash().clone(),
			allow_missing_state: false,
			import_existing: false,
		};

		assert_eq!(client.check_block(check_block_a1.clone()).unwrap(), ImportResult::imported(false));
		assert_eq!(client.block_status(&BlockId::hash(check_block_a1.hash)).unwrap(), BlockStatus::Unknown);

		client.import_as_final(BlockOrigin::Own, a1.clone()).unwrap();

		assert_eq!(client.check_block(check_block_a1.clone()).unwrap(), ImportResult::AlreadyInChain);
		assert_eq!(client.block_status(&BlockId::hash(check_block_a1.hash)).unwrap(), BlockStatus::InChainWithState);

		let a2 = client.new_block_at(&BlockId::Hash(a1.hash()), Default::default(), false)
			.unwrap().build().unwrap().block;
		client.import_as_final(BlockOrigin::Own, a2.clone()).unwrap();

		let check_block_a2 = BlockCheckParams {
			hash: a2.hash().clone(),
			number: 1,
			parent_hash: a1.header().parent_hash().clone(),
			allow_missing_state: false,
			import_existing: false,
		};

		assert_eq!(client.check_block(check_block_a1.clone()).unwrap(), ImportResult::AlreadyInChain);
		assert_eq!(client.block_status(&BlockId::hash(check_block_a1.hash)).unwrap(), BlockStatus::InChainPruned);
		assert_eq!(client.check_block(check_block_a2.clone()).unwrap(), ImportResult::AlreadyInChain);
		assert_eq!(client.block_status(&BlockId::hash(check_block_a2.hash)).unwrap(), BlockStatus::InChainWithState);

		let a3 = client.new_block_at(&BlockId::Hash(a2.hash()), Default::default(), false)
			.unwrap().build().unwrap().block;

		client.import_as_final(BlockOrigin::Own, a3.clone()).unwrap();
		let check_block_a3 = BlockCheckParams {
			hash: a3.hash().clone(),
			number: 2,
			parent_hash: a2.header().parent_hash().clone(),
			allow_missing_state: false,
			import_existing: false,
		};

		// a1 and a2 are both pruned at this point
		assert_eq!(client.check_block(check_block_a1.clone()).unwrap(), ImportResult::AlreadyInChain);
		assert_eq!(client.block_status(&BlockId::hash(check_block_a1.hash)).unwrap(), BlockStatus::InChainPruned);
		assert_eq!(client.check_block(check_block_a2.clone()).unwrap(), ImportResult::AlreadyInChain);
		assert_eq!(client.block_status(&BlockId::hash(check_block_a2.hash)).unwrap(), BlockStatus::InChainPruned);
		assert_eq!(client.check_block(check_block_a3.clone()).unwrap(), ImportResult::AlreadyInChain);
		assert_eq!(client.block_status(&BlockId::hash(check_block_a3.hash)).unwrap(), BlockStatus::InChainWithState);

		let mut check_block_b1 = BlockCheckParams {
			hash: b1.hash().clone(),
			number: 0,
			parent_hash: b1.header().parent_hash().clone(),
			allow_missing_state: false,
			import_existing: false,
		};
		assert_eq!(client.check_block(check_block_b1.clone()).unwrap(), ImportResult::MissingState);
		check_block_b1.allow_missing_state = true;
		assert_eq!(client.check_block(check_block_b1.clone()).unwrap(), ImportResult::imported(false));
		check_block_b1.parent_hash = H256::random();
		assert_eq!(client.check_block(check_block_b1.clone()).unwrap(), ImportResult::UnknownParent);
	}

	#[test]
	fn imports_blocks_with_changes_tries_config_change() {
		// create client with initial 4^2 configuration
		let mut client = TestClientBuilder::with_default_backend()
			.changes_trie_config(Some(ChangesTrieConfiguration {
				digest_interval: 4,
				digest_levels: 2,
			})).build();

		// ===================================================================
		// blocks 1,2,3,4,5,6,7,8,9,10 are empty
		// block 11 changes the key
		// block 12 is the L1 digest that covers this change
		// blocks 13,14,15,16,17,18,19,20,21,22 are empty
		// block 23 changes the configuration to 5^1 AND is skewed digest
		// ===================================================================
		// blocks 24,25 are changing the key
		// block 26 is empty
		// block 27 changes the key
		// block 28 is the L1 digest (NOT SKEWED!!!) that covers changes AND changes configuration to 3^1
		// ===================================================================
		// block 29 is empty
		// block 30 changes the key
		// block 31 is L1 digest that covers this change
		// ===================================================================
		(1..11).for_each(|number| {
			let block = client.new_block_at(&BlockId::Number(number - 1), Default::default(), false)
				.unwrap().build().unwrap().block;
			client.import(BlockOrigin::Own, block).unwrap();
		});
		(11..12).for_each(|number| {
			let mut block = client.new_block_at(&BlockId::Number(number - 1), Default::default(), false).unwrap();
			block.push_storage_change(vec![42], Some(number.to_le_bytes().to_vec())).unwrap();
			let block = block.build().unwrap().block;
			client.import(BlockOrigin::Own, block).unwrap();
		});
		(12..23).for_each(|number| {
			let block = client.new_block_at(&BlockId::Number(number - 1), Default::default(), false)
				.unwrap().build().unwrap().block;
			client.import(BlockOrigin::Own, block).unwrap();
		});
		(23..24).for_each(|number| {
			let mut block = client.new_block_at(&BlockId::Number(number - 1), Default::default(), false).unwrap();
			block.push_changes_trie_configuration_update(Some(ChangesTrieConfiguration {
				digest_interval: 5,
				digest_levels: 1,
			})).unwrap();
			let block = block.build().unwrap().block;
			client.import(BlockOrigin::Own, block).unwrap();
		});
		(24..26).for_each(|number| {
			let mut block = client.new_block_at(&BlockId::Number(number - 1), Default::default(), false).unwrap();
			block.push_storage_change(vec![42], Some(number.to_le_bytes().to_vec())).unwrap();
			let block = block.build().unwrap().block;
			client.import(BlockOrigin::Own, block).unwrap();
		});
		(26..27).for_each(|number| {
			let block = client.new_block_at(&BlockId::Number(number - 1), Default::default(), false)
				.unwrap().build().unwrap().block;
			client.import(BlockOrigin::Own, block).unwrap();
		});
		(27..28).for_each(|number| {
			let mut block = client.new_block_at(&BlockId::Number(number - 1), Default::default(), false).unwrap();
			block.push_storage_change(vec![42], Some(number.to_le_bytes().to_vec())).unwrap();
			let block = block.build().unwrap().block;
			client.import(BlockOrigin::Own, block).unwrap();
		});
		(28..29).for_each(|number| {
			let mut block = client.new_block_at(&BlockId::Number(number - 1), Default::default(), false).unwrap();
			block.push_changes_trie_configuration_update(Some(ChangesTrieConfiguration {
				digest_interval: 3,
				digest_levels: 1,
			})).unwrap();
			let block = block.build().unwrap().block;
			client.import(BlockOrigin::Own, block).unwrap();
		});
		(29..30).for_each(|number| {
			let block = client.new_block_at(&BlockId::Number(number - 1), Default::default(), false)
				.unwrap().build().unwrap().block;
			client.import(BlockOrigin::Own, block).unwrap();
		});
		(30..31).for_each(|number| {
			let mut block = client.new_block_at(&BlockId::Number(number - 1), Default::default(), false).unwrap();
			block.push_storage_change(vec![42], Some(number.to_le_bytes().to_vec())).unwrap();
			let block = block.build().unwrap().block;
			client.import(BlockOrigin::Own, block).unwrap();
		});
		(31..32).for_each(|number| {
			let block = client.new_block_at(&BlockId::Number(number - 1), Default::default(), false)
				.unwrap().build().unwrap().block;
			client.import(BlockOrigin::Own, block).unwrap();
		});

		// now check that configuration cache works
		assert_eq!(
			client.key_changes(1, BlockId::Number(31), None, &StorageKey(vec![42])).unwrap(),
			vec![(30, 0), (27, 0), (25, 0), (24, 0), (11, 0)]
		);
	}

	#[test]
	fn storage_keys_iter_prefix_and_start_key_works() {
		let client = substrate_test_runtime_client::new();

		let prefix = StorageKey(hex!("3a").to_vec());

		let res: Vec<_> = client.storage_keys_iter(&BlockId::Number(0), Some(&prefix), None)
			.unwrap()
			.map(|x| x.0)
			.collect();
		assert_eq!(res, [hex!("3a636f6465").to_vec(), hex!("3a686561707061676573").to_vec()]);

		let res: Vec<_> = client.storage_keys_iter(&BlockId::Number(0), Some(&prefix), Some(&StorageKey(hex!("3a636f6465").to_vec())))
			.unwrap()
			.map(|x| x.0)
			.collect();
		assert_eq!(res, [hex!("3a686561707061676573").to_vec()]);

		let res: Vec<_> = client.storage_keys_iter(&BlockId::Number(0), Some(&prefix), Some(&StorageKey(hex!("3a686561707061676573").to_vec())))
			.unwrap()
			.map(|x| x.0)
			.collect();
		assert_eq!(res, Vec::<Vec<u8>>::new());
	}

	#[test]
	fn storage_keys_iter_works() {
		let client = substrate_test_runtime_client::new();

		let prefix = StorageKey(hex!("").to_vec());

		let res: Vec<_> = client.storage_keys_iter(&BlockId::Number(0), Some(&prefix), None)
			.unwrap()
			.take(2)
			.map(|x| x.0)
			.collect();
		assert_eq!(res, [hex!("0befda6e1ca4ef40219d588a727f1271").to_vec(), hex!("3a636f6465").to_vec()]);

		let res: Vec<_> = client.storage_keys_iter(&BlockId::Number(0), Some(&prefix), Some(&StorageKey(hex!("3a636f6465").to_vec())))
			.unwrap()
			.take(3)
			.map(|x| x.0)
			.collect();
		assert_eq!(res, [
			hex!("3a686561707061676573").to_vec(),
			hex!("6644b9b8bc315888ac8e41a7968dc2b4141a5403c58acdf70b7e8f7e07bf5081").to_vec(),
			hex!("79c07e2b1d2e2abfd4855b936617eeff5e0621c4869aa60c02be9adcc98a0d1d").to_vec(),
		]);

		let res: Vec<_> = client.storage_keys_iter(&BlockId::Number(0), Some(&prefix), Some(&StorageKey(hex!("79c07e2b1d2e2abfd4855b936617eeff5e0621c4869aa60c02be9adcc98a0d1d").to_vec())))
			.unwrap()
			.take(1)
			.map(|x| x.0)
			.collect();
		assert_eq!(res, [hex!("cf722c0832b5231d35e29f319ff27389f5032bfc7bfc3ba5ed7839f2042fb99f").to_vec()]);
	}
}
