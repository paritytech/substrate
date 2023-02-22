// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Substrate Client

use super::{
	block_rules::{BlockRules, LookupResult as BlockLookupResult},
	genesis::BuildGenesisBlock,
};
use futures::{FutureExt, StreamExt};
use log::{error, info, trace, warn};
use parking_lot::{Mutex, RwLock};
use prometheus_endpoint::Registry;
use rand::Rng;
use sc_block_builder::{BlockBuilderApi, BlockBuilderProvider, RecordProof};
use sc_client_api::{
	backend::{
		self, apply_aux, BlockImportOperation, ClientImportOperation, FinalizeSummary, Finalizer,
		ImportSummary, LockImportRun, NewBlockState, StorageProvider,
	},
	client::{
		BadBlocks, BlockBackend, BlockImportNotification, BlockOf, BlockchainEvents, ClientInfo,
		FinalityNotification, FinalityNotifications, ForkBlocks, ImportNotifications,
		PreCommitActions, ProvideUncles,
	},
	execution_extensions::ExecutionExtensions,
	notifications::{StorageEventStream, StorageNotifications},
	CallExecutor, ExecutorProvider, KeyIterator, OnFinalityAction, OnImportAction, ProofProvider,
	UsageProvider,
};
use sc_consensus::{
	BlockCheckParams, BlockImportParams, ForkChoiceStrategy, ImportResult, StateAction,
};
use sc_executor::{RuntimeVersion, RuntimeVersionOf};
use sc_telemetry::{telemetry, TelemetryHandle, SUBSTRATE_INFO};
use sp_api::{
	ApiExt, ApiRef, CallApiAt, CallApiAtParams, ConstructRuntimeApi, Core as CoreApi,
	ProvideRuntimeApi,
};
use sp_blockchain::{
	self as blockchain, well_known_cache_keys::Id as CacheKeyId, Backend as ChainBackend,
	CachedHeaderMetadata, Error, HeaderBackend as ChainHeaderBackend, HeaderMetadata,
};
use sp_consensus::{BlockOrigin, BlockStatus, Error as ConsensusError};

use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedSender};
use sp_core::{
	storage::{
		well_known_keys, ChildInfo, ChildType, PrefixedStorageKey, Storage, StorageChild,
		StorageData, StorageKey,
	},
	traits::SpawnNamed,
};
#[cfg(feature = "test-helpers")]
use sp_keystore::SyncCryptoStorePtr;
use sp_runtime::{
	generic::{BlockId, SignedBlock},
	traits::{
		Block as BlockT, BlockIdTo, HashFor, Header as HeaderT, NumberFor, One,
		SaturatedConversion, Zero,
	},
	Digest, Justification, Justifications, StateVersion,
};
use sp_state_machine::{
	prove_child_read, prove_range_read_with_child_with_size, prove_read,
	read_range_proof_check_with_child_on_proving_backend, Backend as StateBackend,
	ChildStorageCollection, KeyValueStates, KeyValueStorageLevel, StorageCollection,
	MAX_NESTED_TRIE_DEPTH,
};
use sp_trie::{CompactProof, StorageProof};
use std::{
	collections::{hash_map::DefaultHasher, HashMap, HashSet},
	marker::PhantomData,
	path::PathBuf,
	sync::Arc,
};

#[cfg(feature = "test-helpers")]
use {
	super::call_executor::LocalCallExecutor, sc_client_api::in_mem, sp_core::traits::CodeExecutor,
};

type NotificationSinks<T> = Mutex<Vec<TracingUnboundedSender<T>>>;

/// Substrate Client
pub struct Client<B, E, Block, RA>
where
	Block: BlockT,
{
	backend: Arc<B>,
	executor: E,
	storage_notifications: StorageNotifications<Block>,
	import_notification_sinks: NotificationSinks<BlockImportNotification<Block>>,
	finality_notification_sinks: NotificationSinks<FinalityNotification<Block>>,
	// Collects auxiliary operations to be performed atomically together with
	// block import operations.
	import_actions: Mutex<Vec<OnImportAction<Block>>>,
	// Collects auxiliary operations to be performed atomically together with
	// block finalization operations.
	finality_actions: Mutex<Vec<OnFinalityAction<Block>>>,
	// Holds the block hash currently being imported. TODO: replace this with block queue.
	importing_block: RwLock<Option<Block::Hash>>,
	block_rules: BlockRules<Block>,
	config: ClientConfig<Block>,
	telemetry: Option<TelemetryHandle>,
	unpin_worker_sender: TracingUnboundedSender<Block::Hash>,
	_phantom: PhantomData<RA>,
}

/// Used in importing a block, where additional changes are made after the runtime
/// executed.
enum PrePostHeader<H> {
	/// they are the same: no post-runtime digest items.
	Same(H),
	/// different headers (pre, post).
	Different(H, H),
}

impl<H> PrePostHeader<H> {
	/// get a reference to the "post-header" -- the header as it should be
	/// after all changes are applied.
	fn post(&self) -> &H {
		match *self {
			PrePostHeader::Same(ref h) => h,
			PrePostHeader::Different(_, ref h) => h,
		}
	}

	/// convert to the "post-header" -- the header as it should be after
	/// all changes are applied.
	fn into_post(self) -> H {
		match self {
			PrePostHeader::Same(h) => h,
			PrePostHeader::Different(_, h) => h,
		}
	}
}

enum PrepareStorageChangesResult<B: backend::Backend<Block>, Block: BlockT> {
	Discard(ImportResult),
	Import(Option<sc_consensus::StorageChanges<Block, backend::TransactionFor<B, Block>>>),
}

/// Create an instance of in-memory client.
#[cfg(feature = "test-helpers")]
pub fn new_in_mem<E, Block, G, RA>(
	backend: Arc<in_mem::Backend<Block>>,
	executor: E,
	genesis_block_builder: G,
	keystore: Option<SyncCryptoStorePtr>,
	prometheus_registry: Option<Registry>,
	telemetry: Option<TelemetryHandle>,
	spawn_handle: Box<dyn SpawnNamed>,
	config: ClientConfig<Block>,
) -> sp_blockchain::Result<
	Client<in_mem::Backend<Block>, LocalCallExecutor<Block, in_mem::Backend<Block>, E>, Block, RA>,
>
where
	E: CodeExecutor + RuntimeVersionOf,
	Block: BlockT,
	G: BuildGenesisBlock<
			Block,
			BlockImportOperation = <in_mem::Backend<Block> as backend::Backend<Block>>::BlockImportOperation,
		>,
{
	new_with_backend(
		backend,
		executor,
		genesis_block_builder,
		keystore,
		spawn_handle,
		prometheus_registry,
		telemetry,
		config,
	)
}

/// Relevant client configuration items relevant for the client.
#[derive(Debug, Clone)]
pub struct ClientConfig<Block: BlockT> {
	/// Enable the offchain worker db.
	pub offchain_worker_enabled: bool,
	/// If true, allows access from the runtime to write into offchain worker db.
	pub offchain_indexing_api: bool,
	/// Path where WASM files exist to override the on-chain WASM.
	pub wasm_runtime_overrides: Option<PathBuf>,
	/// Skip writing genesis state on first start.
	pub no_genesis: bool,
	/// Map of WASM runtime substitute starting at the child of the given block until the runtime
	/// version doesn't match anymore.
	pub wasm_runtime_substitutes: HashMap<NumberFor<Block>, Vec<u8>>,
}

impl<Block: BlockT> Default for ClientConfig<Block> {
	fn default() -> Self {
		Self {
			offchain_worker_enabled: false,
			offchain_indexing_api: false,
			wasm_runtime_overrides: None,
			no_genesis: false,
			wasm_runtime_substitutes: HashMap::new(),
		}
	}
}

/// Create a client with the explicitly provided backend.
/// This is useful for testing backend implementations.
#[cfg(feature = "test-helpers")]
pub fn new_with_backend<B, E, Block, G, RA>(
	backend: Arc<B>,
	executor: E,
	genesis_block_builder: G,
	keystore: Option<SyncCryptoStorePtr>,
	spawn_handle: Box<dyn SpawnNamed>,
	prometheus_registry: Option<Registry>,
	telemetry: Option<TelemetryHandle>,
	config: ClientConfig<Block>,
) -> sp_blockchain::Result<Client<B, LocalCallExecutor<Block, B, E>, Block, RA>>
where
	E: CodeExecutor + RuntimeVersionOf,
	G: BuildGenesisBlock<
		Block,
		BlockImportOperation = <B as backend::Backend<Block>>::BlockImportOperation,
	>,
	Block: BlockT,
	B: backend::LocalBackend<Block> + 'static,
{
	let extensions = ExecutionExtensions::new(
		Default::default(),
		keystore,
		sc_offchain::OffchainDb::factory_from_backend(&*backend),
	);

	let call_executor = LocalCallExecutor::new(
		backend.clone(),
		executor,
		spawn_handle.clone(),
		config.clone(),
		extensions,
	)?;

	Client::new(
		backend,
		call_executor,
		spawn_handle,
		genesis_block_builder,
		Default::default(),
		Default::default(),
		prometheus_registry,
		telemetry,
		config,
	)
}

impl<B, E, Block, RA> BlockOf for Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	type Type = Block;
}

impl<B, E, Block, RA> LockImportRun<Block, B> for Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	fn lock_import_and_run<R, Err, F>(&self, f: F) -> Result<R, Err>
	where
		F: FnOnce(&mut ClientImportOperation<Block, B>) -> Result<R, Err>,
		Err: From<sp_blockchain::Error>,
	{
		let inner = || {
			let _import_lock = self.backend.get_import_lock().write();

			let mut op = ClientImportOperation {
				op: self.backend.begin_operation()?,
				notify_imported: None,
				notify_finalized: None,
			};

			let r = f(&mut op)?;

			let ClientImportOperation { mut op, notify_imported, notify_finalized } = op;

			let finality_notification = notify_finalized.map(|summary| {
				FinalityNotification::from_summary(summary, self.unpin_worker_sender.clone())
			});

			let (import_notification, storage_changes) = match notify_imported {
				Some(mut summary) => {
					let storage_changes = summary.storage_changes.take();
					(
						Some(BlockImportNotification::from_summary(
							summary,
							self.unpin_worker_sender.clone(),
						)),
						storage_changes,
					)
				},
				None => (None, None),
			};

			if let Some(ref notification) = finality_notification {
				for action in self.finality_actions.lock().iter_mut() {
					op.insert_aux(action(notification))?;
				}
			}
			if let Some(ref notification) = import_notification {
				for action in self.import_actions.lock().iter_mut() {
					op.insert_aux(action(notification))?;
				}
			}

			self.backend.commit_operation(op)?;

			// We need to pin the block in the backend once
			// for each notification. Once all notifications are
			// dropped, the block will be unpinned automatically.
			if let Some(ref notification) = finality_notification {
				if let Err(err) = self.backend.pin_block(notification.hash) {
					error!(
						"Unable to pin block for finality notification. hash: {}, Error: {}",
						notification.hash, err
					);
				};
			}

			if let Some(ref notification) = import_notification {
				if let Err(err) = self.backend.pin_block(notification.hash) {
					error!(
						"Unable to pin block for import notification. hash: {}, Error: {}",
						notification.hash, err
					);
				};
			}

			self.notify_finalized(finality_notification)?;
			self.notify_imported(import_notification, storage_changes)?;

			Ok(r)
		};

		let result = inner();
		*self.importing_block.write() = None;

		result
	}
}

impl<B, E, Block, RA> LockImportRun<Block, B> for &Client<B, E, Block, RA>
where
	Block: BlockT,
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
{
	fn lock_import_and_run<R, Err, F>(&self, f: F) -> Result<R, Err>
	where
		F: FnOnce(&mut ClientImportOperation<Block, B>) -> Result<R, Err>,
		Err: From<sp_blockchain::Error>,
	{
		(**self).lock_import_and_run(f)
	}
}

impl<B, E, Block, RA> Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
	Block::Header: Clone,
{
	/// Creates new Substrate Client with given blockchain and code executor.
	pub fn new<G>(
		backend: Arc<B>,
		executor: E,
		spawn_handle: Box<dyn SpawnNamed>,
		genesis_block_builder: G,
		fork_blocks: ForkBlocks<Block>,
		bad_blocks: BadBlocks<Block>,
		prometheus_registry: Option<Registry>,
		telemetry: Option<TelemetryHandle>,
		config: ClientConfig<Block>,
	) -> sp_blockchain::Result<Self>
	where
		G: BuildGenesisBlock<
			Block,
			BlockImportOperation = <B as backend::Backend<Block>>::BlockImportOperation,
		>,
		B: 'static,
	{
		let info = backend.blockchain().info();
		if info.finalized_state.is_none() {
			let (genesis_block, mut op) = genesis_block_builder.build_genesis_block()?;
			info!(
				"🔨 Initializing Genesis block/state (state: {}, header-hash: {})",
				genesis_block.header().state_root(),
				genesis_block.header().hash()
			);
			// Genesis may be written after some blocks have been imported and finalized.
			// So we only finalize it when the database is empty.
			let block_state = if info.best_hash == Default::default() {
				NewBlockState::Final
			} else {
				NewBlockState::Normal
			};
			let (header, body) = genesis_block.deconstruct();
			op.set_block_data(header, Some(body), None, None, block_state)?;
			backend.commit_operation(op)?;
		}

		let (unpin_worker_sender, mut rx) =
			tracing_unbounded::<Block::Hash>("unpin-worker-channel", 10_000);
		let task_backend = Arc::downgrade(&backend);
		spawn_handle.spawn(
			"unpin-worker",
			None,
			async move {
				while let Some(message) = rx.next().await {
					if let Some(backend) = task_backend.upgrade() {
						backend.unpin_block(message);
					} else {
						log::debug!("Terminating unpin-worker, backend reference was dropped.");
						return
					}
				}
				log::debug!("Terminating unpin-worker, stream terminated.")
			}
			.boxed(),
		);

		Ok(Client {
			backend,
			executor,
			storage_notifications: StorageNotifications::new(prometheus_registry),
			import_notification_sinks: Default::default(),
			finality_notification_sinks: Default::default(),
			import_actions: Default::default(),
			finality_actions: Default::default(),
			importing_block: Default::default(),
			block_rules: BlockRules::new(fork_blocks, bad_blocks),
			config,
			telemetry,
			unpin_worker_sender,
			_phantom: Default::default(),
		})
	}

	/// returns a reference to the block import notification sinks
	/// useful for test environments.
	pub fn import_notification_sinks(&self) -> &NotificationSinks<BlockImportNotification<Block>> {
		&self.import_notification_sinks
	}

	/// returns a reference to the finality notification sinks
	/// useful for test environments.
	pub fn finality_notification_sinks(&self) -> &NotificationSinks<FinalityNotification<Block>> {
		&self.finality_notification_sinks
	}

	/// Get a reference to the state at a given block.
	pub fn state_at(&self, hash: Block::Hash) -> sp_blockchain::Result<B::State> {
		self.backend.state_at(hash)
	}

	/// Get the code at a given block.
	pub fn code_at(&self, hash: Block::Hash) -> sp_blockchain::Result<Vec<u8>> {
		Ok(StorageProvider::storage(self, hash, &StorageKey(well_known_keys::CODE.to_vec()))?
			.expect(
				"None is returned if there's no value stored for the given key;\
				':code' key is always defined; qed",
			)
			.0)
	}

	/// Get the RuntimeVersion at a given block.
	pub fn runtime_version_at(&self, hash: Block::Hash) -> sp_blockchain::Result<RuntimeVersion> {
		CallExecutor::runtime_version(&self.executor, hash)
	}

	/// Apply a checked and validated block to an operation. If a justification is provided
	/// then `finalized` *must* be true.
	fn apply_block(
		&self,
		operation: &mut ClientImportOperation<Block, B>,
		import_block: BlockImportParams<Block, backend::TransactionFor<B, Block>>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
		storage_changes: Option<
			sc_consensus::StorageChanges<Block, backend::TransactionFor<B, Block>>,
		>,
	) -> sp_blockchain::Result<ImportResult>
	where
		Self: ProvideRuntimeApi<Block>,
		<Self as ProvideRuntimeApi<Block>>::Api:
			CoreApi<Block> + ApiExt<Block, StateBackend = B::State>,
	{
		let BlockImportParams {
			origin,
			header,
			justifications,
			post_digests,
			body,
			indexed_body,
			finalized,
			auxiliary,
			fork_choice,
			intermediates,
			import_existing,
			..
		} = import_block;

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
			justifications,
			body,
			indexed_body,
			storage_changes,
			new_cache,
			finalized,
			auxiliary,
			fork_choice,
			import_existing,
		);

		if let Ok(ImportResult::Imported(ref aux)) = result {
			if aux.is_new_best {
				// don't send telemetry block import events during initial sync for every
				// block to avoid spamming the telemetry server, these events will be randomly
				// sent at a rate of 1/10.
				if origin != BlockOrigin::NetworkInitialSync || rand::thread_rng().gen_bool(0.1) {
					telemetry!(
						self.telemetry;
						SUBSTRATE_INFO;
						"block.import";
						"height" => height,
						"best" => ?hash,
						"origin" => ?origin
					);
				}
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
		justifications: Option<Justifications>,
		body: Option<Vec<Block::Extrinsic>>,
		indexed_body: Option<Vec<Vec<u8>>>,
		storage_changes: Option<
			sc_consensus::StorageChanges<Block, backend::TransactionFor<B, Block>>,
		>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
		finalized: bool,
		aux: Vec<(Vec<u8>, Option<Vec<u8>>)>,
		fork_choice: ForkChoiceStrategy,
		import_existing: bool,
	) -> sp_blockchain::Result<ImportResult>
	where
		Self: ProvideRuntimeApi<Block>,
		<Self as ProvideRuntimeApi<Block>>::Api:
			CoreApi<Block> + ApiExt<Block, StateBackend = B::State>,
	{
		let parent_hash = *import_headers.post().parent_hash();
		let status = self.backend.blockchain().status(hash)?;
		let parent_exists =
			self.backend.blockchain().status(parent_hash)? == blockchain::BlockStatus::InChain;
		match (import_existing, status) {
			(false, blockchain::BlockStatus::InChain) => return Ok(ImportResult::AlreadyInChain),
			(false, blockchain::BlockStatus::Unknown) => {},
			(true, blockchain::BlockStatus::InChain) => {},
			(true, blockchain::BlockStatus::Unknown) => {},
		}

		let info = self.backend.blockchain().info();
		let gap_block = info
			.block_gap
			.map_or(false, |(start, _)| *import_headers.post().number() == start);

		assert!(justifications.is_some() && finalized || justifications.is_none() || gap_block);

		// the block is lower than our last finalized block so it must revert
		// finality, refusing import.
		if status == blockchain::BlockStatus::Unknown &&
			*import_headers.post().number() <= info.finalized_number &&
			!gap_block
		{
			return Err(sp_blockchain::Error::NotInFinalizedChain)
		}

		// this is a fairly arbitrary choice of where to draw the line on making notifications,
		// but the general goal is to only make notifications when we are already fully synced
		// and get a new chain head.
		let make_notifications = match origin {
			BlockOrigin::NetworkBroadcast | BlockOrigin::Own | BlockOrigin::ConsensusBroadcast =>
				true,
			BlockOrigin::Genesis | BlockOrigin::NetworkInitialSync | BlockOrigin::File => false,
		};

		let storage_changes = match storage_changes {
			Some(storage_changes) => {
				let storage_changes = match storage_changes {
					sc_consensus::StorageChanges::Changes(storage_changes) => {
						self.backend.begin_state_operation(&mut operation.op, parent_hash)?;
						let (main_sc, child_sc, offchain_sc, tx, _, tx_index) =
							storage_changes.into_inner();

						if self.config.offchain_indexing_api {
							operation.op.update_offchain_storage(offchain_sc)?;
						}

						operation.op.update_db_storage(tx)?;
						operation.op.update_storage(main_sc.clone(), child_sc.clone())?;
						operation.op.update_transaction_index(tx_index)?;

						Some((main_sc, child_sc))
					},
					sc_consensus::StorageChanges::Import(changes) => {
						let mut storage = sp_storage::Storage::default();
						for state in changes.state.0.into_iter() {
							if state.parent_storage_keys.is_empty() && state.state_root.is_empty() {
								for (key, value) in state.key_values.into_iter() {
									storage.top.insert(key, value);
								}
							} else {
								for parent_storage in state.parent_storage_keys {
									let storage_key = PrefixedStorageKey::new_ref(&parent_storage);
									let storage_key =
										match ChildType::from_prefixed_key(storage_key) {
											Some((ChildType::ParentKeyId, storage_key)) =>
												storage_key,
											None =>
												return Err(Error::Backend(
													"Invalid child storage key.".to_string(),
												)),
										};
									let entry = storage
										.children_default
										.entry(storage_key.to_vec())
										.or_insert_with(|| StorageChild {
											data: Default::default(),
											child_info: ChildInfo::new_default(storage_key),
										});
									for (key, value) in state.key_values.iter() {
										entry.data.insert(key.clone(), value.clone());
									}
								}
							}
						}

						// This is use by fast sync for runtime version to be resolvable from
						// changes.
						let state_version =
							resolve_state_version_from_wasm(&storage, &self.executor)?;
						let state_root = operation.op.reset_storage(storage, state_version)?;
						if state_root != *import_headers.post().state_root() {
							// State root mismatch when importing state. This should not happen in
							// safe fast sync mode, but may happen in unsafe mode.
							warn!("Error importing state: State root mismatch.");
							return Err(Error::InvalidStateRoot)
						}
						None
					},
				};

				operation.op.update_cache(new_cache);
				storage_changes
			},
			None => None,
		};

		// Ensure parent chain is finalized to maintain invariant that finality is called
		// sequentially.
		if finalized && parent_exists && info.finalized_hash != parent_hash {
			self.apply_finality_with_block_hash(
				operation,
				parent_hash,
				None,
				info.best_hash,
				make_notifications,
			)?;
		}

		let is_new_best = !gap_block &&
			(finalized ||
				match fork_choice {
					ForkChoiceStrategy::LongestChain =>
						import_headers.post().number() > &info.best_number,
					ForkChoiceStrategy::Custom(v) => v,
				});

		let leaf_state = if finalized {
			NewBlockState::Final
		} else if is_new_best {
			NewBlockState::Best
		} else {
			NewBlockState::Normal
		};

		let tree_route = if is_new_best && info.best_hash != parent_hash && parent_exists {
			let route_from_best =
				sp_blockchain::tree_route(self.backend.blockchain(), info.best_hash, parent_hash)?;
			Some(route_from_best)
		} else {
			None
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
			indexed_body,
			justifications,
			leaf_state,
		)?;

		operation.op.insert_aux(aux)?;

		// We only notify when we are already synced to the tip of the chain
		// or if this import triggers a re-org
		if make_notifications || tree_route.is_some() {
			let header = import_headers.into_post();
			if finalized {
				let mut summary = match operation.notify_finalized.take() {
					Some(mut summary) => {
						summary.header = header.clone();
						summary.finalized.push(hash);
						summary
					},
					None => FinalizeSummary {
						header: header.clone(),
						finalized: vec![hash],
						stale_heads: Vec::new(),
					},
				};

				if parent_exists {
					// Add to the stale list all heads that are branching from parent besides our
					// current `head`.
					for head in self
						.backend
						.blockchain()
						.leaves()?
						.into_iter()
						.filter(|h| *h != parent_hash)
					{
						let route_from_parent = sp_blockchain::tree_route(
							self.backend.blockchain(),
							parent_hash,
							head,
						)?;
						if route_from_parent.retracted().is_empty() {
							summary.stale_heads.push(head);
						}
					}
				}
				operation.notify_finalized = Some(summary);
			}

			operation.notify_imported = Some(ImportSummary {
				hash,
				origin,
				header,
				is_new_best,
				storage_changes,
				tree_route,
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
	) -> sp_blockchain::Result<PrepareStorageChangesResult<B, Block>>
	where
		Self: ProvideRuntimeApi<Block>,
		<Self as ProvideRuntimeApi<Block>>::Api:
			CoreApi<Block> + ApiExt<Block, StateBackend = B::State>,
	{
		let parent_hash = import_block.header.parent_hash();
		let state_action = std::mem::replace(&mut import_block.state_action, StateAction::Skip);
		let (enact_state, storage_changes) = match (self.block_status(*parent_hash)?, state_action)
		{
			(BlockStatus::KnownBad, _) =>
				return Ok(PrepareStorageChangesResult::Discard(ImportResult::KnownBad)),
			(
				BlockStatus::InChainPruned,
				StateAction::ApplyChanges(sc_consensus::StorageChanges::Changes(_)),
			) => return Ok(PrepareStorageChangesResult::Discard(ImportResult::MissingState)),
			(_, StateAction::ApplyChanges(changes)) => (true, Some(changes)),
			(BlockStatus::Unknown, _) =>
				return Ok(PrepareStorageChangesResult::Discard(ImportResult::UnknownParent)),
			(_, StateAction::Skip) => (false, None),
			(BlockStatus::InChainPruned, StateAction::Execute) =>
				return Ok(PrepareStorageChangesResult::Discard(ImportResult::MissingState)),
			(BlockStatus::InChainPruned, StateAction::ExecuteIfPossible) => (false, None),
			(_, StateAction::Execute) => (true, None),
			(_, StateAction::ExecuteIfPossible) => (true, None),
		};

		let storage_changes = match (enact_state, storage_changes, &import_block.body) {
			// We have storage changes and should enact the state, so we don't need to do anything
			// here
			(true, changes @ Some(_), _) => changes,
			// We should enact state, but don't have any storage changes, so we need to execute the
			// block.
			(true, None, Some(ref body)) => {
				let runtime_api = self.runtime_api();
				let execution_context = import_block.origin.into();

				runtime_api.execute_block_with_context(
					*parent_hash,
					execution_context,
					Block::new(import_block.header.clone(), body.clone()),
				)?;

				let state = self.backend.state_at(*parent_hash)?;
				let gen_storage_changes = runtime_api
					.into_storage_changes(&state, *parent_hash)
					.map_err(sp_blockchain::Error::Storage)?;

				if import_block.header.state_root() != &gen_storage_changes.transaction_storage_root
				{
					return Err(Error::InvalidStateRoot)
				}
				Some(sc_consensus::StorageChanges::Changes(gen_storage_changes))
			},
			// No block body, no storage changes
			(true, None, None) => None,
			// We should not enact the state, so we set the storage changes to `None`.
			(false, _, _) => None,
		};

		Ok(PrepareStorageChangesResult::Import(storage_changes))
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
			warn!(
				"Possible safety violation: attempted to re-finalize last finalized block {:?} ",
				last_finalized
			);
			return Ok(())
		}

		let route_from_finalized =
			sp_blockchain::tree_route(self.backend.blockchain(), last_finalized, block)?;

		if let Some(retracted) = route_from_finalized.retracted().get(0) {
			warn!(
				"Safety violation: attempted to revert finalized block {:?} which is not in the \
				same chain as last finalized {:?}",
				retracted, last_finalized
			);

			return Err(sp_blockchain::Error::NotInFinalizedChain)
		}

		let route_from_best =
			sp_blockchain::tree_route(self.backend.blockchain(), best_block, block)?;

		// if the block is not a direct ancestor of the current best chain,
		// then some other block is the common ancestor.
		if route_from_best.common_block().hash != block {
			// NOTE: we're setting the finalized block as best block, this might
			// be slightly inaccurate since we might have a "better" block
			// further along this chain, but since best chain selection logic is
			// plugable we cannot make a better choice here. usages that need
			// an accurate "best" block need to go through `SelectChain`
			// instead.
			operation.op.mark_head(block)?;
		}

		let enacted = route_from_finalized.enacted();
		assert!(enacted.len() > 0);
		for finalize_new in &enacted[..enacted.len() - 1] {
			operation.op.mark_finalized(finalize_new.hash, None)?;
		}

		assert_eq!(enacted.last().map(|e| e.hash), Some(block));
		operation.op.mark_finalized(block, justification)?;

		if notify {
			let finalized =
				route_from_finalized.enacted().iter().map(|elem| elem.hash).collect::<Vec<_>>();

			let block_number = route_from_finalized
				.last()
				.expect(
					"The block to finalize is always the latest \
						block in the route to the finalized block; qed",
				)
				.number;

			// The stale heads are the leaves that will be displaced after the
			// block is finalized.
			let stale_heads =
				self.backend.blockchain().displaced_leaves_after_finalizing(block_number)?;

			let header = self
				.backend
				.blockchain()
				.header(block)?
				.expect("Block to finalize expected to be onchain; qed");

			operation.notify_finalized = Some(FinalizeSummary { header, finalized, stale_heads });
		}

		Ok(())
	}

	fn notify_finalized(
		&self,
		notification: Option<FinalityNotification<Block>>,
	) -> sp_blockchain::Result<()> {
		let mut sinks = self.finality_notification_sinks.lock();

		let notification = match notification {
			Some(notify_finalized) => notify_finalized,
			None => {
				// Cleanup any closed finality notification sinks
				// since we won't be running the loop below which
				// would also remove any closed sinks.
				sinks.retain(|sink| !sink.is_closed());
				return Ok(())
			},
		};

		telemetry!(
			self.telemetry;
			SUBSTRATE_INFO;
			"notify.finalized";
			"height" => format!("{}", notification.header.number()),
			"best" => ?notification.hash,
		);

		sinks.retain(|sink| sink.unbounded_send(notification.clone()).is_ok());

		Ok(())
	}

	fn notify_imported(
		&self,
		notification: Option<BlockImportNotification<Block>>,
		storage_changes: Option<(StorageCollection, ChildStorageCollection)>,
	) -> sp_blockchain::Result<()> {
		let notification = match notification {
			Some(notify_import) => notify_import,
			None => {
				// Cleanup any closed import notification sinks since we won't
				// be sending any notifications below which would remove any
				// closed sinks. this is necessary since during initial sync we
				// won't send any import notifications which could lead to a
				// temporary leak of closed/discarded notification sinks (e.g.
				// from consensus code).
				self.import_notification_sinks.lock().retain(|sink| !sink.is_closed());
				return Ok(())
			},
		};

		if let Some(storage_changes) = storage_changes {
			// TODO [ToDr] How to handle re-orgs? Should we re-emit all storage changes?
			self.storage_notifications.trigger(
				&notification.hash,
				storage_changes.0.into_iter(),
				storage_changes.1.into_iter().map(|(sk, v)| (sk, v.into_iter())),
			);
		}

		self.import_notification_sinks
			.lock()
			.retain(|sink| sink.unbounded_send(notification.clone()).is_ok());

		Ok(())
	}

	/// Attempts to revert the chain by `n` blocks guaranteeing that no block is
	/// reverted past the last finalized block. Returns the number of blocks
	/// that were successfully reverted.
	pub fn revert(&self, n: NumberFor<Block>) -> sp_blockchain::Result<NumberFor<Block>> {
		let (number, _) = self.backend.revert(n, false)?;
		Ok(number)
	}

	/// Attempts to revert the chain by `n` blocks disregarding finality. This method will revert
	/// any finalized blocks as requested and can potentially leave the node in an inconsistent
	/// state. Other modules in the system that persist data and that rely on finality
	/// (e.g. consensus parts) will be unaffected by the revert. Use this method with caution and
	/// making sure that no other data needs to be reverted for consistency aside from the block
	/// data. If `blacklist` is set to true, will also blacklist reverted blocks from finalizing
	/// again. The blacklist is reset upon client restart.
	///
	/// Returns the number of blocks that were successfully reverted.
	pub fn unsafe_revert(
		&mut self,
		n: NumberFor<Block>,
		blacklist: bool,
	) -> sp_blockchain::Result<NumberFor<Block>> {
		let (number, reverted) = self.backend.revert(n, true)?;
		if blacklist {
			for b in reverted {
				self.block_rules.mark_bad(b);
			}
		}
		Ok(number)
	}

	/// Get blockchain info.
	pub fn chain_info(&self) -> blockchain::Info<Block> {
		self.backend.blockchain().info()
	}

	/// Get block status.
	pub fn block_status(&self, hash: Block::Hash) -> sp_blockchain::Result<BlockStatus> {
		// this can probably be implemented more efficiently
		if self
			.importing_block
			.read()
			.as_ref()
			.map_or(false, |importing| &hash == importing)
		{
			return Ok(BlockStatus::Queued)
		}

		let hash_and_number = self.backend.blockchain().number(hash)?.map(|n| (hash, n));
		match hash_and_number {
			Some((hash, number)) =>
				if self.backend.have_state_at(hash, number) {
					Ok(BlockStatus::InChainWithState)
				} else {
					Ok(BlockStatus::InChainPruned)
				},
			None => Ok(BlockStatus::Unknown),
		}
	}

	/// Get block header by id.
	pub fn header(
		&self,
		hash: Block::Hash,
	) -> sp_blockchain::Result<Option<<Block as BlockT>::Header>> {
		self.backend.blockchain().header(hash)
	}

	/// Get block body by id.
	pub fn body(
		&self,
		hash: Block::Hash,
	) -> sp_blockchain::Result<Option<Vec<<Block as BlockT>::Extrinsic>>> {
		self.backend.blockchain().body(hash)
	}

	/// Gets the uncles of the block with `target_hash` going back `max_generation` ancestors.
	pub fn uncles(
		&self,
		target_hash: Block::Hash,
		max_generation: NumberFor<Block>,
	) -> sp_blockchain::Result<Vec<Block::Hash>> {
		let load_header = |hash: Block::Hash| -> sp_blockchain::Result<Block::Header> {
			self.backend
				.blockchain()
				.header(hash)?
				.ok_or_else(|| Error::UnknownBlock(format!("{:?}", hash)))
		};

		let genesis_hash = self.backend.blockchain().info().genesis_hash;
		if genesis_hash == target_hash {
			return Ok(Vec::new())
		}

		let mut current_hash = target_hash;
		let mut current = load_header(current_hash)?;
		let mut ancestor_hash = *current.parent_hash();
		let mut ancestor = load_header(ancestor_hash)?;
		let mut uncles = Vec::new();

		let mut generation: NumberFor<Block> = Zero::zero();
		while generation < max_generation {
			let children = self.backend.blockchain().children(ancestor_hash)?;
			uncles.extend(children.into_iter().filter(|h| h != &current_hash));
			current_hash = ancestor_hash;

			if genesis_hash == current_hash {
				break
			}

			current = ancestor;
			ancestor_hash = *current.parent_hash();
			ancestor = load_header(ancestor_hash)?;
			generation += One::one();
		}
		trace!("Collected {} uncles", uncles.len());
		Ok(uncles)
	}
}

/// Return the genesis state version given the genesis storage and executor.
pub fn resolve_state_version_from_wasm<E>(
	storage: &Storage,
	executor: &E,
) -> sp_blockchain::Result<StateVersion>
where
	E: RuntimeVersionOf,
{
	if let Some(wasm) = storage.top.get(well_known_keys::CODE) {
		let mut ext = sp_state_machine::BasicExternalities::new_empty(); // just to read runtime version.

		let code_fetcher = sp_core::traits::WrappedRuntimeCode(wasm.as_slice().into());
		let runtime_code = sp_core::traits::RuntimeCode {
			code_fetcher: &code_fetcher,
			heap_pages: None,
			hash: {
				use std::hash::{Hash, Hasher};
				let mut state = DefaultHasher::new();
				wasm.hash(&mut state);
				state.finish().to_le_bytes().to_vec()
			},
		};
		let runtime_version = RuntimeVersionOf::runtime_version(executor, &mut ext, &runtime_code)
			.map_err(|e| sp_blockchain::Error::VersionInvalid(e.to_string()))?;
		Ok(runtime_version.state_version())
	} else {
		Err(sp_blockchain::Error::VersionInvalid(
			"Runtime missing from initial storage, could not read state version.".to_string(),
		))
	}
}

impl<B, E, Block, RA> UsageProvider<Block> for Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	/// Get usage info about current client.
	fn usage_info(&self) -> ClientInfo<Block> {
		ClientInfo { chain: self.chain_info(), usage: self.backend.usage_info() }
	}
}

impl<B, E, Block, RA> ProofProvider<Block> for Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	fn read_proof(
		&self,
		hash: Block::Hash,
		keys: &mut dyn Iterator<Item = &[u8]>,
	) -> sp_blockchain::Result<StorageProof> {
		self.state_at(hash)
			.and_then(|state| prove_read(state, keys).map_err(Into::into))
	}

	fn read_child_proof(
		&self,
		hash: Block::Hash,
		child_info: &ChildInfo,
		keys: &mut dyn Iterator<Item = &[u8]>,
	) -> sp_blockchain::Result<StorageProof> {
		self.state_at(hash)
			.and_then(|state| prove_child_read(state, child_info, keys).map_err(Into::into))
	}

	fn execution_proof(
		&self,
		hash: Block::Hash,
		method: &str,
		call_data: &[u8],
	) -> sp_blockchain::Result<(Vec<u8>, StorageProof)> {
		self.executor.prove_execution(hash, method, call_data)
	}

	fn read_proof_collection(
		&self,
		hash: Block::Hash,
		start_key: &[Vec<u8>],
		size_limit: usize,
	) -> sp_blockchain::Result<(CompactProof, u32)> {
		let state = self.state_at(hash)?;
		// this is a read proof, using version V0 or V1 is equivalent.
		let root = state.storage_root(std::iter::empty(), StateVersion::V0).0;

		let (proof, count) = prove_range_read_with_child_with_size::<_, HashFor<Block>>(
			state, size_limit, start_key,
		)?;
		let proof = proof
			.into_compact_proof::<HashFor<Block>>(root)
			.map_err(|e| sp_blockchain::Error::from_state(Box::new(e)))?;
		Ok((proof, count))
	}

	fn storage_collection(
		&self,
		hash: Block::Hash,
		start_key: &[Vec<u8>],
		size_limit: usize,
	) -> sp_blockchain::Result<Vec<(KeyValueStorageLevel, bool)>> {
		if start_key.len() > MAX_NESTED_TRIE_DEPTH {
			return Err(Error::Backend("Invalid start key.".to_string()))
		}
		let state = self.state_at(hash)?;
		let child_info = |storage_key: &Vec<u8>| -> sp_blockchain::Result<ChildInfo> {
			let storage_key = PrefixedStorageKey::new_ref(storage_key);
			match ChildType::from_prefixed_key(storage_key) {
				Some((ChildType::ParentKeyId, storage_key)) =>
					Ok(ChildInfo::new_default(storage_key)),
				None => Err(Error::Backend("Invalid child storage key.".to_string())),
			}
		};
		let mut current_child = if start_key.len() == 2 {
			let start_key = start_key.get(0).expect("checked len");
			if let Some(child_root) = state
				.storage(start_key)
				.map_err(|e| sp_blockchain::Error::from_state(Box::new(e)))?
			{
				Some((child_info(start_key)?, child_root))
			} else {
				return Err(Error::Backend("Invalid root start key.".to_string()))
			}
		} else {
			None
		};
		let mut current_key = start_key.last().map(Clone::clone).unwrap_or_default();
		let mut total_size = 0;
		let mut result = vec![(
			KeyValueStorageLevel {
				state_root: Vec::new(),
				key_values: Vec::new(),
				parent_storage_keys: Vec::new(),
			},
			false,
		)];

		let mut child_roots = HashSet::new();
		loop {
			let mut entries = Vec::new();
			let mut complete = true;
			let mut switch_child_key = None;
			while let Some(next_key) = if let Some(child) = current_child.as_ref() {
				state
					.next_child_storage_key(&child.0, &current_key)
					.map_err(|e| sp_blockchain::Error::from_state(Box::new(e)))?
			} else {
				state
					.next_storage_key(&current_key)
					.map_err(|e| sp_blockchain::Error::from_state(Box::new(e)))?
			} {
				let value = if let Some(child) = current_child.as_ref() {
					state
						.child_storage(&child.0, next_key.as_ref())
						.map_err(|e| sp_blockchain::Error::from_state(Box::new(e)))?
						.unwrap_or_default()
				} else {
					state
						.storage(next_key.as_ref())
						.map_err(|e| sp_blockchain::Error::from_state(Box::new(e)))?
						.unwrap_or_default()
				};
				let size = value.len() + next_key.len();
				if total_size + size > size_limit && !entries.is_empty() {
					complete = false;
					break
				}
				total_size += size;

				if current_child.is_none() &&
					sp_core::storage::well_known_keys::is_child_storage_key(next_key.as_slice()) &&
					!child_roots.contains(value.as_slice())
				{
					child_roots.insert(value.clone());
					switch_child_key = Some((next_key.clone(), value.clone()));
					entries.push((next_key.clone(), value));
					break
				}
				entries.push((next_key.clone(), value));
				current_key = next_key;
			}
			if let Some((child, child_root)) = switch_child_key.take() {
				result[0].0.key_values.extend(entries.into_iter());
				current_child = Some((child_info(&child)?, child_root));
				current_key = Vec::new();
			} else if let Some((child, child_root)) = current_child.take() {
				current_key = child.into_prefixed_storage_key().into_inner();
				result.push((
					KeyValueStorageLevel {
						state_root: child_root,
						key_values: entries,
						parent_storage_keys: Vec::new(),
					},
					complete,
				));
				if !complete {
					break
				}
			} else {
				result[0].0.key_values.extend(entries.into_iter());
				result[0].1 = complete;
				break
			}
		}
		Ok(result)
	}

	fn verify_range_proof(
		&self,
		root: Block::Hash,
		proof: CompactProof,
		start_key: &[Vec<u8>],
	) -> sp_blockchain::Result<(KeyValueStates, usize)> {
		let mut db = sp_state_machine::MemoryDB::<HashFor<Block>>::new(&[]);
		// Compact encoding
		let _ = sp_trie::decode_compact::<sp_state_machine::LayoutV0<HashFor<Block>>, _, _>(
			&mut db,
			proof.iter_compact_encoded_nodes(),
			Some(&root),
		)
		.map_err(|e| sp_blockchain::Error::from_state(Box::new(e)))?;
		let proving_backend = sp_state_machine::TrieBackendBuilder::new(db, root).build();
		let state = read_range_proof_check_with_child_on_proving_backend::<HashFor<Block>>(
			&proving_backend,
			start_key,
		)?;

		Ok(state)
	}
}

impl<B, E, Block, RA> BlockBuilderProvider<B, Block, Self> for Client<B, E, Block, RA>
where
	B: backend::Backend<Block> + Send + Sync + 'static,
	E: CallExecutor<Block> + Send + Sync + 'static,
	Block: BlockT,
	Self: ChainHeaderBackend<Block> + ProvideRuntimeApi<Block>,
	<Self as ProvideRuntimeApi<Block>>::Api:
		ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>> + BlockBuilderApi<Block>,
{
	fn new_block_at<R: Into<RecordProof>>(
		&self,
		parent: Block::Hash,
		inherent_digests: Digest,
		record_proof: R,
	) -> sp_blockchain::Result<sc_block_builder::BlockBuilder<Block, Self, B>> {
		sc_block_builder::BlockBuilder::new(
			self,
			parent,
			self.expect_block_number_from_id(&BlockId::Hash(parent))?,
			record_proof.into(),
			inherent_digests,
			&self.backend,
		)
	}

	fn new_block(
		&self,
		inherent_digests: Digest,
	) -> sp_blockchain::Result<sc_block_builder::BlockBuilder<Block, Self, B>> {
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
}

impl<B, E, Block, RA> ExecutorProvider<Block> for Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	type Executor = E;

	fn executor(&self) -> &Self::Executor {
		&self.executor
	}

	fn execution_extensions(&self) -> &ExecutionExtensions<Block> {
		self.executor.execution_extensions()
	}
}

impl<B, E, Block, RA> StorageProvider<Block, B> for Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	fn storage_keys(
		&self,
		hash: Block::Hash,
		key_prefix: &StorageKey,
	) -> sp_blockchain::Result<Vec<StorageKey>> {
		let keys = self.state_at(hash)?.keys(&key_prefix.0).into_iter().map(StorageKey).collect();
		Ok(keys)
	}

	fn storage_pairs(
		&self,
		hash: <Block as BlockT>::Hash,
		key_prefix: &StorageKey,
	) -> sp_blockchain::Result<Vec<(StorageKey, StorageData)>> {
		let state = self.state_at(hash)?;
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

	fn storage_keys_iter(
		&self,
		hash: <Block as BlockT>::Hash,
		prefix: Option<&StorageKey>,
		start_key: Option<&StorageKey>,
	) -> sp_blockchain::Result<KeyIterator<B::State, Block>> {
		let state = self.state_at(hash)?;
		let start_key = start_key.or(prefix).map(|key| key.0.clone()).unwrap_or_else(Vec::new);
		Ok(KeyIterator::new(state, prefix.cloned(), start_key))
	}

	fn child_storage_keys_iter(
		&self,
		hash: <Block as BlockT>::Hash,
		child_info: ChildInfo,
		prefix: Option<&StorageKey>,
		start_key: Option<&StorageKey>,
	) -> sp_blockchain::Result<KeyIterator<B::State, Block>> {
		let state = self.state_at(hash)?;
		let start_key = start_key.or(prefix).map(|key| key.0.clone()).unwrap_or_else(Vec::new);
		Ok(KeyIterator::new_child(state, child_info, prefix.cloned(), start_key))
	}

	fn storage(
		&self,
		hash: Block::Hash,
		key: &StorageKey,
	) -> sp_blockchain::Result<Option<StorageData>> {
		Ok(self
			.state_at(hash)?
			.storage(&key.0)
			.map_err(|e| sp_blockchain::Error::from_state(Box::new(e)))?
			.map(StorageData))
	}

	fn storage_hash(
		&self,
		hash: <Block as BlockT>::Hash,
		key: &StorageKey,
	) -> sp_blockchain::Result<Option<Block::Hash>> {
		self.state_at(hash)?
			.storage_hash(&key.0)
			.map_err(|e| sp_blockchain::Error::from_state(Box::new(e)))
	}

	fn child_storage_keys(
		&self,
		hash: <Block as BlockT>::Hash,
		child_info: &ChildInfo,
		key_prefix: &StorageKey,
	) -> sp_blockchain::Result<Vec<StorageKey>> {
		let keys = self
			.state_at(hash)?
			.child_keys(child_info, &key_prefix.0)
			.into_iter()
			.map(StorageKey)
			.collect();
		Ok(keys)
	}

	fn child_storage(
		&self,
		hash: <Block as BlockT>::Hash,
		child_info: &ChildInfo,
		key: &StorageKey,
	) -> sp_blockchain::Result<Option<StorageData>> {
		Ok(self
			.state_at(hash)?
			.child_storage(child_info, &key.0)
			.map_err(|e| sp_blockchain::Error::from_state(Box::new(e)))?
			.map(StorageData))
	}

	fn child_storage_hash(
		&self,
		hash: <Block as BlockT>::Hash,
		child_info: &ChildInfo,
		key: &StorageKey,
	) -> sp_blockchain::Result<Option<Block::Hash>> {
		self.state_at(hash)?
			.child_storage_hash(child_info, &key.0)
			.map_err(|e| sp_blockchain::Error::from_state(Box::new(e)))
	}
}

impl<B, E, Block, RA> HeaderMetadata<Block> for Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	type Error = sp_blockchain::Error;

	fn header_metadata(
		&self,
		hash: Block::Hash,
	) -> Result<CachedHeaderMetadata<Block>, Self::Error> {
		self.backend.blockchain().header_metadata(hash)
	}

	fn insert_header_metadata(&self, hash: Block::Hash, metadata: CachedHeaderMetadata<Block>) {
		self.backend.blockchain().insert_header_metadata(hash, metadata)
	}

	fn remove_header_metadata(&self, hash: Block::Hash) {
		self.backend.blockchain().remove_header_metadata(hash)
	}
}

impl<B, E, Block, RA> ProvideUncles<Block> for Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	fn uncles(
		&self,
		target_hash: Block::Hash,
		max_generation: NumberFor<Block>,
	) -> sp_blockchain::Result<Vec<Block::Header>> {
		Ok(Client::uncles(self, target_hash, max_generation)?
			.into_iter()
			.filter_map(|hash| Client::header(self, hash).unwrap_or(None))
			.collect())
	}
}

impl<B, E, Block, RA> ChainHeaderBackend<Block> for Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block> + Send + Sync,
	Block: BlockT,
	RA: Send + Sync,
{
	fn header(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<Block::Header>> {
		self.backend.blockchain().header(hash)
	}

	fn info(&self) -> blockchain::Info<Block> {
		self.backend.blockchain().info()
	}

	fn status(&self, hash: Block::Hash) -> sp_blockchain::Result<blockchain::BlockStatus> {
		self.backend.blockchain().status(hash)
	}

	fn number(
		&self,
		hash: Block::Hash,
	) -> sp_blockchain::Result<Option<<<Block as BlockT>::Header as HeaderT>::Number>> {
		self.backend.blockchain().number(hash)
	}

	fn hash(&self, number: NumberFor<Block>) -> sp_blockchain::Result<Option<Block::Hash>> {
		self.backend.blockchain().hash(number)
	}
}

impl<B, E, Block, RA> BlockIdTo<Block> for Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block> + Send + Sync,
	Block: BlockT,
	RA: Send + Sync,
{
	type Error = Error;

	fn to_hash(&self, block_id: &BlockId<Block>) -> sp_blockchain::Result<Option<Block::Hash>> {
		self.block_hash_from_id(block_id)
	}

	fn to_number(
		&self,
		block_id: &BlockId<Block>,
	) -> sp_blockchain::Result<Option<NumberFor<Block>>> {
		self.block_number_from_id(block_id)
	}
}

impl<B, E, Block, RA> ChainHeaderBackend<Block> for &Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block> + Send + Sync,
	Block: BlockT,
	RA: Send + Sync,
{
	fn header(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<Block::Header>> {
		self.backend.blockchain().header(hash)
	}

	fn info(&self) -> blockchain::Info<Block> {
		self.backend.blockchain().info()
	}

	fn status(&self, hash: Block::Hash) -> sp_blockchain::Result<blockchain::BlockStatus> {
		(**self).status(hash)
	}

	fn number(
		&self,
		hash: Block::Hash,
	) -> sp_blockchain::Result<Option<<<Block as BlockT>::Header as HeaderT>::Number>> {
		(**self).number(hash)
	}

	fn hash(&self, number: NumberFor<Block>) -> sp_blockchain::Result<Option<Block::Hash>> {
		(**self).hash(number)
	}
}

impl<B, E, Block, RA> ProvideRuntimeApi<Block> for Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block, Backend = B> + Send + Sync,
	Block: BlockT,
	RA: ConstructRuntimeApi<Block, Self> + Send + Sync,
{
	type Api = <RA as ConstructRuntimeApi<Block, Self>>::RuntimeApi;

	fn runtime_api(&self) -> ApiRef<Self::Api> {
		RA::construct_runtime_api(self)
	}
}

impl<B, E, Block, RA> CallApiAt<Block> for Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block, Backend = B> + Send + Sync,
	Block: BlockT,
	RA: Send + Sync,
{
	type StateBackend = B::State;

	fn call_api_at(
		&self,
		params: CallApiAtParams<Block, B::State>,
	) -> Result<Vec<u8>, sp_api::ApiError> {
		self.executor
			.contextual_call(
				params.at,
				params.function,
				&params.arguments,
				params.overlayed_changes,
				Some(params.storage_transaction_cache),
				params.recorder,
				params.context,
			)
			.map_err(Into::into)
	}

	fn runtime_version_at(&self, hash: Block::Hash) -> Result<RuntimeVersion, sp_api::ApiError> {
		CallExecutor::runtime_version(&self.executor, hash).map_err(Into::into)
	}

	fn state_at(&self, at: Block::Hash) -> Result<Self::StateBackend, sp_api::ApiError> {
		self.state_at(at).map_err(Into::into)
	}
}

/// NOTE: only use this implementation when you are sure there are NO consensus-level BlockImport
/// objects. Otherwise, importing blocks directly into the client would be bypassing
/// important verification work.
#[async_trait::async_trait]
impl<B, E, Block, RA> sc_consensus::BlockImport<Block> for &Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block> + Send + Sync,
	Block: BlockT,
	Client<B, E, Block, RA>: ProvideRuntimeApi<Block>,
	<Client<B, E, Block, RA> as ProvideRuntimeApi<Block>>::Api:
		CoreApi<Block> + ApiExt<Block, StateBackend = B::State>,
	RA: Sync + Send,
	backend::TransactionFor<B, Block>: Send + 'static,
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
	async fn import_block(
		&mut self,
		mut import_block: BlockImportParams<Block, backend::TransactionFor<B, Block>>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		let span = tracing::span!(tracing::Level::DEBUG, "import_block");
		let _enter = span.enter();

		let storage_changes =
			match self.prepare_block_storage_changes(&mut import_block).map_err(|e| {
				warn!("Block prepare storage changes error: {}", e);
				ConsensusError::ClientImport(e.to_string())
			})? {
				PrepareStorageChangesResult::Discard(res) => return Ok(res),
				PrepareStorageChangesResult::Import(storage_changes) => storage_changes,
			};

		self.lock_import_and_run(|operation| {
			self.apply_block(operation, import_block, new_cache, storage_changes)
		})
		.map_err(|e| {
			warn!("Block import error: {}", e);
			ConsensusError::ClientImport(e.to_string())
		})
	}

	/// Check block preconditions.
	async fn check_block(
		&mut self,
		block: BlockCheckParams<Block>,
	) -> Result<ImportResult, Self::Error> {
		let BlockCheckParams {
			hash,
			number,
			parent_hash,
			allow_missing_state,
			import_existing,
			allow_missing_parent,
		} = block;

		// Check the block against white and black lists if any are defined
		// (i.e. fork blocks and bad blocks respectively)
		match self.block_rules.lookup(number, &hash) {
			BlockLookupResult::KnownBad => {
				trace!("Rejecting known bad block: #{} {:?}", number, hash);
				return Ok(ImportResult::KnownBad)
			},
			BlockLookupResult::Expected(expected_hash) => {
				trace!(
					"Rejecting block from known invalid fork. Got {:?}, expected: {:?} at height {}",
					hash,
					expected_hash,
					number
				);
				return Ok(ImportResult::KnownBad)
			},
			BlockLookupResult::NotSpecial => {},
		}

		// Own status must be checked first. If the block and ancestry is pruned
		// this function must return `AlreadyInChain` rather than `MissingState`
		match self
			.block_status(hash)
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
		{
			BlockStatus::InChainWithState | BlockStatus::Queued =>
				return Ok(ImportResult::AlreadyInChain),
			BlockStatus::InChainPruned if !import_existing =>
				return Ok(ImportResult::AlreadyInChain),
			BlockStatus::InChainPruned => {},
			BlockStatus::Unknown => {},
			BlockStatus::KnownBad => return Ok(ImportResult::KnownBad),
		}

		match self
			.block_status(parent_hash)
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?
		{
			BlockStatus::InChainWithState | BlockStatus::Queued => {},
			BlockStatus::Unknown if allow_missing_parent => {},
			BlockStatus::Unknown => return Ok(ImportResult::UnknownParent),
			BlockStatus::InChainPruned if allow_missing_state => {},
			BlockStatus::InChainPruned => return Ok(ImportResult::MissingState),
			BlockStatus::KnownBad => return Ok(ImportResult::KnownBad),
		}

		Ok(ImportResult::imported(false))
	}
}

#[async_trait::async_trait]
impl<B, E, Block, RA> sc_consensus::BlockImport<Block> for Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block> + Send + Sync,
	Block: BlockT,
	Self: ProvideRuntimeApi<Block>,
	<Self as ProvideRuntimeApi<Block>>::Api:
		CoreApi<Block> + ApiExt<Block, StateBackend = B::State>,
	RA: Sync + Send,
	backend::TransactionFor<B, Block>: Send + 'static,
{
	type Error = ConsensusError;
	type Transaction = backend::TransactionFor<B, Block>;

	async fn import_block(
		&mut self,
		import_block: BlockImportParams<Block, Self::Transaction>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		(&*self).import_block(import_block, new_cache).await
	}

	async fn check_block(
		&mut self,
		block: BlockCheckParams<Block>,
	) -> Result<ImportResult, Self::Error> {
		(&*self).check_block(block).await
	}
}

impl<B, E, Block, RA> Finalizer<Block, B> for Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	fn apply_finality(
		&self,
		operation: &mut ClientImportOperation<Block, B>,
		hash: Block::Hash,
		justification: Option<Justification>,
		notify: bool,
	) -> sp_blockchain::Result<()> {
		let last_best = self.backend.blockchain().info().best_hash;
		self.apply_finality_with_block_hash(operation, hash, justification, last_best, notify)
	}

	fn finalize_block(
		&self,
		hash: Block::Hash,
		justification: Option<Justification>,
		notify: bool,
	) -> sp_blockchain::Result<()> {
		self.lock_import_and_run(|operation| {
			self.apply_finality(operation, hash, justification, notify)
		})
	}
}

impl<B, E, Block, RA> Finalizer<Block, B> for &Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	fn apply_finality(
		&self,
		operation: &mut ClientImportOperation<Block, B>,
		hash: Block::Hash,
		justification: Option<Justification>,
		notify: bool,
	) -> sp_blockchain::Result<()> {
		(**self).apply_finality(operation, hash, justification, notify)
	}

	fn finalize_block(
		&self,
		hash: Block::Hash,
		justification: Option<Justification>,
		notify: bool,
	) -> sp_blockchain::Result<()> {
		(**self).finalize_block(hash, justification, notify)
	}
}

impl<B, E, Block, RA> PreCommitActions<Block> for Client<B, E, Block, RA>
where
	Block: BlockT,
{
	fn register_import_action(&self, action: OnImportAction<Block>) {
		self.import_actions.lock().push(action);
	}

	fn register_finality_action(&self, action: OnFinalityAction<Block>) {
		self.finality_actions.lock().push(action);
	}
}

impl<B, E, Block, RA> BlockchainEvents<Block> for Client<B, E, Block, RA>
where
	E: CallExecutor<Block>,
	Block: BlockT,
{
	/// Get block import event stream.
	fn import_notification_stream(&self) -> ImportNotifications<Block> {
		let (sink, stream) = tracing_unbounded("mpsc_import_notification_stream", 100_000);
		self.import_notification_sinks.lock().push(sink);
		stream
	}

	fn finality_notification_stream(&self) -> FinalityNotifications<Block> {
		let (sink, stream) = tracing_unbounded("mpsc_finality_notification_stream", 100_000);
		self.finality_notification_sinks.lock().push(sink);
		stream
	}

	/// Get storage changes event stream.
	fn storage_changes_notification_stream(
		&self,
		filter_keys: Option<&[StorageKey]>,
		child_filter_keys: Option<&[(StorageKey, Option<Vec<StorageKey>>)]>,
	) -> sp_blockchain::Result<StorageEventStream<Block::Hash>> {
		Ok(self.storage_notifications.listen(filter_keys, child_filter_keys))
	}
}

impl<B, E, Block, RA> BlockBackend<Block> for Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
{
	fn block_body(
		&self,
		hash: Block::Hash,
	) -> sp_blockchain::Result<Option<Vec<<Block as BlockT>::Extrinsic>>> {
		self.body(hash)
	}

	fn block(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<SignedBlock<Block>>> {
		Ok(match (self.header(hash)?, self.body(hash)?, self.justifications(hash)?) {
			(Some(header), Some(extrinsics), justifications) =>
				Some(SignedBlock { block: Block::new(header, extrinsics), justifications }),
			_ => None,
		})
	}

	fn block_status(&self, hash: Block::Hash) -> sp_blockchain::Result<BlockStatus> {
		Client::block_status(self, hash)
	}

	fn justifications(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<Justifications>> {
		self.backend.blockchain().justifications(hash)
	}

	fn block_hash(&self, number: NumberFor<Block>) -> sp_blockchain::Result<Option<Block::Hash>> {
		self.backend.blockchain().hash(number)
	}

	fn indexed_transaction(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<Vec<u8>>> {
		self.backend.blockchain().indexed_transaction(hash)
	}

	fn has_indexed_transaction(&self, hash: Block::Hash) -> sp_blockchain::Result<bool> {
		self.backend.blockchain().has_indexed_transaction(hash)
	}

	fn block_indexed_body(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<Vec<Vec<u8>>>> {
		self.backend.blockchain().block_indexed_body(hash)
	}

	fn requires_full_sync(&self) -> bool {
		self.backend.requires_full_sync()
	}
}

impl<B, E, Block, RA> backend::AuxStore for Client<B, E, Block, RA>
where
	B: backend::Backend<Block>,
	E: CallExecutor<Block>,
	Block: BlockT,
	Self: ProvideRuntimeApi<Block>,
	<Self as ProvideRuntimeApi<Block>>::Api: CoreApi<Block>,
{
	/// Insert auxiliary data into key-value store.
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item = &'a (&'c [u8], &'c [u8])>,
		D: IntoIterator<Item = &'a &'b [u8]>,
	>(
		&self,
		insert: I,
		delete: D,
	) -> sp_blockchain::Result<()> {
		// Import is locked here because we may have other block import
		// operations that tries to set aux data. Note that for consensus
		// layer, one can always use atomic operations to make sure
		// import is only locked once.
		self.lock_import_and_run(|operation| apply_aux(operation, insert, delete))
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
	<Client<B, E, Block, RA> as ProvideRuntimeApi<Block>>::Api: CoreApi<Block>,
{
	fn insert_aux<
		'a,
		'b: 'a,
		'c: 'a,
		I: IntoIterator<Item = &'a (&'c [u8], &'c [u8])>,
		D: IntoIterator<Item = &'a &'b [u8]>,
	>(
		&self,
		insert: I,
		delete: D,
	) -> sp_blockchain::Result<()> {
		(**self).insert_aux(insert, delete)
	}

	fn get_aux(&self, key: &[u8]) -> sp_blockchain::Result<Option<Vec<u8>>> {
		(**self).get_aux(key)
	}
}

impl<BE, E, B, RA> sp_consensus::block_validation::Chain<B> for Client<BE, E, B, RA>
where
	BE: backend::Backend<B>,
	E: CallExecutor<B>,
	B: BlockT,
{
	fn block_status(
		&self,
		hash: B::Hash,
	) -> Result<BlockStatus, Box<dyn std::error::Error + Send>> {
		Client::block_status(self, hash).map_err(|e| Box::new(e) as Box<_>)
	}
}

impl<BE, E, B, RA> sp_transaction_storage_proof::IndexedBody<B> for Client<BE, E, B, RA>
where
	BE: backend::Backend<B>,
	E: CallExecutor<B>,
	B: BlockT,
{
	fn block_indexed_body(
		&self,
		number: NumberFor<B>,
	) -> Result<Option<Vec<Vec<u8>>>, sp_transaction_storage_proof::Error> {
		let hash = match self
			.backend
			.blockchain()
			.block_hash_from_id(&BlockId::Number(number))
			.map_err(|e| sp_transaction_storage_proof::Error::Application(Box::new(e)))?
		{
			Some(hash) => hash,
			None => return Ok(None),
		};

		self.backend
			.blockchain()
			.block_indexed_body(hash)
			.map_err(|e| sp_transaction_storage_proof::Error::Application(Box::new(e)))
	}

	fn number(
		&self,
		hash: B::Hash,
	) -> Result<Option<NumberFor<B>>, sp_transaction_storage_proof::Error> {
		self.backend
			.blockchain()
			.number(hash)
			.map_err(|e| sp_transaction_storage_proof::Error::Application(Box::new(e)))
	}
}
