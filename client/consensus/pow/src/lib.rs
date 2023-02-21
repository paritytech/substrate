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

//! Proof of work consensus for Substrate.
//!
//! To use this engine, you can need to have a struct that implements
//! [`PowAlgorithm`]. After that, pass an instance of the struct, along
//! with other necessary client references to [`import_queue`] to setup
//! the queue.
//!
//! This library also comes with an async mining worker, which can be
//! started via the [`start_mining_worker`] function. It returns a worker
//! handle together with a future. The future must be pulled. Through
//! the worker handle, you can pull the metadata needed to start the
//! mining process via [`MiningHandle::metadata`], and then do the actual
//! mining on a standalone thread. Finally, when a seal is found, call
//! [`MiningHandle::submit`] to build the block.
//!
//! The auxiliary storage for PoW engine only stores the total difficulty.
//! For other storage requirements for particular PoW algorithm (such as
//! the actual difficulty for each particular blocks), you can take a client
//! reference in your [`PowAlgorithm`] implementation, and use a separate prefix
//! for the auxiliary storage. It is also possible to just use the runtime
//! as the storage, but it is not recommended as it won't work well with light
//! clients.

mod worker;

pub use crate::worker::{MiningBuild, MiningHandle, MiningMetadata};

use crate::worker::UntilImportedOrTimeout;
use codec::{Decode, Encode};
use futures::{Future, StreamExt};
use log::*;
use prometheus_endpoint::Registry;
use sc_client_api::{self, backend::AuxStore, BlockOf, BlockchainEvents};
use sc_consensus::{
	BasicQueue, BlockCheckParams, BlockImport, BlockImportParams, BoxBlockImport,
	BoxJustificationImport, ForkChoiceStrategy, ImportResult, Verifier,
};
use sp_api::ProvideRuntimeApi;
use sp_block_builder::BlockBuilder as BlockBuilderApi;
use sp_blockchain::{well_known_cache_keys::Id as CacheKeyId, HeaderBackend};
use sp_consensus::{Environment, Error as ConsensusError, Proposer, SelectChain, SyncOracle};
use sp_consensus_pow::{Seal, TotalDifficulty, POW_ENGINE_ID};
use sp_core::ExecutionContext;
use sp_inherents::{CreateInherentDataProviders, InherentDataProvider};
use sp_runtime::{
	generic::{BlockId, Digest, DigestItem},
	traits::{Block as BlockT, Header as HeaderT},
	RuntimeString,
};
use std::{cmp::Ordering, collections::HashMap, marker::PhantomData, sync::Arc, time::Duration};

const LOG_TARGET: &str = "pow";

#[derive(Debug, thiserror::Error)]
pub enum Error<B: BlockT> {
	#[error("Header uses the wrong engine {0:?}")]
	WrongEngine([u8; 4]),
	#[error("Header {0:?} is unsealed")]
	HeaderUnsealed(B::Hash),
	#[error("PoW validation error: invalid seal")]
	InvalidSeal,
	#[error("PoW validation error: preliminary verification failed")]
	FailedPreliminaryVerify,
	#[error("Rejecting block too far in future")]
	TooFarInFuture,
	#[error("Fetching best header failed using select chain: {0}")]
	BestHeaderSelectChain(ConsensusError),
	#[error("Fetching best header failed: {0}")]
	BestHeader(sp_blockchain::Error),
	#[error("Best header does not exist")]
	NoBestHeader,
	#[error("Block proposing error: {0}")]
	BlockProposingError(String),
	#[error("Fetch best hash failed via select chain: {0}")]
	BestHashSelectChain(ConsensusError),
	#[error("Error with block built on {0:?}: {1}")]
	BlockBuiltError(B::Hash, ConsensusError),
	#[error("Creating inherents failed: {0}")]
	CreateInherents(sp_inherents::Error),
	#[error("Checking inherents failed: {0}")]
	CheckInherents(sp_inherents::Error),
	#[error(
		"Checking inherents unknown error for identifier: {}",
		String::from_utf8_lossy(.0)
	)]
	CheckInherentsUnknownError(sp_inherents::InherentIdentifier),
	#[error("Multiple pre-runtime digests")]
	MultiplePreRuntimeDigests,
	#[error(transparent)]
	Client(sp_blockchain::Error),
	#[error(transparent)]
	Codec(codec::Error),
	#[error("{0}")]
	Environment(String),
	#[error("{0}")]
	Runtime(RuntimeString),
	#[error("{0}")]
	Other(String),
}

impl<B: BlockT> From<Error<B>> for String {
	fn from(error: Error<B>) -> String {
		error.to_string()
	}
}

impl<B: BlockT> From<Error<B>> for ConsensusError {
	fn from(error: Error<B>) -> ConsensusError {
		ConsensusError::ClientImport(error.to_string())
	}
}

/// Auxiliary storage prefix for PoW engine.
pub const POW_AUX_PREFIX: [u8; 4] = *b"PoW:";

/// Get the auxiliary storage key used by engine to store total difficulty.
fn aux_key<T: AsRef<[u8]>>(hash: &T) -> Vec<u8> {
	POW_AUX_PREFIX.iter().chain(hash.as_ref()).copied().collect()
}

/// Intermediate value passed to block importer.
#[derive(Encode, Decode, Clone, Debug, Default)]
pub struct PowIntermediate<Difficulty> {
	/// Difficulty of the block, if known.
	pub difficulty: Option<Difficulty>,
}

/// Intermediate key for PoW engine.
pub static INTERMEDIATE_KEY: &[u8] = b"pow1";

/// Auxiliary storage data for PoW.
#[derive(Encode, Decode, Clone, Debug, Default)]
pub struct PowAux<Difficulty> {
	/// Difficulty of the current block.
	pub difficulty: Difficulty,
	/// Total difficulty up to current block.
	pub total_difficulty: Difficulty,
}

impl<Difficulty> PowAux<Difficulty>
where
	Difficulty: Decode + Default,
{
	/// Read the auxiliary from client.
	pub fn read<C: AuxStore, B: BlockT>(client: &C, hash: &B::Hash) -> Result<Self, Error<B>> {
		let key = aux_key(&hash);

		match client.get_aux(&key).map_err(Error::Client)? {
			Some(bytes) => Self::decode(&mut &bytes[..]).map_err(Error::Codec),
			None => Ok(Self::default()),
		}
	}
}

/// Algorithm used for proof of work.
pub trait PowAlgorithm<B: BlockT> {
	/// Difficulty for the algorithm.
	type Difficulty: TotalDifficulty + Default + Encode + Decode + Ord + Clone + Copy;

	/// Get the next block's difficulty.
	///
	/// This function will be called twice during the import process, so the implementation
	/// should be properly cached.
	fn difficulty(&self, parent: B::Hash) -> Result<Self::Difficulty, Error<B>>;
	/// Verify that the seal is valid against given pre hash when parent block is not yet imported.
	///
	/// None means that preliminary verify is not available for this algorithm.
	fn preliminary_verify(
		&self,
		_pre_hash: &B::Hash,
		_seal: &Seal,
	) -> Result<Option<bool>, Error<B>> {
		Ok(None)
	}
	/// Break a fork choice tie.
	///
	/// By default this chooses the earliest block seen. Using uniform tie
	/// breaking algorithms will help to protect against selfish mining.
	///
	/// Returns if the new seal should be considered best block.
	fn break_tie(&self, _own_seal: &Seal, _new_seal: &Seal) -> bool {
		false
	}
	/// Verify that the difficulty is valid against given seal.
	fn verify(
		&self,
		parent: &BlockId<B>,
		pre_hash: &B::Hash,
		pre_digest: Option<&[u8]>,
		seal: &Seal,
		difficulty: Self::Difficulty,
	) -> Result<bool, Error<B>>;
}

/// A block importer for PoW.
pub struct PowBlockImport<B: BlockT, I, C, S, Algorithm, CIDP> {
	algorithm: Algorithm,
	inner: I,
	select_chain: S,
	client: Arc<C>,
	create_inherent_data_providers: Arc<CIDP>,
	check_inherents_after: <<B as BlockT>::Header as HeaderT>::Number,
}

impl<B: BlockT, I: Clone, C, S: Clone, Algorithm: Clone, CIDP> Clone
	for PowBlockImport<B, I, C, S, Algorithm, CIDP>
{
	fn clone(&self) -> Self {
		Self {
			algorithm: self.algorithm.clone(),
			inner: self.inner.clone(),
			select_chain: self.select_chain.clone(),
			client: self.client.clone(),
			create_inherent_data_providers: self.create_inherent_data_providers.clone(),
			check_inherents_after: self.check_inherents_after,
		}
	}
}

impl<B, I, C, S, Algorithm, CIDP> PowBlockImport<B, I, C, S, Algorithm, CIDP>
where
	B: BlockT,
	I: BlockImport<B, Transaction = sp_api::TransactionFor<C, B>> + Send + Sync,
	I::Error: Into<ConsensusError>,
	C: ProvideRuntimeApi<B> + Send + Sync + HeaderBackend<B> + AuxStore + BlockOf,
	C::Api: BlockBuilderApi<B>,
	Algorithm: PowAlgorithm<B>,
	CIDP: CreateInherentDataProviders<B, ()>,
{
	/// Create a new block import suitable to be used in PoW
	pub fn new(
		inner: I,
		client: Arc<C>,
		algorithm: Algorithm,
		check_inherents_after: <<B as BlockT>::Header as HeaderT>::Number,
		select_chain: S,
		create_inherent_data_providers: CIDP,
	) -> Self {
		Self {
			inner,
			client,
			algorithm,
			check_inherents_after,
			select_chain,
			create_inherent_data_providers: Arc::new(create_inherent_data_providers),
		}
	}

	async fn check_inherents(
		&self,
		block: B,
		at_hash: B::Hash,
		inherent_data_providers: CIDP::InherentDataProviders,
		execution_context: ExecutionContext,
	) -> Result<(), Error<B>> {
		if *block.header().number() < self.check_inherents_after {
			return Ok(())
		}

		let inherent_data = inherent_data_providers
			.create_inherent_data()
			.await
			.map_err(|e| Error::CreateInherents(e))?;

		let inherent_res = self
			.client
			.runtime_api()
			.check_inherents_with_context(at_hash, execution_context, block, inherent_data)
			.map_err(|e| Error::Client(e.into()))?;

		if !inherent_res.ok() {
			for (identifier, error) in inherent_res.into_errors() {
				match inherent_data_providers.try_handle_error(&identifier, &error).await {
					Some(res) => res.map_err(Error::CheckInherents)?,
					None => return Err(Error::CheckInherentsUnknownError(identifier)),
				}
			}
		}

		Ok(())
	}
}

#[async_trait::async_trait]
impl<B, I, C, S, Algorithm, CIDP> BlockImport<B> for PowBlockImport<B, I, C, S, Algorithm, CIDP>
where
	B: BlockT,
	I: BlockImport<B, Transaction = sp_api::TransactionFor<C, B>> + Send + Sync,
	I::Error: Into<ConsensusError>,
	S: SelectChain<B>,
	C: ProvideRuntimeApi<B> + Send + Sync + HeaderBackend<B> + AuxStore + BlockOf,
	C::Api: BlockBuilderApi<B>,
	Algorithm: PowAlgorithm<B> + Send + Sync,
	Algorithm::Difficulty: 'static + Send,
	CIDP: CreateInherentDataProviders<B, ()> + Send + Sync,
{
	type Error = ConsensusError;
	type Transaction = sp_api::TransactionFor<C, B>;

	async fn check_block(
		&mut self,
		block: BlockCheckParams<B>,
	) -> Result<ImportResult, Self::Error> {
		self.inner.check_block(block).await.map_err(Into::into)
	}

	async fn import_block(
		&mut self,
		mut block: BlockImportParams<B, Self::Transaction>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		let best_header = self
			.select_chain
			.best_chain()
			.await
			.map_err(|e| format!("Fetch best chain failed via select chain: {}", e))?;
		let best_hash = best_header.hash();

		let parent_hash = *block.header.parent_hash();
		let best_aux = PowAux::read::<_, B>(self.client.as_ref(), &best_hash)?;
		let mut aux = PowAux::read::<_, B>(self.client.as_ref(), &parent_hash)?;

		if let Some(inner_body) = block.body.take() {
			let check_block = B::new(block.header.clone(), inner_body);

			if !block.state_action.skip_execution_checks() {
				self.check_inherents(
					check_block.clone(),
					parent_hash,
					self.create_inherent_data_providers
						.create_inherent_data_providers(parent_hash, ())
						.await?,
					block.origin.into(),
				)
				.await?;
			}

			block.body = Some(check_block.deconstruct().1);
		}

		let inner_seal = fetch_seal::<B>(block.post_digests.last(), block.header.hash())?;

		let intermediate = block
			.remove_intermediate::<PowIntermediate<Algorithm::Difficulty>>(INTERMEDIATE_KEY)?;

		let difficulty = match intermediate.difficulty {
			Some(difficulty) => difficulty,
			None => self.algorithm.difficulty(parent_hash)?,
		};

		let pre_hash = block.header.hash();
		let pre_digest = find_pre_digest::<B>(&block.header)?;
		if !self.algorithm.verify(
			&BlockId::hash(parent_hash),
			&pre_hash,
			pre_digest.as_ref().map(|v| &v[..]),
			&inner_seal,
			difficulty,
		)? {
			return Err(Error::<B>::InvalidSeal.into())
		}

		aux.difficulty = difficulty;
		aux.total_difficulty.increment(difficulty);

		let key = aux_key(&block.post_hash());
		block.auxiliary.push((key, Some(aux.encode())));
		if block.fork_choice.is_none() {
			block.fork_choice = Some(ForkChoiceStrategy::Custom(
				match aux.total_difficulty.cmp(&best_aux.total_difficulty) {
					Ordering::Less => false,
					Ordering::Greater => true,
					Ordering::Equal => {
						let best_inner_seal =
							fetch_seal::<B>(best_header.digest().logs.last(), best_hash)?;

						self.algorithm.break_tie(&best_inner_seal, &inner_seal)
					},
				},
			));
		}

		self.inner.import_block(block, new_cache).await.map_err(Into::into)
	}
}

/// A verifier for PoW blocks.
pub struct PowVerifier<B: BlockT, Algorithm> {
	algorithm: Algorithm,
	_marker: PhantomData<B>,
}

impl<B: BlockT, Algorithm> PowVerifier<B, Algorithm> {
	pub fn new(algorithm: Algorithm) -> Self {
		Self { algorithm, _marker: PhantomData }
	}

	fn check_header(&self, mut header: B::Header) -> Result<(B::Header, DigestItem), Error<B>>
	where
		Algorithm: PowAlgorithm<B>,
	{
		let hash = header.hash();

		let (seal, inner_seal) = match header.digest_mut().pop() {
			Some(DigestItem::Seal(id, seal)) =>
				if id == POW_ENGINE_ID {
					(DigestItem::Seal(id, seal.clone()), seal)
				} else {
					return Err(Error::WrongEngine(id))
				},
			_ => return Err(Error::HeaderUnsealed(hash)),
		};

		let pre_hash = header.hash();

		if !self.algorithm.preliminary_verify(&pre_hash, &inner_seal)?.unwrap_or(true) {
			return Err(Error::FailedPreliminaryVerify)
		}

		Ok((header, seal))
	}
}

#[async_trait::async_trait]
impl<B: BlockT, Algorithm> Verifier<B> for PowVerifier<B, Algorithm>
where
	Algorithm: PowAlgorithm<B> + Send + Sync,
	Algorithm::Difficulty: 'static + Send,
{
	async fn verify(
		&mut self,
		mut block: BlockImportParams<B, ()>,
	) -> Result<(BlockImportParams<B, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		let hash = block.header.hash();
		let (checked_header, seal) = self.check_header(block.header)?;

		let intermediate = PowIntermediate::<Algorithm::Difficulty> { difficulty: None };
		block.header = checked_header;
		block.post_digests.push(seal);
		block.insert_intermediate(INTERMEDIATE_KEY, intermediate);
		block.post_hash = Some(hash);

		Ok((block, None))
	}
}

/// The PoW import queue type.
pub type PowImportQueue<B, Transaction> = BasicQueue<B, Transaction>;

/// Import queue for PoW engine.
pub fn import_queue<B, Transaction, Algorithm>(
	block_import: BoxBlockImport<B, Transaction>,
	justification_import: Option<BoxJustificationImport<B>>,
	algorithm: Algorithm,
	spawner: &impl sp_core::traits::SpawnEssentialNamed,
	registry: Option<&Registry>,
) -> Result<PowImportQueue<B, Transaction>, sp_consensus::Error>
where
	B: BlockT,
	Transaction: Send + Sync + 'static,
	Algorithm: PowAlgorithm<B> + Clone + Send + Sync + 'static,
	Algorithm::Difficulty: Send,
{
	let verifier = PowVerifier::new(algorithm);

	Ok(BasicQueue::new(verifier, block_import, justification_import, spawner, registry))
}

/// Start the mining worker for PoW. This function provides the necessary helper functions that can
/// be used to implement a miner. However, it does not do the CPU-intensive mining itself.
///
/// Two values are returned -- a worker, which contains functions that allows querying the current
/// mining metadata and submitting mined blocks, and a future, which must be polled to fill in
/// information in the worker.
///
/// `pre_runtime` is a parameter that allows a custom additional pre-runtime digest to be inserted
/// for blocks being built. This can encode authorship information, or just be a graffiti.
pub fn start_mining_worker<Block, C, S, Algorithm, E, SO, L, CIDP>(
	block_import: BoxBlockImport<Block, sp_api::TransactionFor<C, Block>>,
	client: Arc<C>,
	select_chain: S,
	algorithm: Algorithm,
	mut env: E,
	sync_oracle: SO,
	justification_sync_link: L,
	pre_runtime: Option<Vec<u8>>,
	create_inherent_data_providers: CIDP,
	timeout: Duration,
	build_time: Duration,
) -> (
	MiningHandle<Block, Algorithm, C, L, <E::Proposer as Proposer<Block>>::Proof>,
	impl Future<Output = ()>,
)
where
	Block: BlockT,
	C: ProvideRuntimeApi<Block> + BlockchainEvents<Block> + 'static,
	S: SelectChain<Block> + 'static,
	Algorithm: PowAlgorithm<Block> + Clone,
	Algorithm::Difficulty: Send + 'static,
	E: Environment<Block> + Send + Sync + 'static,
	E::Error: std::fmt::Debug,
	E::Proposer: Proposer<Block, Transaction = sp_api::TransactionFor<C, Block>>,
	SO: SyncOracle + Clone + Send + Sync + 'static,
	L: sc_consensus::JustificationSyncLink<Block>,
	CIDP: CreateInherentDataProviders<Block, ()>,
{
	let mut timer = UntilImportedOrTimeout::new(client.import_notification_stream(), timeout);
	let worker = MiningHandle::new(algorithm.clone(), block_import, justification_sync_link);
	let worker_ret = worker.clone();

	let task = async move {
		loop {
			if timer.next().await.is_none() {
				break
			}

			if sync_oracle.is_major_syncing() {
				debug!(target: LOG_TARGET, "Skipping proposal due to sync.");
				worker.on_major_syncing();
				continue
			}

			let best_header = match select_chain.best_chain().await {
				Ok(x) => x,
				Err(err) => {
					warn!(
						target: LOG_TARGET,
						"Unable to pull new block for authoring. \
						 Select best chain error: {}",
						err
					);
					continue
				},
			};
			let best_hash = best_header.hash();

			if worker.best_hash() == Some(best_hash) {
				continue
			}

			// The worker is locked for the duration of the whole proposing period. Within this
			// period, the mining target is outdated and useless anyway.

			let difficulty = match algorithm.difficulty(best_hash) {
				Ok(x) => x,
				Err(err) => {
					warn!(
						target: LOG_TARGET,
						"Unable to propose new block for authoring. \
						 Fetch difficulty failed: {}",
						err,
					);
					continue
				},
			};

			let inherent_data_providers = match create_inherent_data_providers
				.create_inherent_data_providers(best_hash, ())
				.await
			{
				Ok(x) => x,
				Err(err) => {
					warn!(
						target: LOG_TARGET,
						"Unable to propose new block for authoring. \
						 Creating inherent data providers failed: {}",
						err,
					);
					continue
				},
			};

			let inherent_data = match inherent_data_providers.create_inherent_data().await {
				Ok(r) => r,
				Err(e) => {
					warn!(
						target: LOG_TARGET,
						"Unable to propose new block for authoring. \
						 Creating inherent data failed: {}",
						e,
					);
					continue
				},
			};

			let mut inherent_digest = Digest::default();
			if let Some(pre_runtime) = &pre_runtime {
				inherent_digest.push(DigestItem::PreRuntime(POW_ENGINE_ID, pre_runtime.to_vec()));
			}

			let pre_runtime = pre_runtime.clone();

			let proposer = match env.init(&best_header).await {
				Ok(x) => x,
				Err(err) => {
					warn!(
						target: LOG_TARGET,
						"Unable to propose new block for authoring. \
						 Creating proposer failed: {:?}",
						err,
					);
					continue
				},
			};

			let proposal =
				match proposer.propose(inherent_data, inherent_digest, build_time, None).await {
					Ok(x) => x,
					Err(err) => {
						warn!(
							target: LOG_TARGET,
							"Unable to propose new block for authoring. \
							 Creating proposal failed: {}",
							err,
						);
						continue
					},
				};

			let build = MiningBuild::<Block, Algorithm, C, _> {
				metadata: MiningMetadata {
					best_hash,
					pre_hash: proposal.block.header().hash(),
					pre_runtime: pre_runtime.clone(),
					difficulty,
				},
				proposal,
			};

			worker.on_build(build);
		}
	};

	(worker_ret, task)
}

/// Find PoW pre-runtime.
fn find_pre_digest<B: BlockT>(header: &B::Header) -> Result<Option<Vec<u8>>, Error<B>> {
	let mut pre_digest: Option<_> = None;
	for log in header.digest().logs() {
		trace!(target: LOG_TARGET, "Checking log {:?}, looking for pre runtime digest", log);
		match (log, pre_digest.is_some()) {
			(DigestItem::PreRuntime(POW_ENGINE_ID, _), true) =>
				return Err(Error::MultiplePreRuntimeDigests),
			(DigestItem::PreRuntime(POW_ENGINE_ID, v), false) => {
				pre_digest = Some(v.clone());
			},
			(_, _) => trace!(target: LOG_TARGET, "Ignoring digest not meant for us"),
		}
	}

	Ok(pre_digest)
}

/// Fetch PoW seal.
fn fetch_seal<B: BlockT>(digest: Option<&DigestItem>, hash: B::Hash) -> Result<Vec<u8>, Error<B>> {
	match digest {
		Some(DigestItem::Seal(id, seal)) =>
			if id == &POW_ENGINE_ID {
				Ok(seal.clone())
			} else {
				Err(Error::<B>::WrongEngine(*id))
			},
		_ => Err(Error::<B>::HeaderUnsealed(hash)),
	}
}
