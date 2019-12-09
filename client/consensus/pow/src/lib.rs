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

//! Proof of work consensus for Substrate.
//!
//! To use this engine, you can need to have a struct that implements
//! `PowAlgorithm`. After that, pass an instance of the struct, along
//! with other necessary client references to `import_queue` to setup
//! the queue. Use the `start_mine` function for basic CPU mining.
//!
//! The auxiliary storage for PoW engine only stores the total difficulty.
//! For other storage requirements for particular PoW algorithm (such as
//! the actual difficulty for each particular blocks), you can take a client
//! reference in your `PowAlgorithm` implementation, and use a separate prefix
//! for the auxiliary storage. It is also possible to just use the runtime
//! as the storage, but it is not recommended as it won't work well with light
//! clients.

use std::sync::Arc;
use std::thread;
use std::collections::HashMap;
use client_api::{BlockOf, backend::AuxStore};
use sp_blockchain::{HeaderBackend, ProvideCache, well_known_cache_keys::Id as CacheKeyId};
use block_builder_api::BlockBuilder as BlockBuilderApi;
use sp_runtime::{Justification, RuntimeString};
use sp_runtime::generic::{BlockId, Digest, DigestItem};
use sp_runtime::traits::{Block as BlockT, Header as HeaderT, ProvideRuntimeApi};
use sp_timestamp::{TimestampInherentData, InherentError as TIError};
use pow_primitives::{Seal, TotalDifficulty, POW_ENGINE_ID};
use primitives::H256;
use inherents::{InherentDataProviders, InherentData};
use consensus_common::{
	BlockImportParams, BlockOrigin, ForkChoiceStrategy, SyncOracle, Environment, Proposer,
	SelectChain, Error as ConsensusError, CanAuthorWith,
};
use consensus_common::import_queue::{BoxBlockImport, BasicQueue, Verifier};
use codec::{Encode, Decode};
use client_api;
use log::*;

#[derive(derive_more::Display, Debug)]
pub enum Error<B: BlockT> {
	#[display(fmt = "Header uses the wrong engine {:?}", _0)]
	WrongEngine([u8; 4]),
	#[display(fmt = "Header {:?} is unsealed", _0)]
	HeaderUnsealed(B::Hash),
	#[display(fmt = "PoW validation error: invalid seal")]
	InvalidSeal,
	#[display(fmt = "Rejecting block too far in future")]
	TooFarInFuture,
	#[display(fmt = "Fetching best header failed using select chain: {:?}", _0)]
	BestHeaderSelectChain(ConsensusError),
	#[display(fmt = "Fetching best header failed: {:?}", _0)]
	BestHeader(sp_blockchain::Error),
	#[display(fmt = "Best header does not exist")]
	NoBestHeader,
	#[display(fmt = "Block proposing error: {:?}", _0)]
	BlockProposingError(String),
	#[display(fmt = "Fetch best hash failed via select chain: {:?}", _0)]
	BestHashSelectChain(ConsensusError),
	#[display(fmt = "Error with block built on {:?}: {:?}", _0, _1)]
	BlockBuiltError(B::Hash, ConsensusError),
	#[display(fmt = "Creating inherents failed: {}", _0)]
	CreateInherents(inherents::Error),
	#[display(fmt = "Checking inherents failed: {}", _0)]
	CheckInherents(String),
	Client(sp_blockchain::Error),
	Codec(codec::Error),
	Environment(String),
	Runtime(RuntimeString)
}

impl<B: BlockT> std::convert::From<Error<B>> for String {
	fn from(error: Error<B>) -> String {
		error.to_string()
	}
}

/// Auxiliary storage prefix for PoW engine.
pub const POW_AUX_PREFIX: [u8; 4] = *b"PoW:";

/// Get the auxiliary storage key used by engine to store total difficulty.
fn aux_key(hash: &H256) -> Vec<u8> {
	POW_AUX_PREFIX.iter().chain(&hash[..])
		.cloned().collect::<Vec<_>>()
}

/// Auxiliary storage data for PoW.
#[derive(Encode, Decode, Clone, Debug, Default)]
pub struct PowAux<Difficulty> {
	/// Difficulty of the current block.
	pub difficulty: Difficulty,
	/// Total difficulty up to current block.
	pub total_difficulty: Difficulty,
}

impl<Difficulty> PowAux<Difficulty> where
	Difficulty: Decode + Default,
{
	/// Read the auxiliary from client.
	pub fn read<C: AuxStore, B: BlockT>(client: &C, hash: &H256) -> Result<Self, Error<B>> {
		let key = aux_key(hash);

		match client.get_aux(&key).map_err(Error::Client)? {
			Some(bytes) => Self::decode(&mut &bytes[..])
				.map_err(Error::Codec),
			None => Ok(Self::default()),
		}
	}
}

/// Algorithm used for proof of work.
pub trait PowAlgorithm<B: BlockT> {
	/// Difficulty for the algorithm.
	type Difficulty: TotalDifficulty + Default + Encode + Decode + Ord + Clone + Copy;

	/// Get the next block's difficulty.
	fn difficulty(&self, parent: &BlockId<B>) -> Result<Self::Difficulty, Error<B>>;
	/// Verify proof of work against the given difficulty.
	fn verify(
		&self,
		parent: &BlockId<B>,
		pre_hash: &H256,
		seal: &Seal,
		difficulty: Self::Difficulty,
	) -> Result<bool, Error<B>>;
	/// Mine a seal that satisfies the given difficulty.
	fn mine(
		&self,
		parent: &BlockId<B>,
		pre_hash: &H256,
		difficulty: Self::Difficulty,
		round: u32,
	) -> Result<Option<Seal>, Error<B>>;
}

/// A verifier for PoW blocks.
pub struct PowVerifier<B: BlockT<Hash=H256>, C, S, Algorithm> {
	client: Arc<C>,
	algorithm: Algorithm,
	inherent_data_providers: inherents::InherentDataProviders,
	select_chain: Option<S>,
	check_inherents_after: <<B as BlockT>::Header as HeaderT>::Number,
}

impl<B: BlockT<Hash=H256>, C, S, Algorithm> PowVerifier<B, C, S, Algorithm> {
	pub fn new(
		client: Arc<C>,
		algorithm: Algorithm,
		check_inherents_after: <<B as BlockT>::Header as HeaderT>::Number,
		select_chain: Option<S>,
		inherent_data_providers: inherents::InherentDataProviders,
	) -> Self {
		Self { client, algorithm, inherent_data_providers, select_chain, check_inherents_after }
	}

	fn check_header(
		&self,
		mut header: B::Header,
		parent_block_id: BlockId<B>,
	) -> Result<(B::Header, Algorithm::Difficulty, DigestItem<H256>), Error<B>> where
		Algorithm: PowAlgorithm<B>,
	{
		let hash = header.hash();

		let (seal, inner_seal) = match header.digest_mut().pop() {
			Some(DigestItem::Seal(id, seal)) => {
				if id == POW_ENGINE_ID {
					(DigestItem::Seal(id, seal.clone()), seal)
				} else {
					return Err(Error::WrongEngine(id))
				}
			},
			_ => return Err(Error::HeaderUnsealed(hash)),
		};

		let pre_hash = header.hash();
		let difficulty = self.algorithm.difficulty(&parent_block_id)?;

		if !self.algorithm.verify(
			&parent_block_id,
			&pre_hash,
			&inner_seal,
			difficulty,
		)? {
			return Err(Error::InvalidSeal);
		}

		Ok((header, difficulty, seal))
	}

	fn check_inherents(
		&self,
		block: B,
		block_id: BlockId<B>,
		inherent_data: InherentData,
		timestamp_now: u64,
	) -> Result<(), Error<B>> where
		C: ProvideRuntimeApi, C::Api: BlockBuilderApi<B, Error = sp_blockchain::Error>
	{
		const MAX_TIMESTAMP_DRIFT_SECS: u64 = 60;

		if *block.header().number() < self.check_inherents_after {
			return Ok(())
		}

		let inherent_res = self.client.runtime_api().check_inherents(
			&block_id,
			block,
			inherent_data,
		).map_err(Error::Client)?;

		if !inherent_res.ok() {
			inherent_res
				.into_errors()
				.try_for_each(|(i, e)| match TIError::try_from(&i, &e) {
					Some(TIError::ValidAtTimestamp(timestamp)) => {
						if timestamp > timestamp_now + MAX_TIMESTAMP_DRIFT_SECS {
							return Err(Error::TooFarInFuture);
						}

						Ok(())
					},
					Some(TIError::Other(e)) => Err(Error::Runtime(e)),
					None => Err(Error::CheckInherents(
						self.inherent_data_providers.error_to_string(&i, &e)
					)),
				})
		} else {
			Ok(())
		}
	}
}

impl<B: BlockT<Hash=H256>, C, S, Algorithm> Verifier<B> for PowVerifier<B, C, S, Algorithm> where
	C: ProvideRuntimeApi + Send + Sync + HeaderBackend<B> + AuxStore + ProvideCache<B> + BlockOf,
	C::Api: BlockBuilderApi<B, Error = sp_blockchain::Error>,
	S: SelectChain<B>,
	Algorithm: PowAlgorithm<B> + Send + Sync,
{
	fn verify(
		&mut self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Option<Justification>,
		mut body: Option<Vec<B::Extrinsic>>,
	) -> Result<(BlockImportParams<B>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		let inherent_data = self.inherent_data_providers
			.create_inherent_data().map_err(|e| e.into_string())?;
		let timestamp_now = inherent_data.timestamp_inherent_data().map_err(|e| e.into_string())?;

		let best_hash = match self.select_chain.as_ref() {
			Some(select_chain) => select_chain.best_chain()
				.map_err(|e| format!("Fetch best chain failed via select chain: {:?}", e))?
				.hash(),
			None => self.client.info().best_hash,
		};
		let hash = header.hash();
		let parent_hash = *header.parent_hash();
		let best_aux = PowAux::read::<_, B>(self.client.as_ref(), &best_hash)?;
		let mut aux = PowAux::read::<_, B>(self.client.as_ref(), &parent_hash)?;

		let (checked_header, difficulty, seal) = self.check_header(
			header,
			BlockId::Hash(parent_hash),
		)?;
		aux.difficulty = difficulty;
		aux.total_difficulty.increment(difficulty);

		if let Some(inner_body) = body.take() {
			let block = B::new(checked_header.clone(), inner_body);

			self.check_inherents(
				block.clone(),
				BlockId::Hash(parent_hash),
				inherent_data,
				timestamp_now
			)?;

			let (_, inner_body) = block.deconstruct();
			body = Some(inner_body);
		}
		let key = aux_key(&hash);
		let import_block = BlockImportParams {
			origin,
			header: checked_header,
			post_digests: vec![seal],
			body,
			finalized: false,
			justification,
			auxiliary: vec![(key, Some(aux.encode()))],
			fork_choice: ForkChoiceStrategy::Custom(aux.total_difficulty > best_aux.total_difficulty),
			allow_missing_state: false,
			import_existing: false,
		};

		Ok((import_block, None))
	}
}

/// Register the PoW inherent data provider, if not registered already.
pub fn register_pow_inherent_data_provider(
	inherent_data_providers: &InherentDataProviders,
) -> Result<(), consensus_common::Error> {
	if !inherent_data_providers.has_provider(&sp_timestamp::INHERENT_IDENTIFIER) {
		inherent_data_providers
			.register_provider(sp_timestamp::InherentDataProvider)
			.map_err(Into::into)
			.map_err(consensus_common::Error::InherentData)
	} else {
		Ok(())
	}
}

/// The PoW import queue type.
pub type PowImportQueue<B> = BasicQueue<B>;

/// Import queue for PoW engine.
pub fn import_queue<B, C, S, Algorithm>(
	block_import: BoxBlockImport<B>,
	client: Arc<C>,
	algorithm: Algorithm,
	check_inherents_after: <<B as BlockT>::Header as HeaderT>::Number,
	select_chain: Option<S>,
	inherent_data_providers: InherentDataProviders,
) -> Result<PowImportQueue<B>, consensus_common::Error> where
	B: BlockT<Hash=H256>,
	C: ProvideRuntimeApi + HeaderBackend<B> + BlockOf + ProvideCache<B> + AuxStore,
	C: Send + Sync + AuxStore + 'static,
	C::Api: BlockBuilderApi<B, Error = sp_blockchain::Error>,
	Algorithm: PowAlgorithm<B> + Send + Sync + 'static,
	S: SelectChain<B> + 'static,
{
	register_pow_inherent_data_provider(&inherent_data_providers)?;

	let verifier = PowVerifier::new(
		client.clone(),
		algorithm,
		check_inherents_after,
		select_chain,
		inherent_data_providers,
	);

	Ok(BasicQueue::new(
		verifier,
		block_import,
		None,
		None
	))
}

/// Start the background mining thread for PoW. Note that because PoW mining
/// is CPU-intensive, it is not possible to use an async future to define this.
/// However, it's not recommended to use background threads in the rest of the
/// codebase.
///
/// `preruntime` is a parameter that allows a custom additional pre-runtime
/// digest to be inserted for blocks being built. This can encode authorship
/// information, or just be a graffiti. `round` is for number of rounds the
/// CPU miner runs each time. This parameter should be tweaked so that each
/// mining round is within sub-second time.
pub fn start_mine<B: BlockT<Hash=H256>, C, Algorithm, E, SO, S, CAW>(
	mut block_import: BoxBlockImport<B>,
	client: Arc<C>,
	algorithm: Algorithm,
	mut env: E,
	preruntime: Option<Vec<u8>>,
	round: u32,
	mut sync_oracle: SO,
	build_time: std::time::Duration,
	select_chain: Option<S>,
	inherent_data_providers: inherents::InherentDataProviders,
	can_author_with: CAW,
) where
	C: HeaderBackend<B> + AuxStore + 'static,
	Algorithm: PowAlgorithm<B> + Send + Sync + 'static,
	E: Environment<B> + Send + Sync + 'static,
	E::Error: std::fmt::Debug,
	SO: SyncOracle + Send + Sync + 'static,
	S: SelectChain<B> + 'static,
	CAW: CanAuthorWith<B> + Send + 'static,
{
	if let Err(_) = register_pow_inherent_data_provider(&inherent_data_providers) {
		warn!("Registering inherent data provider for timestamp failed");
	}

	thread::spawn(move || {
		loop {
			match mine_loop(
				&mut block_import,
				client.as_ref(),
				&algorithm,
				&mut env,
				preruntime.as_ref(),
				round,
				&mut sync_oracle,
				build_time.clone(),
				select_chain.as_ref(),
				&inherent_data_providers,
				&can_author_with,
			) {
				Ok(()) => (),
				Err(e) => error!(
					"Mining block failed with {:?}. Sleep for 1 second before restarting...",
					e
				),
			}
			std::thread::sleep(std::time::Duration::new(1, 0));
		}
	});
}

fn mine_loop<B: BlockT<Hash=H256>, C, Algorithm, E, SO, S, CAW>(
	block_import: &mut BoxBlockImport<B>,
	client: &C,
	algorithm: &Algorithm,
	env: &mut E,
	preruntime: Option<&Vec<u8>>,
	round: u32,
	sync_oracle: &mut SO,
	build_time: std::time::Duration,
	select_chain: Option<&S>,
	inherent_data_providers: &inherents::InherentDataProviders,
	can_author_with: &CAW,
) -> Result<(), Error<B>> where
	C: HeaderBackend<B> + AuxStore,
	Algorithm: PowAlgorithm<B>,
	E: Environment<B>,
	E::Error: std::fmt::Debug,
	SO: SyncOracle,
	S: SelectChain<B>,
	CAW: CanAuthorWith<B>,
{
	'outer: loop {
		if sync_oracle.is_major_syncing() {
			debug!(target: "pow", "Skipping proposal due to sync.");
			std::thread::sleep(std::time::Duration::new(1, 0));
			continue 'outer
		}

		let (best_hash, best_header) = match select_chain {
			Some(select_chain) => {
				let header = select_chain.best_chain()
					.map_err(Error::BestHeaderSelectChain)?;
				let hash = header.hash();
				(hash, header)
			},
			None => {
				let hash = client.info().best_hash;
				let header = client.header(BlockId::Hash(hash))
					.map_err(Error::BestHeader)?
					.ok_or(Error::NoBestHeader)?;
				(hash, header)
			},
		};

		if let Err(err) = can_author_with.can_author_with(&BlockId::Hash(best_hash)) {
			warn!(
				target: "pow",
				"Skipping proposal `can_author_with` returned: {} \
				Probably a node update is required!",
				err,
			);
			std::thread::sleep(std::time::Duration::from_secs(1));
			continue 'outer
		}

		let mut aux = PowAux::read(client, &best_hash)?;
		let mut proposer = env.init(&best_header)
			.map_err(|e| Error::Environment(format!("{:?}", e)))?;

		let inherent_data = inherent_data_providers
			.create_inherent_data().map_err(Error::CreateInherents)?;
		let mut inherent_digest = Digest::default();
		if let Some(preruntime) = &preruntime {
			inherent_digest.push(DigestItem::PreRuntime(POW_ENGINE_ID, preruntime.to_vec()));
		}
		let block = futures::executor::block_on(proposer.propose(
			inherent_data,
			inherent_digest,
			build_time.clone(),
		)).map_err(|e| Error::BlockProposingError(format!("{:?}", e)))?;

		let (header, body) = block.deconstruct();
		let (difficulty, seal) = {
			let difficulty = algorithm.difficulty(
				&BlockId::Hash(best_hash),
			)?;

			loop {
				let seal = algorithm.mine(
					&BlockId::Hash(best_hash),
					&header.hash(),
					difficulty,
					round,
				)?;

				if let Some(seal) = seal {
					break (difficulty, seal)
				}

				if best_hash != client.info().best_hash {
					continue 'outer
				}
			}
		};

		aux.difficulty = difficulty;
		aux.total_difficulty.increment(difficulty);
		let hash = {
			let mut header = header.clone();
			header.digest_mut().push(DigestItem::Seal(POW_ENGINE_ID, seal.clone()));
			header.hash()
		};

		let key = aux_key(&hash);
		let best_hash = match select_chain {
			Some(select_chain) => select_chain.best_chain()
				.map_err(Error::BestHashSelectChain)?
				.hash(),
			None => client.info().best_hash,
		};
		let best_aux = PowAux::<Algorithm::Difficulty>::read(client, &best_hash)?;

		// if the best block has changed in the meantime drop our proposal
		if best_aux.total_difficulty > aux.total_difficulty {
			continue 'outer
		}

		let import_block = BlockImportParams {
			origin: BlockOrigin::Own,
			header,
			justification: None,
			post_digests: vec![DigestItem::Seal(POW_ENGINE_ID, seal)],
			body: Some(body),
			finalized: false,
			auxiliary: vec![(key, Some(aux.encode()))],
			fork_choice: ForkChoiceStrategy::Custom(true),
			allow_missing_state: false,
			import_existing: false,
		};

		block_import.import_block(import_block, HashMap::default())
			.map_err(|e| Error::BlockBuiltError(best_hash, e))?;
	}
}
