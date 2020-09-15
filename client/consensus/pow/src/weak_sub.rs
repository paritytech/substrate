// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

use std::{
	sync::Arc, collections::HashMap, marker::PhantomData, fmt::Debug,
	time::{SystemTime, Duration}, ops::Add,
};
use codec::{Encode, Decode};
use sc_client_api::{BlockOf, AuxStore};
use sp_api::ProvideRuntimeApi;
use sp_runtime::{traits::{Block as BlockT, Header as HeaderT}};
use sp_blockchain::{
	well_known_cache_keys::Id as CacheKeyId, HeaderMetadata,
};
use sp_consensus::{
	ImportResult, BlockImportParams, BlockCheckParams, Error as ConsensusError, BlockImport,
	SelectChain, ForkChoiceStrategy,
};
use crate::{Error, DifficultyOf};

/// Auxiliaty for weak subjectivity.
#[derive(Encode, Decode, Clone, Debug)]
pub struct WeakSubjectiveAux {
	/// Receive timestamp second.
	pub receive_timestamp_secs: u64,
	/// Receive timestamp subsecond nanos.
	pub receive_timestamp_subsec_nanos: u32,
}

impl WeakSubjectiveAux {
	/// Create a new weak subjectivity auxiliaty.
	pub fn new(receive_timestamp: Duration) -> Self {
		Self {
			receive_timestamp_secs: receive_timestamp.as_secs(),
			receive_timestamp_subsec_nanos: receive_timestamp.subsec_nanos(),
		}
	}

	/// Get the receive timestamp of the auxiliaty.
	pub fn receive_timestamp(&self) -> Duration {
		Duration::new(self.receive_timestamp_secs, self.receive_timestamp_subsec_nanos)
	}
}

/// Read the auxiliary from client.
fn read_aux<C: AuxStore, B: BlockT>(
	client: &C,
	hash: &B::Hash,
) -> Result<Option<WeakSubjectiveAux>, Error<B>> {
	let key = aux_key(&hash);

	match client.get_aux(&key).map_err(Error::Client)? {
		Some(bytes) => WeakSubjectiveAux::decode(&mut &bytes[..]).map(Some).map_err(Error::Codec),
		None => Ok(None),
	}
}

/// Auxiliaty storage prefix for weak subjectivity block import.
pub const WEAK_SUB_AUX_PREFIX: [u8; 9] = *b"PoW-Weak:";

/// Get the auxiliaty storage key for weak subjectivity.
fn aux_key<T: AsRef<[u8]>>(hash: &T) -> Vec<u8> {
	WEAK_SUB_AUX_PREFIX.iter().chain(hash.as_ref()).copied().collect()
}

/// Parameters passed to decision function of whether to block the reorg.
pub struct WeakSubjectiveParams<Difficulty> {
	/// Total difficulty of the best block.
	pub best_total_difficulty: Difficulty,
	/// Total difficulty of the common ancestor.
	pub common_total_difficulty: Difficulty,
	/// Total difficulty of the new block to be imported.
	pub new_total_difficulty: Difficulty,
	/// Recieve timestamp of the best block.
	pub best_receive_timestamp: Duration,
	/// Receive timestamp of the common ancestor.
	pub common_receive_timestamp: Duration,
	/// Receive timestamp of the new block to be imported.
	pub new_receive_timestamp: Duration,
	/// Retracted block length if the reorg happens.
	pub retracted_len: usize,
}

/// Deccision of weak subjectivity.
pub enum WeakSubjectiveDecision {
	/// Block the reorg.
	BlockReorg,
	/// Continue the normal import.
	Continue,
}

/// Algorithm used for the decision function of weak subjectivity.
pub trait WeakSubjectiveAlgorithm<Difficulty> {
	/// Decide based on the weak subjectivity parameters of whether to block the import.
	fn weak_subjective_decide(
		&self,
		params: WeakSubjectiveParams<Difficulty>,
	) -> WeakSubjectiveDecision;
}

/// Block import for weak subjectivity. It must be combined with a PoW block import.
pub struct WeakSubjectiveBlockImport<B: BlockT, I, C, S, Algorithm> {
	inner: I,
	client: Arc<C>,
	select_chain: S,
	algorithm: Algorithm,
	_marker: PhantomData<B>,
}

impl<B: BlockT, I: Clone, C, S: Clone, Algorithm: Clone> Clone
	for WeakSubjectiveBlockImport<B, I, C, S, Algorithm>
{
	fn clone(&self) -> Self {
		Self {
			inner: self.inner.clone(),
			client: self.client.clone(),
			select_chain: self.select_chain.clone(),
			algorithm: self.algorithm.clone(),
			_marker: PhantomData,
		}
	}
}

impl<B, I, C, S, Algorithm> WeakSubjectiveBlockImport<B, I, C, S, Algorithm> where
	B: BlockT,
	I: BlockImport<B, Transaction = sp_api::TransactionFor<C, B>> + DifficultyOf<B> + Send + Sync,
	I::Error: Into<ConsensusError>,
	I::Difficulty: Decode + Add<I::Difficulty, Output=I::Difficulty>,
	C: ProvideRuntimeApi<B> + HeaderMetadata<B> + BlockOf + AuxStore + Send + Sync,
	C::Error: Debug,
	S: SelectChain<B>,
	Algorithm: WeakSubjectiveAlgorithm<I::Difficulty>,
{
	/// Create a new block import for weak subjectivity.
	pub fn new(
		inner: I,
		client: Arc<C>,
		algorithm: Algorithm,
		select_chain: S,
	) -> Self {
		Self {
			inner,
			client,
			algorithm,
			select_chain,
			_marker: PhantomData,
		}
	}
}

impl<B, I, C, S, Algorithm> BlockImport<B> for WeakSubjectiveBlockImport<B, I, C, S, Algorithm> where
	B: BlockT,
	I: BlockImport<B, Transaction = sp_api::TransactionFor<C, B>> + DifficultyOf<B> + Send + Sync,
	I::Error: Into<ConsensusError>,
	I::Difficulty: Decode + Add<I::Difficulty, Output=I::Difficulty>,
	C: ProvideRuntimeApi<B> + HeaderMetadata<B> + BlockOf + AuxStore + Send + Sync,
	C::Error: Debug,
	S: SelectChain<B>,
	Algorithm: WeakSubjectiveAlgorithm<I::Difficulty>,
{
	type Error = ConsensusError;
	type Transaction = sp_api::TransactionFor<C, B>;

	fn check_block(
		&mut self,
		block: BlockCheckParams<B>,
	) -> Result<ImportResult, Self::Error> {
		self.inner.check_block(block).map_err(Into::into)
	}

	fn import_block(
		&mut self,
		mut block: BlockImportParams<B, Self::Transaction>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		let best_header = self.select_chain.best_chain()
			.map_err(|e| format!("Fetch best chain failed via select chain: {:?}", e))?;
		let best_hash = best_header.hash();

		let parent_hash = *block.header.parent_hash();
		let route_from_best = sp_blockchain::tree_route(
			self.client.as_ref(),
			best_hash,
			parent_hash,
		).map_err(|e| format!("Find route from best failed: {:?}", e))?;

		let retracted_len = route_from_best.retracted().len();

		let best_aux = read_aux::<_, B>(
			self.client.as_ref(),
			&best_hash,
		)?;
		let common_aux = read_aux::<_, B>(
			self.client.as_ref(),
			&route_from_best.common_block().hash,
		)?;

		let best_difficulty_aux = self.inner.difficulty_of(&best_hash)?;
		let parent_difficulty_aux = self.inner.difficulty_of(&parent_hash)?;
		let common_difficulty_aux = self.inner.difficulty_of(&route_from_best.common_block().hash)?;

		let new_receive_timestamp = SystemTime::now().duration_since(SystemTime::UNIX_EPOCH)
			.map_err(|e| format!("Current time is before unix epoch: {:?}", e))?;

		if let (
			Some(best_aux),
			Some(common_aux),
			Some(best_difficulty_aux),
			Some(parent_difficulty_aux),
			Some(common_difficulty_aux),
		) = (
			best_aux,
			common_aux,
			best_difficulty_aux,
			parent_difficulty_aux,
			common_difficulty_aux,
		) {
			let best_total_difficulty = best_difficulty_aux.total_difficulty;
			let common_total_difficulty = common_difficulty_aux.total_difficulty;
			let new_total_difficulty = parent_difficulty_aux.total_difficulty +
				self.inner.next_difficulty_of(&parent_hash)?;

			let params = WeakSubjectiveParams {
				best_total_difficulty,
				common_total_difficulty,
				new_total_difficulty,
				best_receive_timestamp: best_aux.receive_timestamp(),
				new_receive_timestamp: new_receive_timestamp.clone(),
				common_receive_timestamp: common_aux.receive_timestamp(),
				retracted_len,
			};

			match self.algorithm.weak_subjective_decide(params) {
				WeakSubjectiveDecision::BlockReorg => {
					block.fork_choice = Some(ForkChoiceStrategy::Custom(false));
				},
				WeakSubjectiveDecision::Continue => (),
			}
		}

		let key = aux_key(&block.post_hash());
		block.auxiliary.push((key, Some(WeakSubjectiveAux::new(new_receive_timestamp).encode())));

		self.inner.import_block(block, new_cache).map_err(Into::into)
	}
}
