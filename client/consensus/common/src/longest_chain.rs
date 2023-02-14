// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Longest chain implementation

use sc_client_api::backend;
use sp_blockchain::{Backend, HeaderBackend};
use sp_consensus::{Error as ConsensusError, SelectChain};
use sp_runtime::traits::{Block as BlockT, Header, NumberFor};
use std::{marker::PhantomData, sync::Arc};

/// Implement Longest Chain Select implementation
/// where 'longest' is defined as the highest number of blocks
pub struct LongestChain<B, Block> {
	backend: Arc<B>,
	_phantom: PhantomData<Block>,
}

impl<B, Block> Clone for LongestChain<B, Block> {
	fn clone(&self) -> Self {
		let backend = self.backend.clone();
		LongestChain { backend, _phantom: Default::default() }
	}
}

impl<B, Block> LongestChain<B, Block>
where
	B: backend::Backend<Block>,
	Block: BlockT,
{
	/// Instantiate a new LongestChain for Backend B
	pub fn new(backend: Arc<B>) -> Self {
		LongestChain { backend, _phantom: Default::default() }
	}

	fn best_hash(&self) -> sp_blockchain::Result<<Block as BlockT>::Hash> {
		let info = self.backend.blockchain().info();
		let import_lock = self.backend.get_import_lock();
		let best_hash = self
			.backend
			.blockchain()
			.longest_containing(info.best_hash, import_lock)?
			.unwrap_or(info.best_hash);
		Ok(best_hash)
	}

	fn best_header(&self) -> sp_blockchain::Result<<Block as BlockT>::Header> {
		let best_hash = self.best_hash()?;
		Ok(self
			.backend
			.blockchain()
			.header(best_hash)?
			.expect("given block hash was fetched from block in db; qed"))
	}

	/// Returns the highest descendant of the given block that is a valid
	/// candidate to be finalized.
	///
	/// In this context, being a valid target means being an ancestor of
	/// the best chain according to the `best_header` method.
	///
	/// If `maybe_max_number` is `Some(max_block_number)` the search is
	/// limited to block `number <= max_block_number`. In other words
	/// as if there were no blocks greater than `max_block_number`.
	fn finality_target(
		&self,
		base_hash: Block::Hash,
		maybe_max_number: Option<NumberFor<Block>>,
	) -> sp_blockchain::Result<Block::Hash> {
		use sp_blockchain::Error::{Application, MissingHeader};
		let blockchain = self.backend.blockchain();

		let mut current_head = self.best_header()?;
		let mut best_hash = current_head.hash();

		let base_header = blockchain
			.header(base_hash)?
			.ok_or_else(|| MissingHeader(base_hash.to_string()))?;
		let base_number = *base_header.number();

		if let Some(max_number) = maybe_max_number {
			if max_number < base_number {
				let msg = format!(
					"Requested a finality target using max number {} below the base number {}",
					max_number, base_number
				);
				return Err(Application(msg.into()))
			}

			while current_head.number() > &max_number {
				best_hash = *current_head.parent_hash();
				current_head = blockchain
					.header(best_hash)?
					.ok_or_else(|| MissingHeader(format!("{best_hash:?}")))?;
			}
		}

		while current_head.hash() != base_hash {
			if *current_head.number() < base_number {
				let msg = format!(
					"Requested a finality target using a base {:?} not in the best chain {:?}",
					base_hash, best_hash,
				);
				return Err(Application(msg.into()))
			}
			let current_hash = *current_head.parent_hash();
			current_head = blockchain
				.header(current_hash)?
				.ok_or_else(|| MissingHeader(format!("{best_hash:?}")))?;
		}

		Ok(best_hash)
	}

	fn leaves(&self) -> Result<Vec<<Block as BlockT>::Hash>, sp_blockchain::Error> {
		self.backend.blockchain().leaves()
	}
}

#[async_trait::async_trait]
impl<B, Block> SelectChain<Block> for LongestChain<B, Block>
where
	B: backend::Backend<Block>,
	Block: BlockT,
{
	async fn leaves(&self) -> Result<Vec<<Block as BlockT>::Hash>, ConsensusError> {
		LongestChain::leaves(self).map_err(|e| ConsensusError::ChainLookup(e.to_string()))
	}

	async fn best_chain(&self) -> Result<<Block as BlockT>::Header, ConsensusError> {
		LongestChain::best_header(self).map_err(|e| ConsensusError::ChainLookup(e.to_string()))
	}

	async fn finality_target(
		&self,
		base_hash: Block::Hash,
		maybe_max_number: Option<NumberFor<Block>>,
	) -> Result<Block::Hash, ConsensusError> {
		LongestChain::finality_target(self, base_hash, maybe_max_number)
			.map_err(|e| ConsensusError::ChainLookup(e.to_string()))
	}
}
