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

//! Substrate blockchain API.

mod chain_full;

#[cfg(test)]
mod tests;

use std::sync::Arc;

use crate::SubscriptionTaskExecutor;

use jsonrpsee::{core::RpcResult, types::SubscriptionResult, SubscriptionSink};
use sc_client_api::BlockchainEvents;
use sp_rpc::{list::ListOrValue, number::NumberOrHex};
use sp_runtime::{
	generic::SignedBlock,
	traits::{Block as BlockT, NumberFor},
};

use self::error::Error;

use sc_client_api::BlockBackend;
pub use sc_rpc_api::chain::*;
use sp_blockchain::HeaderBackend;

/// Blockchain backend API
trait ChainBackend<Client, Block: BlockT>: Send + Sync + 'static
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	Client: HeaderBackend<Block> + BlockchainEvents<Block> + 'static,
{
	/// Get client reference.
	fn client(&self) -> &Arc<Client>;

	/// Tries to unwrap passed block hash, or uses best block hash otherwise.
	fn unwrap_or_best(&self, hash: Option<Block::Hash>) -> Block::Hash {
		match hash {
			None => self.client().info().best_hash,
			Some(hash) => hash,
		}
	}

	/// Get header of a relay chain block.
	fn header(&self, hash: Option<Block::Hash>) -> Result<Option<Block::Header>, Error>;

	/// Get header and body of a relay chain block.
	fn block(&self, hash: Option<Block::Hash>) -> Result<Option<SignedBlock<Block>>, Error>;

	/// Get hash of the n-th block in the canon chain.
	///
	/// By default returns latest block hash.
	fn block_hash(&self, number: Option<NumberOrHex>) -> Result<Option<Block::Hash>, Error> {
		match number {
			None => Ok(Some(self.client().info().best_hash)),
			Some(num_or_hex) => {
				// FIXME <2329>: Database seems to limit the block number to u32 for no reason
				let block_num: u32 = num_or_hex.try_into().map_err(|_| {
					Error::Other(format!(
						"`{:?}` > u32::MAX, the max block number is u32.",
						num_or_hex
					))
				})?;
				let block_num = <NumberFor<Block>>::from(block_num);
				self.client().hash(block_num).map_err(client_err)
			},
		}
	}

	/// Get hash of the last finalized block in the canon chain.
	fn finalized_head(&self) -> Result<Block::Hash, Error> {
		Ok(self.client().info().finalized_hash)
	}

	/// All new head subscription
	fn subscribe_all_heads(&self, sink: SubscriptionSink);

	/// New best head subscription
	fn subscribe_new_heads(&self, sink: SubscriptionSink);

	/// Finalized head subscription
	fn subscribe_finalized_heads(&self, sink: SubscriptionSink);
}

/// Create new state API that works on full node.
pub fn new_full<Block: BlockT, Client>(
	client: Arc<Client>,
	executor: SubscriptionTaskExecutor,
) -> Chain<Block, Client>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	Client: BlockBackend<Block> + HeaderBackend<Block> + BlockchainEvents<Block> + 'static,
{
	Chain { backend: Box::new(self::chain_full::FullChain::new(client, executor)) }
}

/// Chain API with subscriptions support.
pub struct Chain<Block: BlockT, Client> {
	backend: Box<dyn ChainBackend<Client, Block>>,
}

impl<Block, Client> ChainApiServer<NumberFor<Block>, Block::Hash, Block::Header, SignedBlock<Block>>
	for Chain<Block, Client>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	Client: HeaderBackend<Block> + BlockchainEvents<Block> + 'static,
{
	fn header(&self, hash: Option<Block::Hash>) -> RpcResult<Option<Block::Header>> {
		self.backend.header(hash).map_err(Into::into)
	}

	fn block(&self, hash: Option<Block::Hash>) -> RpcResult<Option<SignedBlock<Block>>> {
		self.backend.block(hash).map_err(Into::into)
	}

	fn block_hash(
		&self,
		number: Option<ListOrValue<NumberOrHex>>,
	) -> RpcResult<ListOrValue<Option<Block::Hash>>> {
		match number {
			None => self.backend.block_hash(None).map(ListOrValue::Value).map_err(Into::into),
			Some(ListOrValue::Value(number)) => self
				.backend
				.block_hash(Some(number))
				.map(ListOrValue::Value)
				.map_err(Into::into),
			Some(ListOrValue::List(list)) => Ok(ListOrValue::List(
				list.into_iter()
					.map(|number| self.backend.block_hash(Some(number)))
					.collect::<Result<_, _>>()?,
			)),
		}
	}

	fn finalized_head(&self) -> RpcResult<Block::Hash> {
		self.backend.finalized_head().map_err(Into::into)
	}

	fn subscribe_all_heads(&self, sink: SubscriptionSink) -> SubscriptionResult {
		self.backend.subscribe_all_heads(sink);
		Ok(())
	}

	fn subscribe_new_heads(&self, sink: SubscriptionSink) -> SubscriptionResult {
		self.backend.subscribe_new_heads(sink);
		Ok(())
	}

	fn subscribe_finalized_heads(&self, sink: SubscriptionSink) -> SubscriptionResult {
		self.backend.subscribe_finalized_heads(sink);
		Ok(())
	}
}

fn client_err(err: sp_blockchain::Error) -> Error {
	Error::Client(Box::new(err))
}
