// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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
mod chain_light;
mod helpers;

#[cfg(test)]
mod tests;

use std::sync::Arc;

use crate::SubscriptionTaskExecutor;

use jsonrpsee::{
	types::{async_trait, JsonRpcResult},
	SubscriptionSink,
};
use sc_client_api::{
	light::{Fetcher, RemoteBlockchain},
	BlockchainEvents,
};
use sp_rpc::{list::ListOrValue, number::NumberOrHex};
use sp_runtime::{
	generic::{BlockId, SignedBlock},
	traits::{Block as BlockT, Header, NumberFor},
};

use self::error::Error;

use sc_client_api::BlockBackend;
pub use sc_rpc_api::chain::*;
use sp_blockchain::HeaderBackend;

/// Blockchain backend API
#[async_trait::async_trait]
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
		match hash.into() {
			None => self.client().info().best_hash,
			Some(hash) => hash,
		}
	}

	/// Get header of a relay chain block.
	async fn header(&self, hash: Option<Block::Hash>) -> Result<Option<Block::Header>, Error>;

	/// Get header and body of a relay chain block.
	async fn block(&self, hash: Option<Block::Hash>) -> Result<Option<SignedBlock<Block>>, Error>;

	/// Get hash of the n-th block in the canon chain.
	///
	/// By default returns latest block hash.
	fn block_hash(&self, number: Option<NumberOrHex>) -> Result<Option<Block::Hash>, Error> {
		match number {
			None => Ok(Some(self.client().info().best_hash)),
			Some(num_or_hex) => {
				use std::convert::TryInto;

				// FIXME <2329>: Database seems to limit the block number to u32 for no reason
				let block_num: u32 = num_or_hex.try_into().map_err(|_| {
					Error::from(format!(
						"`{:?}` > u32::MAX, the max block number is u32.",
						num_or_hex
					))
				})?;
				let block_num = <NumberFor<Block>>::from(block_num);
				Ok(self
					.client()
					.header(BlockId::number(block_num))
					.map_err(client_err)?
					.map(|h| h.hash()))
			},
		}
	}

	/// Get hash of the last finalized block in the canon chain.
	fn finalized_head(&self) -> Result<Block::Hash, Error> {
		Ok(self.client().info().finalized_hash)
	}

	/// All new head subscription
	fn subscribe_all_heads(&self, sink: SubscriptionSink) -> Result<(), Error>;

	/// New best head subscription
	fn subscribe_new_heads(&self, sink: SubscriptionSink) -> Result<(), Error>;

	/// Finalized head subscription
	fn subscribe_finalized_heads(&self, sink: SubscriptionSink) -> Result<(), Error>;
}

/// Create new state API that works on full node.
pub fn new_full<Block: BlockT, Client>(
	client: Arc<Client>,
	executor: Arc<SubscriptionTaskExecutor>,
) -> Chain<Block, Client>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	Client: BlockBackend<Block> + HeaderBackend<Block> + BlockchainEvents<Block> + 'static,
{
	Chain { backend: Box::new(self::chain_full::FullChain::new(client, executor)) }
}

/// Create new state API that works on light node.
pub fn new_light<Block: BlockT, Client, F: Fetcher<Block>>(
	client: Arc<Client>,
	executor: Arc<SubscriptionTaskExecutor>,
	remote_blockchain: Arc<dyn RemoteBlockchain<Block>>,
	fetcher: Arc<F>,
) -> Chain<Block, Client>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	Client: BlockBackend<Block> + HeaderBackend<Block> + BlockchainEvents<Block> + 'static,
	F: Send + Sync + 'static,
{
	Chain {
		backend: Box::new(self::chain_light::LightChain::new(
			client,
			remote_blockchain,
			fetcher,
			executor,
		)),
	}
}

/// Chain API with subscriptions support.
pub struct Chain<Block: BlockT, Client> {
	backend: Box<dyn ChainBackend<Client, Block>>,
}

// TODO(niklasad1): check if those DeserializeOwned bounds are really required.
#[async_trait]
impl<Block, Client> ChainApiServer<NumberFor<Block>, Block::Hash, Block::Header, SignedBlock<Block>>
	for Chain<Block, Client>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	Client: HeaderBackend<Block> + BlockchainEvents<Block> + 'static,
{
	async fn header(&self, hash: Option<Block::Hash>) -> JsonRpcResult<Option<Block::Header>> {
		self.backend.header(hash).await.map_err(Into::into)
	}

	async fn block(&self, hash: Option<Block::Hash>) -> JsonRpcResult<Option<SignedBlock<Block>>> {
		self.backend.block(hash).await.map_err(Into::into)
	}

	fn block_hash(
		&self,
		number: Option<ListOrValue<NumberOrHex>>,
	) -> JsonRpcResult<ListOrValue<Option<Block::Hash>>> {
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

	fn finalized_head(&self) -> JsonRpcResult<Block::Hash> {
		self.backend.finalized_head().map_err(Into::into)
	}

	fn subscribe_all_heads(&self, sink: SubscriptionSink) {
		let _ = self.backend.subscribe_all_heads(sink);
	}

	fn subscribe_new_heads(&self, sink: SubscriptionSink) {
		let _ = self.backend.subscribe_new_heads(sink);
	}

	fn subscribe_finalized_heads(&self, sink: SubscriptionSink) {
		let _ = self.backend.subscribe_finalized_heads(sink);
	}
}

fn client_err(err: sp_blockchain::Error) -> Error {
	Error::Client(Box::new(err))
}
