// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! API implementation for `archive`.

use crate::{
	archive::{ArchiveApiServer, NetworkConfig},
	SubscriptionTaskExecutor,
};
use jsonrpsee::{
	core::{async_trait, RpcResult},
	types::SubscriptionResult,
	SubscriptionSink,
};
use sc_client_api::{Backend, BlockBackend, BlockchainEvents, ExecutorProvider, StorageProvider};
use sp_api::BlockT;
use sp_blockchain::{Error as BlockChainError, HeaderBackend, HeaderMetadata};
use std::{marker::PhantomData, sync::Arc};

/// An API for archive RPC calls.
pub struct Archive<BE, Block: BlockT, Client> {
	/// Substrate client.
	_client: Arc<Client>,
	/// Executor to spawn subscriptions.
	_executor: SubscriptionTaskExecutor,
	/// The hexadecimal encoded hash of the genesis block.
	genesis_hash: String,
	/// Phantom member to pin the block type.
	_phantom: PhantomData<(Block, BE)>,
}

impl<BE, Block: BlockT, Client> Archive<BE, Block, Client> {
	/// Create a new [`Archive`].
	pub fn new<GenesisHash: AsRef<[u8]>>(
		client: Arc<Client>,
		executor: SubscriptionTaskExecutor,
		genesis_hash: GenesisHash,
	) -> Self {
		let genesis_hash = format!("0x{}", hex::encode(genesis_hash));

		Self { _client: client, _executor: executor, genesis_hash, _phantom: PhantomData }
	}
}

#[async_trait]
impl<BE, Block: BlockT, Client> ArchiveApiServer<Block::Hash> for Archive<BE, Block, Client>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	BE: Backend<Block> + 'static,
	Client: BlockBackend<Block>
		+ ExecutorProvider<Block>
		+ HeaderBackend<Block>
		+ HeaderMetadata<Block, Error = BlockChainError>
		+ BlockchainEvents<Block>
		+ StorageProvider<Block, BE>
		+ 'static,
{
	fn archive_unstable_body(
		&self,
		mut _sink: SubscriptionSink,
		_hash: Block::Hash,
		_network_config: Option<NetworkConfig>,
	) -> SubscriptionResult {
		Ok(())
	}

	fn archive_unstable_genesis_hash(&self) -> RpcResult<String> {
		Ok(self.genesis_hash.clone())
	}

	fn archive_unstable_hash_by_height(
		&self,
		mut _sink: SubscriptionSink,
		_height: String,
		_network_config: Option<NetworkConfig>,
	) -> SubscriptionResult {
		Ok(())
	}

	fn archive_unstable_header(
		&self,
		mut _sink: SubscriptionSink,
		_hash: Block::Hash,
		_network_config: Option<NetworkConfig>,
	) -> SubscriptionResult {
		Ok(())
	}

	fn archive_unstable_storage(
		&self,
		mut _sink: SubscriptionSink,
		_hash: Block::Hash,
		_key: String,
		_child_key: Option<String>,
		_network_config: Option<NetworkConfig>,
	) -> SubscriptionResult {
		Ok(())
	}
}
