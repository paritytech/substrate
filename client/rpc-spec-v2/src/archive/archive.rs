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
	archive::{
		error::Error as ArchiveRpcError,
		event::{ArchiveEvent, ArchiveResult, ErrorEvent},
		ArchiveApiServer, NetworkConfig,
	},
	SubscriptionTaskExecutor,
};
use codec::Encode;
use futures::future::FutureExt;
use jsonrpsee::{
	core::{async_trait, RpcResult},
	types::{SubscriptionEmptyError, SubscriptionResult},
	SubscriptionSink,
};
use sc_client_api::{
	Backend, BlockBackend, BlockchainEvents, ChildInfo, ExecutorProvider, StorageKey,
	StorageProvider,
};
use sp_api::{BlockId, BlockT};
use sp_blockchain::{Error as BlockChainError, HeaderBackend, HeaderMetadata};
use sp_core::{hexdisplay::HexDisplay, storage::well_known_keys};
use std::{marker::PhantomData, sync::Arc};

/// An API for archive RPC calls.
pub struct Archive<BE, Block: BlockT, Client> {
	/// Substrate client.
	client: Arc<Client>,
	/// Executor to spawn subscriptions.
	executor: SubscriptionTaskExecutor,
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

		Self { client, executor, genesis_hash, _phantom: PhantomData }
	}
}

fn parse_hex_param(
	sink: &mut SubscriptionSink,
	param: String,
) -> Result<Vec<u8>, SubscriptionEmptyError> {
	match array_bytes::hex2bytes(&param) {
		Ok(bytes) => Ok(bytes),
		Err(_) => {
			let _ = sink.reject(ArchiveRpcError::InvalidParam(param));
			Err(SubscriptionEmptyError)
		},
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
		mut sink: SubscriptionSink,
		hash: Block::Hash,
		_network_config: Option<NetworkConfig>,
	) -> SubscriptionResult {
		let client = self.client.clone();

		let fut = async move {
			let event = match client.block(&BlockId::Hash(hash)) {
				Ok(Some(signed_block)) => {
					let extrinsics = signed_block.block.extrinsics();
					let result = format!("0x{}", HexDisplay::from(&extrinsics.encode()));
					ArchiveEvent::Done(ArchiveResult { result })
				},
				Ok(None) => ArchiveEvent::Inaccessible,
				Err(error) => ArchiveEvent::Error(ErrorEvent { error: error.to_string() }),
			};
			let _ = sink.send(&event);
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
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
		mut sink: SubscriptionSink,
		hash: Block::Hash,
		_network_config: Option<NetworkConfig>,
	) -> SubscriptionResult {
		let client = self.client.clone();

		let fut = async move {
			let event = match client.header(BlockId::Hash(hash)) {
				Ok(Some(header)) => {
					let result = format!("0x{}", HexDisplay::from(&header.encode()));
					ArchiveEvent::Done(ArchiveResult { result })
				},
				Ok(None) => ArchiveEvent::Inaccessible,
				Err(error) => ArchiveEvent::Error(ErrorEvent { error: error.to_string() }),
			};
			let _ = sink.send(&event);
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}

	fn archive_unstable_storage(
		&self,
		mut sink: SubscriptionSink,
		hash: Block::Hash,
		key: String,
		child_key: Option<String>,
		_network_config: Option<NetworkConfig>,
	) -> SubscriptionResult {
		let key = StorageKey(parse_hex_param(&mut sink, key)?);

		let child_key = child_key
			.map(|child_key| parse_hex_param(&mut sink, child_key))
			.transpose()?
			.map(ChildInfo::new_default_from_vec);

		let client = self.client.clone();

		let fut = async move {
			// The child key is provided, use the key to query the child trie.
			if let Some(child_key) = child_key {
				// The child key must not be prefixed with ":child_storage:" nor
				// ":child_storage:default:".
				if well_known_keys::is_default_child_storage_key(child_key.storage_key()) ||
					well_known_keys::is_child_storage_key(child_key.storage_key())
				{
					let _ =
						sink.send(&ArchiveEvent::Done(ArchiveResult { result: None::<String> }));
					return
				}

				let res = client
					.child_storage(hash, &child_key, &key)
					.map(|result| {
						let result =
							result.map(|storage| format!("0x{}", HexDisplay::from(&storage.0)));
						ArchiveEvent::Done(ArchiveResult { result })
					})
					.unwrap_or_else(|error| {
						ArchiveEvent::Error(ErrorEvent { error: error.to_string() })
					});
				let _ = sink.send(&res);
				return
			}

			// The main key must not be prefixed with b":child_storage:" nor
			// b":child_storage:default:".
			if well_known_keys::is_default_child_storage_key(&key.0) ||
				well_known_keys::is_child_storage_key(&key.0)
			{
				let _ = sink.send(&ArchiveEvent::Done(ArchiveResult { result: None::<String> }));
				return
			}

			// Main root trie storage query.
			let res = client
				.storage(hash, &key)
				.map(|result| {
					let result =
						result.map(|storage| format!("0x{}", HexDisplay::from(&storage.0)));
					ArchiveEvent::Done(ArchiveResult { result })
				})
				.unwrap_or_else(|error| {
					ArchiveEvent::Error(ErrorEvent { error: error.to_string() })
				});
			let _ = sink.send(&res);
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}
}
