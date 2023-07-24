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

//! API implementation for `chainHead`.

use crate::{
	chain_head::{
		api::ChainHeadApiServer,
		chain_head_follow::ChainHeadFollower,
		error::Error as ChainHeadRpcError,
		event::{ChainHeadEvent, ChainHeadResult, ErrorEvent, FollowEvent, NetworkConfig},
		hex_string,
		subscription::{SubscriptionManagement, SubscriptionManagementError},
	},
	SubscriptionTaskExecutor,
};
use codec::Encode;
use futures::future::FutureExt;
use jsonrpsee::{
	core::{async_trait, RpcResult},
	types::{SubscriptionEmptyError, SubscriptionId, SubscriptionResult},
	SubscriptionSink,
};
use log::debug;
use sc_client_api::{
	Backend, BlockBackend, BlockchainEvents, CallExecutor, ChildInfo, ExecutorProvider, StorageKey,
	StorageProvider,
};
use sp_api::CallApiAt;
use sp_blockchain::{Error as BlockChainError, HeaderBackend, HeaderMetadata};
use sp_core::{traits::CallContext, Bytes};
use sp_runtime::traits::Block as BlockT;
use std::{marker::PhantomData, sync::Arc, time::Duration};

use super::{
	chain_head_storage::ChainHeadStorage,
	event::{ChainHeadStorageEvent, StorageQuery, StorageQueryType},
};

pub(crate) const LOG_TARGET: &str = "rpc-spec-v2";

/// An API for chain head RPC calls.
pub struct ChainHead<BE: Backend<Block>, Block: BlockT, Client> {
	/// Substrate client.
	client: Arc<Client>,
	/// Backend of the chain.
	backend: Arc<BE>,
	/// Executor to spawn subscriptions.
	executor: SubscriptionTaskExecutor,
	/// Keep track of the pinned blocks for each subscription.
	subscriptions: Arc<SubscriptionManagement<Block, BE>>,
	/// The hexadecimal encoded hash of the genesis block.
	genesis_hash: String,
	/// Phantom member to pin the block type.
	_phantom: PhantomData<Block>,
}

impl<BE: Backend<Block>, Block: BlockT, Client> ChainHead<BE, Block, Client> {
	/// Create a new [`ChainHead`].
	pub fn new<GenesisHash: AsRef<[u8]>>(
		client: Arc<Client>,
		backend: Arc<BE>,
		executor: SubscriptionTaskExecutor,
		genesis_hash: GenesisHash,
		max_pinned_blocks: usize,
		max_pinned_duration: Duration,
	) -> Self {
		let genesis_hash = hex_string(&genesis_hash.as_ref());

		Self {
			client,
			backend: backend.clone(),
			executor,
			subscriptions: Arc::new(SubscriptionManagement::new(
				max_pinned_blocks,
				max_pinned_duration,
				backend,
			)),
			genesis_hash,
			_phantom: PhantomData,
		}
	}

	/// Accept the subscription and return the subscription ID on success.
	fn accept_subscription(
		&self,
		sink: &mut SubscriptionSink,
	) -> Result<String, SubscriptionEmptyError> {
		// The subscription must be accepted before it can provide a valid subscription ID.
		sink.accept()?;

		let Some(sub_id) = sink.subscription_id() else {
			// This can only happen if the subscription was not accepted.
			return Err(SubscriptionEmptyError)
		};

		// Get the string representation for the subscription.
		let sub_id = match sub_id {
			SubscriptionId::Num(num) => num.to_string(),
			SubscriptionId::Str(id) => id.into_owned().into(),
		};

		Ok(sub_id)
	}
}

/// Parse hex-encoded string parameter as raw bytes.
///
/// If the parsing fails, the subscription is rejected.
fn parse_hex_param(
	sink: &mut SubscriptionSink,
	param: String,
) -> Result<Vec<u8>, SubscriptionEmptyError> {
	// Methods can accept empty parameters.
	if param.is_empty() {
		return Ok(Default::default())
	}

	match array_bytes::hex2bytes(&param) {
		Ok(bytes) => Ok(bytes),
		Err(_) => {
			let _ = sink.reject(ChainHeadRpcError::InvalidParam(param));
			Err(SubscriptionEmptyError)
		},
	}
}

#[async_trait]
impl<BE, Block, Client> ChainHeadApiServer<Block::Hash> for ChainHead<BE, Block, Client>
where
	Block: BlockT + 'static,
	Block::Header: Unpin,
	BE: Backend<Block> + 'static,
	Client: BlockBackend<Block>
		+ ExecutorProvider<Block>
		+ HeaderBackend<Block>
		+ HeaderMetadata<Block, Error = BlockChainError>
		+ BlockchainEvents<Block>
		+ CallApiAt<Block>
		+ StorageProvider<Block, BE>
		+ 'static,
{
	fn chain_head_unstable_follow(
		&self,
		mut sink: SubscriptionSink,
		with_runtime: bool,
	) -> SubscriptionResult {
		let sub_id = match self.accept_subscription(&mut sink) {
			Ok(sub_id) => sub_id,
			Err(err) => {
				sink.close(ChainHeadRpcError::InvalidSubscriptionID);
				return Err(err)
			},
		};
		// Keep track of the subscription.
		let Some(rx_stop) = self.subscriptions.insert_subscription(sub_id.clone(), with_runtime)
		else {
			// Inserting the subscription can only fail if the JsonRPSee
			// generated a duplicate subscription ID.
			debug!(target: LOG_TARGET, "[follow][id={:?}] Subscription already accepted", sub_id);
			let _ = sink.send(&FollowEvent::<Block::Hash>::Stop);
			return Ok(())
		};
		debug!(target: LOG_TARGET, "[follow][id={:?}] Subscription accepted", sub_id);

		let subscriptions = self.subscriptions.clone();
		let backend = self.backend.clone();
		let client = self.client.clone();
		let fut = async move {
			let mut chain_head_follow = ChainHeadFollower::new(
				client,
				backend,
				subscriptions.clone(),
				with_runtime,
				sub_id.clone(),
			);

			chain_head_follow.generate_events(sink, rx_stop).await;

			subscriptions.remove_subscription(&sub_id);
			debug!(target: LOG_TARGET, "[follow][id={:?}] Subscription removed", sub_id);
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}

	fn chain_head_unstable_body(
		&self,
		mut sink: SubscriptionSink,
		follow_subscription: String,
		hash: Block::Hash,
		_network_config: Option<NetworkConfig>,
	) -> SubscriptionResult {
		let client = self.client.clone();
		let subscriptions = self.subscriptions.clone();

		let block_guard = match subscriptions.lock_block(&follow_subscription, hash) {
			Ok(block) => block,
			Err(SubscriptionManagementError::SubscriptionAbsent) => {
				// Invalid invalid subscription ID.
				let _ = sink.send(&ChainHeadEvent::<String>::Disjoint);
				return Ok(())
			},
			Err(SubscriptionManagementError::BlockHashAbsent) => {
				// Block is not part of the subscription.
				let _ = sink.reject(ChainHeadRpcError::InvalidBlock);
				return Ok(())
			},
			Err(error) => {
				let _ = sink.send(&ChainHeadEvent::<String>::Error(ErrorEvent {
					error: error.to_string(),
				}));
				return Ok(())
			},
		};

		let fut = async move {
			let _block_guard = block_guard;
			let event = match client.block(hash) {
				Ok(Some(signed_block)) => {
					let extrinsics = signed_block.block.extrinsics();
					let result = hex_string(&extrinsics.encode());
					ChainHeadEvent::Done(ChainHeadResult { result })
				},
				Ok(None) => {
					// The block's body was pruned. This subscription ID has become invalid.
					debug!(
						target: LOG_TARGET,
						"[body][id={:?}] Stopping subscription because hash={:?} was pruned",
						&follow_subscription,
						hash
					);
					subscriptions.remove_subscription(&follow_subscription);
					ChainHeadEvent::<String>::Disjoint
				},
				Err(error) => ChainHeadEvent::Error(ErrorEvent { error: error.to_string() }),
			};
			let _ = sink.send(&event);
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}

	fn chain_head_unstable_header(
		&self,
		follow_subscription: String,
		hash: Block::Hash,
	) -> RpcResult<Option<String>> {
		let _block_guard = match self.subscriptions.lock_block(&follow_subscription, hash) {
			Ok(block) => block,
			Err(SubscriptionManagementError::SubscriptionAbsent) => {
				// Invalid invalid subscription ID.
				return Ok(None)
			},
			Err(SubscriptionManagementError::BlockHashAbsent) => {
				// Block is not part of the subscription.
				return Err(ChainHeadRpcError::InvalidBlock.into())
			},
			Err(_) => return Err(ChainHeadRpcError::InvalidBlock.into()),
		};

		self.client
			.header(hash)
			.map(|opt_header| opt_header.map(|h| hex_string(&h.encode())))
			.map_err(ChainHeadRpcError::FetchBlockHeader)
			.map_err(Into::into)
	}

	fn chain_head_unstable_genesis_hash(&self) -> RpcResult<String> {
		Ok(self.genesis_hash.clone())
	}

	fn chain_head_unstable_storage(
		&self,
		mut sink: SubscriptionSink,
		follow_subscription: String,
		hash: Block::Hash,
		items: Vec<StorageQuery<String>>,
		child_trie: Option<String>,
		_network_config: Option<NetworkConfig>,
	) -> SubscriptionResult {
		// Gain control over parameter parsing and returned error.
		let items = items
			.into_iter()
			.map(|query| {
				if query.queue_type != StorageQueryType::Value &&
					query.queue_type != StorageQueryType::Hash
				{
					// Note: remove this once all types are implemented.
					let _ = sink.reject(ChainHeadRpcError::InvalidParam(
						"Storage query type not supported".into(),
					));
					return Err(SubscriptionEmptyError)
				}

				Ok(StorageQuery {
					key: StorageKey(parse_hex_param(&mut sink, query.key)?),
					queue_type: query.queue_type,
				})
			})
			.collect::<Result<Vec<_>, _>>()?;

		let child_trie = child_trie
			.map(|child_trie| parse_hex_param(&mut sink, child_trie))
			.transpose()?
			.map(ChildInfo::new_default_from_vec);

		let client = self.client.clone();
		let subscriptions = self.subscriptions.clone();

		let block_guard = match subscriptions.lock_block(&follow_subscription, hash) {
			Ok(block) => block,
			Err(SubscriptionManagementError::SubscriptionAbsent) => {
				// Invalid invalid subscription ID.
				let _ = sink.send(&ChainHeadStorageEvent::<String>::Disjoint);
				return Ok(())
			},
			Err(SubscriptionManagementError::BlockHashAbsent) => {
				// Block is not part of the subscription.
				let _ = sink.reject(ChainHeadRpcError::InvalidBlock);
				return Ok(())
			},
			Err(error) => {
				let _ = sink.send(&ChainHeadStorageEvent::<String>::Error(ErrorEvent {
					error: error.to_string(),
				}));
				return Ok(())
			},
		};

		let storage_client = ChainHeadStorage::<Client, Block, BE>::new(client);

		let fut = async move {
			let _block_guard = block_guard;

			storage_client.generate_events(sink, hash, items, child_trie);
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}

	fn chain_head_unstable_call(
		&self,
		mut sink: SubscriptionSink,
		follow_subscription: String,
		hash: Block::Hash,
		function: String,
		call_parameters: String,
		_network_config: Option<NetworkConfig>,
	) -> SubscriptionResult {
		let call_parameters = Bytes::from(parse_hex_param(&mut sink, call_parameters)?);

		let client = self.client.clone();
		let subscriptions = self.subscriptions.clone();

		let block_guard = match subscriptions.lock_block(&follow_subscription, hash) {
			Ok(block) => block,
			Err(SubscriptionManagementError::SubscriptionAbsent) => {
				// Invalid invalid subscription ID.
				let _ = sink.send(&ChainHeadEvent::<String>::Disjoint);
				return Ok(())
			},
			Err(SubscriptionManagementError::BlockHashAbsent) => {
				// Block is not part of the subscription.
				let _ = sink.reject(ChainHeadRpcError::InvalidBlock);
				return Ok(())
			},
			Err(error) => {
				let _ = sink.send(&ChainHeadEvent::<String>::Error(ErrorEvent {
					error: error.to_string(),
				}));
				return Ok(())
			},
		};

		let fut = async move {
			// Reject subscription if with_runtime is false.
			if !block_guard.has_runtime() {
				let _ = sink.reject(ChainHeadRpcError::InvalidParam(
					"The runtime updates flag must be set".into(),
				));
				return
			}

			let res = client
				.executor()
				.call(hash, &function, &call_parameters, CallContext::Offchain)
				.map(|result| {
					let result = hex_string(&result);
					ChainHeadEvent::Done(ChainHeadResult { result })
				})
				.unwrap_or_else(|error| {
					ChainHeadEvent::Error(ErrorEvent { error: error.to_string() })
				});

			let _ = sink.send(&res);
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}

	fn chain_head_unstable_unpin(
		&self,
		follow_subscription: String,
		hash: Block::Hash,
	) -> RpcResult<()> {
		match self.subscriptions.unpin_block(&follow_subscription, hash) {
			Ok(()) => Ok(()),
			Err(SubscriptionManagementError::SubscriptionAbsent) => {
				// Invalid invalid subscription ID.
				Ok(())
			},
			Err(SubscriptionManagementError::BlockHashAbsent) => {
				// Block is not part of the subscription.
				Err(ChainHeadRpcError::InvalidBlock.into())
			},
			Err(_) => Err(ChainHeadRpcError::InvalidBlock.into()),
		}
	}
}
