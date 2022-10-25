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

//! API implementation for `chainHead`.

use crate::{
	chain_head::{
		api::ChainHeadApiServer,
		error::Error as ChainHeadRpcError,
		event::{
			BestBlockChanged, ChainHeadEvent, ChainHeadResult, ErrorEvent, Finalized, FollowEvent,
			Initialized, NewBlock, RuntimeEvent, RuntimeVersionEvent,
		},
		subscription::{SubscriptionError, SubscriptionManagement},
	},
	SubscriptionTaskExecutor,
};
use codec::Encode;
use futures::{
	future::FutureExt,
	stream::{self, StreamExt},
};
use jsonrpsee::{
	core::{async_trait, error::SubscriptionClosed, RpcResult},
	types::{SubscriptionEmptyError, SubscriptionResult},
	SubscriptionSink,
};
use sc_client_api::{
	Backend, BlockBackend, BlockchainEvents, CallExecutor, ExecutorProvider, StorageKey,
	StorageProvider,
};
use sp_api::CallApiAt;
use sp_blockchain::HeaderBackend;
use sp_core::{hexdisplay::HexDisplay, Bytes};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header},
};
use std::{marker::PhantomData, sync::Arc};

/// An API for chain head RPC calls.
pub struct ChainHead<BE, Block: BlockT, Client> {
	/// Substrate client.
	client: Arc<Client>,
	/// Executor to spawn subscriptions.
	executor: SubscriptionTaskExecutor,
	/// Keep track of the pinned blocks for each subscription.
	subscriptions: Arc<SubscriptionManagement<Block>>,
	/// The hexadecimal encoded hash of the genesis block.
	genesis_hash: String,
	/// Phantom member to pin the block type.
	_phantom: PhantomData<(Block, BE)>,
}
impl<BE, Block: BlockT, Client> ChainHead<BE, Block, Client> {
	/// Create a new [`ChainHead`].
	pub fn new<GenesisHash: AsRef<[u8]>>(
		client: Arc<Client>,
		executor: SubscriptionTaskExecutor,
		genesis_hash: GenesisHash,
	) -> Self {
		let genesis_hash = format!("0x{}", hex::encode(genesis_hash));

		Self {
			client,
			executor,
			subscriptions: Arc::new(SubscriptionManagement::new()),
			genesis_hash,
			_phantom: PhantomData,
		}
	}

	/// Accept the subscription and return the subscription ID on success.
	///
	/// Also keep track of the subscription ID internally.
	fn accept_subscription(
		&self,
		sink: &mut SubscriptionSink,
	) -> Result<String, SubscriptionEmptyError> {
		// The subscription must be accepted before it can provide a valid subscription ID.
		sink.accept()?;

		// TODO: Jsonrpsee needs release + merge in substrate
		// let sub_id = match sink.subscription_id() {
		// 	Some(id) => id,
		// 	// This can only happen if the subscription was not accepted.
		// 	None => {
		// 		let err = ErrorObject::owned(PARSE_ERROR_CODE, "invalid subscription ID", None);
		// 		sink.close(err);
		// 		return Err(SubscriptionEmptyError)
		// 	}
		// };
		// // Get the string representation for the subscription.
		// let sub_id = match serde_json::to_string(&sub_id) {
		// 	Ok(sub_id) => sub_id,
		// 	Err(err) => {
		// 		sink.close(err);
		// 		return Err(SubscriptionEmptyError)
		// 	},
		// };

		let sub_id: String = "A".into();
		Ok(sub_id)
	}
}

fn parse_hex_param(
	sink: &mut SubscriptionSink,
	param: String,
) -> Result<Vec<u8>, SubscriptionEmptyError> {
	match array_bytes::hex2bytes(&param) {
		Ok(bytes) => Ok(bytes),
		Err(_) => {
			let _ = sink.reject(ChainHeadRpcError::InvalidParam(param));
			Err(SubscriptionEmptyError)
		},
	}
}

fn generate_runtime_event<Client, Block>(
	client: &Arc<Client>,
	runtime_updates: bool,
	block: &BlockId<Block>,
	parent: Option<&BlockId<Block>>,
) -> Option<RuntimeEvent>
where
	Block: BlockT + 'static,
	Client: CallApiAt<Block> + 'static,
{
	// No runtime versions should be reported.
	if runtime_updates {
		return None
	}

	// Helper for uniform conversions on errors.
	let to_event_err =
		|err| Some(RuntimeEvent::Invalid(ErrorEvent { error: format!("Api error: {}", err) }));

	let block_rt = match client.runtime_version_at(block) {
		Ok(rt) => rt,
		Err(err) => return to_event_err(err),
	};

	let parent = match parent {
		Some(parent) => parent,
		// Nothing to compare against, always report.
		None => return Some(RuntimeEvent::Valid(RuntimeVersionEvent { spec: block_rt })),
	};

	let parent_rt = match client.runtime_version_at(parent) {
		Ok(rt) => rt,
		Err(err) => return to_event_err(err),
	};

	// Report the runtime version change.
	if block_rt != parent_rt {
		Some(RuntimeEvent::Valid(RuntimeVersionEvent { spec: block_rt }))
	} else {
		None
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
		+ BlockchainEvents<Block>
		+ CallApiAt<Block>
		+ StorageProvider<Block, BE>
		+ 'static,
{
	fn chain_head_unstable_follow(
		&self,
		mut sink: SubscriptionSink,
		runtime_updates: bool,
	) -> SubscriptionResult {
		let sub_id = self.accept_subscription(&mut sink)?;
		// Keep track of the subscription.
		self.subscriptions.insert_subscription(sub_id.clone());

		let client = self.client.clone();
		let subscriptions = self.subscriptions.clone();

		let sub_id_import = sub_id.clone();
		let stream_import = self
			.client
			.import_notification_stream()
			.map(move |notification| {
				let new_runtime = generate_runtime_event(
					&client,
					runtime_updates,
					&BlockId::Hash(notification.hash),
					Some(&BlockId::Hash(*notification.header.parent_hash())),
				);

				let _ = subscriptions.pin_block(&sub_id_import, notification.hash);

				// Note: `Block::Hash` will serialize to hexadecimal encoded string.
				let new_block = FollowEvent::NewBlock(NewBlock {
					block_hash: notification.hash,
					parent_block_hash: *notification.header.parent_hash(),
					new_runtime,
					runtime_updates,
				});

				if !notification.is_new_best {
					return stream::iter(vec![new_block])
				}

				// If this is the new best block, then we need to generate two events.
				let best_block = FollowEvent::BestBlockChanged(BestBlockChanged {
					best_block_hash: notification.hash,
				});
				stream::iter(vec![new_block, best_block])
			})
			.flatten();

		let subscriptions = self.subscriptions.clone();
		let sub_id_finalized = sub_id.clone();

		let stream_finalized =
			self.client.finality_notification_stream().map(move |notification| {
				// We might not receive all new blocks reports, also pin the block here.
				let _ = subscriptions.pin_block(&sub_id_finalized, notification.hash);

				FollowEvent::Finalized(Finalized {
					finalized_block_hashes: notification.tree_route.iter().cloned().collect(),
					pruned_block_hashes: notification.stale_heads.iter().cloned().collect(),
				})
			});

		let merged = tokio_stream::StreamExt::merge(stream_import, stream_finalized);

		// The initialized event is the first one sent.
		let finalized_block_hash = self.client.info().finalized_hash;
		let finalized_block_runtime = generate_runtime_event(
			&self.client,
			runtime_updates,
			&BlockId::Hash(finalized_block_hash),
			None,
		);

		let _ = self.subscriptions.pin_block(&sub_id, finalized_block_hash);

		let stream = stream::once(async move {
			FollowEvent::Initialized(Initialized {
				finalized_block_hash,
				finalized_block_runtime,
				runtime_updates,
			})
		})
		.chain(merged);

		let subscriptions = self.subscriptions.clone();
		let fut = async move {
			if let SubscriptionClosed::Failed(_) = sink.pipe_from_stream(stream.boxed()).await {
				// The subscription failed to pipe from the stream.
				let _ = sink.send(&FollowEvent::<Block::Hash>::Stop);
			}

			// The client disconnected or called the unsubscribe method.
			subscriptions.remove_subscription(&sub_id);
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}

	fn chain_head_unstable_body(
		&self,
		mut sink: SubscriptionSink,
		follow_subscription: String,
		hash: Block::Hash,
		_network_config: Option<()>,
	) -> SubscriptionResult {
		let client = self.client.clone();
		let subscriptions = self.subscriptions.clone();

		let fut = async move {
			let res = match subscriptions.contains(&follow_subscription, &hash) {
				Err(SubscriptionError::InvalidBlock) => {
					let _ = sink.reject(ChainHeadRpcError::InvalidBlock);
					return
				},
				Err(SubscriptionError::InvalidSubId) => ChainHeadEvent::<String>::Disjoint,
				Ok(()) => match client.block(&BlockId::Hash(hash)) {
					Ok(Some(signed_block)) => {
						let extrinsics = signed_block.block.extrinsics();
						let result = format!("0x{}", HexDisplay::from(&extrinsics.encode()));
						ChainHeadEvent::Done(ChainHeadResult { result })
					},
					Ok(None) => {
						// The block's body was pruned. This subscription ID has become invalid.
						// TODO: Stop the `follow` method.
						ChainHeadEvent::<String>::Disjoint
					},
					Err(error) => ChainHeadEvent::Error(ErrorEvent { error: error.to_string() }),
				},
			};

			let stream = stream::once(async move { res });
			sink.pipe_from_stream(stream.boxed()).await;
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}

	fn chain_head_unstable_header(
		&self,
		follow_subscription: String,
		hash: Block::Hash,
	) -> RpcResult<Option<String>> {
		match self.subscriptions.contains(&follow_subscription, &hash) {
			Err(SubscriptionError::InvalidBlock) =>
				return Err(ChainHeadRpcError::InvalidBlock.into()),
			Err(SubscriptionError::InvalidSubId) => return Ok(None),
			_ => (),
		};

		self.client
			.header(BlockId::Hash(hash))
			.map(|opt_header| opt_header.map(|h| format!("0x{}", HexDisplay::from(&h.encode()))))
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
		key: String,
		_child_key: Option<String>,
		_network_config: Option<()>,
	) -> SubscriptionResult {
		let key = StorageKey(parse_hex_param(&mut sink, key)?);

		let client = self.client.clone();
		let subscriptions = self.subscriptions.clone();

		let fut = async move {
			let res = match subscriptions.contains(&follow_subscription, &hash) {
				Err(SubscriptionError::InvalidBlock) => {
					let _ = sink.reject(ChainHeadRpcError::InvalidBlock);
					return
				},
				Err(SubscriptionError::InvalidSubId) => ChainHeadEvent::<Option<String>>::Disjoint,
				Ok(()) => match client.storage(&hash, &key) {
					Ok(result) => {
						let result =
							result.map(|storage| format!("0x{}", HexDisplay::from(&storage.0)));
						ChainHeadEvent::Done(ChainHeadResult { result })
					},
					Err(error) => ChainHeadEvent::Error(ErrorEvent { error: error.to_string() }),
				},
			};

			let stream = stream::once(async move { res });
			sink.pipe_from_stream(stream.boxed()).await;
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
		_network_config: Option<()>,
	) -> SubscriptionResult {
		let call_parameters = Bytes::from(parse_hex_param(&mut sink, call_parameters)?);

		let client = self.client.clone();
		let subscriptions = self.subscriptions.clone();

		let fut = async move {
			let res = match subscriptions.contains(&follow_subscription, &hash) {
				// TODO: Reject subscription if runtime_updates is false.
				Err(SubscriptionError::InvalidBlock) => {
					let _ = sink.reject(ChainHeadRpcError::InvalidBlock);
					return
				},
				Err(SubscriptionError::InvalidSubId) => ChainHeadEvent::<String>::Disjoint,
				Ok(()) => {
					match client.executor().call(
						&BlockId::Hash(hash),
						&function,
						&call_parameters,
						client.execution_extensions().strategies().other,
						None,
					) {
						Ok(result) => {
							let result = format!("0x{}", HexDisplay::from(&result));
							ChainHeadEvent::Done(ChainHeadResult { result })
						},
						Err(error) =>
							ChainHeadEvent::Error(ErrorEvent { error: error.to_string() }),
					}
				},
			};

			let stream = stream::once(async move { res });
			sink.pipe_from_stream(stream.boxed()).await;
		};

		self.executor.spawn("substrate-rpc-subscription", Some("rpc"), fut.boxed());
		Ok(())
	}

	fn chain_head_unstable_unpin(
		&self,
		follow_subscription: String,
		hash: Block::Hash,
	) -> RpcResult<()> {
		match self.subscriptions.unpin_block(&follow_subscription, &hash) {
			Err(SubscriptionError::InvalidBlock) => Err(ChainHeadRpcError::InvalidBlock.into()),
			_ => Ok(()),
		}
	}
}
