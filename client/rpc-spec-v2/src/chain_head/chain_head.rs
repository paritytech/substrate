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
use std::{marker::PhantomData, sync::Arc};
use sc_client_api::CallExecutor;
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
	Backend, BlockBackend, BlockchainEvents, ExecutorProvider, StorageKey, StorageProvider,
};
use sp_api::CallApiAt;
use sp_blockchain::HeaderBackend;
use sp_core::{hexdisplay::HexDisplay, Bytes};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header},
};

/// An API for chain head RPC calls.
pub struct ChainHead<BE, Block: BlockT, Client> {
	/// Substrate client.
	client: Arc<Client>,
	/// Executor to spawn subscriptions.
	executor: SubscriptionTaskExecutor,
	/// Keep track of the pinned blocks for each subscription.
	subscriptions: Arc<SubscriptionManagement<Block>>,
	/// Phantom member to pin the block type.
	_phantom: PhantomData<(Block, BE)>,
}

impl<BE, Block: BlockT, Client> ChainHead<BE, Block, Client> {
	/// Create a new [`ChainHead`].
	pub fn new(client: Arc<Client>, executor: SubscriptionTaskExecutor) -> Self {
		Self {
			client,
			executor,
			subscriptions: Arc::new(SubscriptionManagement::new()),
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
		mut _sink: SubscriptionSink,
		_runtime_updates: bool,
	) -> SubscriptionResult {
		Ok(())
	}

	fn chain_head_unstable_body(
		&self,
		mut _sink: SubscriptionSink,
		_follow_subscription: String,
		_hash: Block::Hash,
		_network_config: Option<()>,
	) -> SubscriptionResult {
		Ok(())
	}

	fn chain_head_unstable_header(
		&self,
		_follow_subscription: String,
		_hash: Block::Hash,
	) -> RpcResult<Option<String>> {
		Ok(None)
	}

	fn chain_head_unstable_storage(
		&self,
		mut _sink: SubscriptionSink,
		_follow_subscription: String,
		_hash: Block::Hash,
		_key: StorageKey,
		_child_key: Option<StorageKey>,
		_network_config: Option<()>,
	) -> SubscriptionResult {
		Ok(())
	}

	fn chain_head_unstable_call(
		&self,
		mut _sink: SubscriptionSink,
		_follow_subscription: String,
		_hash: Block::Hash,
		_function: String,
		_call_parameters: Bytes,
		_network_config: Option<()>,
	) -> SubscriptionResult {
		Ok(())
	}

	fn chain_head_unstable_unpin(
		&self,
		_follow_subscription: String,
		_hash: Block::Hash,
	) -> RpcResult<()> {
		Ok(())
	}
}
