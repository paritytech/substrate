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

//! API implementation for submitting transactions.

use crate::{
	transaction::{
		api::TransactionApiServer,
		error::Error,
		event::{TransactionBlock, TransactionBroadcasted, TransactionError, TransactionEvent},
	},
	SubscriptionTaskExecutor,
};
use jsonrpsee::{core::async_trait, types::SubscriptionResult, SubscriptionSink};
use sc_transaction_pool_api::{
	error::IntoPoolError, BlockHash, TransactionFor, TransactionPool, TransactionSource,
	TransactionStatus,
};
use std::sync::Arc;

use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_core::Bytes;
use sp_runtime::{generic, traits::Block as BlockT};

use codec::Decode;
use futures::{FutureExt, StreamExt, TryFutureExt};
use jsonrpsee::types::error::CallError;

/// An API for transaction RPC calls.
pub struct Transaction<Pool, Client> {
	/// Substrate client.
	client: Arc<Client>,
	/// Transactions pool.
	pool: Arc<Pool>,
	/// Executor to spawn subscriptions.
	executor: SubscriptionTaskExecutor,
}

impl<Pool, Client> Transaction<Pool, Client> {
	/// Creates a new [`Transaction`].
	pub fn new(client: Arc<Client>, pool: Arc<Pool>, executor: SubscriptionTaskExecutor) -> Self {
		Transaction { client, pool, executor }
	}
}

/// Currently we treat all RPC transactions as externals.
///
/// Possibly in the future we could allow opt-in for special treatment
/// of such transactions, so that the block authors can inject
/// some unique transactions via RPC and have them included in the pool.
const TX_SOURCE: TransactionSource = TransactionSource::External;

#[async_trait]
impl<Pool, Client> TransactionApiServer<BlockHash<Pool>> for Transaction<Pool, Client>
where
	Pool: TransactionPool + Sync + Send + 'static,
	Pool::Hash: Unpin,
	<Pool::Block as BlockT>::Hash: Unpin,
	Client: HeaderBackend<Pool::Block> + ProvideRuntimeApi<Pool::Block> + Send + Sync + 'static,
{
	fn submit_and_watch(&self, mut sink: SubscriptionSink, xt: Bytes) -> SubscriptionResult {
		// This is the only place where the RPC server can return an error for this
		// subscription. Other defects must be signaled as events to the sink.
		let decoded_extrinsic = match TransactionFor::<Pool>::decode(&mut &xt[..]) {
			Ok(decoded_extrinsic) => decoded_extrinsic,
			Err(e) => {
				let err = CallError::Failed(e.into());
				let _ = sink.reject(err);
				return Ok(())
			},
		};

		Ok(())
	}
}
