// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

//! Chain api required for the transaction pool.

use codec::Encode;
use futures::{
	channel::{mpsc, oneshot},
	future::{ready, Future, FutureExt, Ready},
	lock::Mutex,
	SinkExt, StreamExt,
};
use std::{marker::PhantomData, pin::Pin, sync::Arc};

use prometheus_endpoint::Registry as PrometheusRegistry;
use sc_client_api::{blockchain::HeaderBackend, BlockBackend};
use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_blockchain::{HeaderMetadata, TreeRoute};
use sp_core::traits::SpawnEssentialNamed;
use sp_runtime::{
	generic::BlockId,
	traits::{self, Block as BlockT, BlockIdTo},
	transaction_validity::{TransactionSource, TransactionValidity},
};
use sp_transaction_pool::runtime_api::TaggedTransactionQueue;

use crate::{
	error::{self, Error},
	graph,
	metrics::{ApiMetrics, ApiMetricsExt},
};

/// The transaction pool logic for full client.
pub struct FullChainApi<Client, Block> {
	client: Arc<Client>,
	_marker: PhantomData<Block>,
	metrics: Option<Arc<ApiMetrics>>,
	validation_pool: Arc<Mutex<mpsc::Sender<Pin<Box<dyn Future<Output = ()> + Send>>>>>,
}

/// Spawn a validation task that will be used by the transaction pool to validate transactions.
fn spawn_validation_pool_task(
	name: &'static str,
	receiver: Arc<Mutex<mpsc::Receiver<Pin<Box<dyn Future<Output = ()> + Send>>>>>,
	spawner: &impl SpawnEssentialNamed,
) {
	spawner.spawn_essential_blocking(
		name,
		Some("transaction-pool"),
		async move {
			loop {
				let task = receiver.lock().await.next().await;
				match task {
					None => return,
					Some(task) => task.await,
				}
			}
		}
		.boxed(),
	);
}

impl<Client, Block> FullChainApi<Client, Block> {
	/// Create new transaction pool logic.
	pub fn new(
		client: Arc<Client>,
		prometheus: Option<&PrometheusRegistry>,
		spawner: &impl SpawnEssentialNamed,
	) -> Self {
		let metrics = prometheus.map(ApiMetrics::register).and_then(|r| match r {
			Err(err) => {
				log::warn!(
					target: "txpool",
					"Failed to register transaction pool api prometheus metrics: {:?}",
					err,
				);
				None
			},
			Ok(api) => Some(Arc::new(api)),
		});

		let (sender, receiver) = mpsc::channel(0);

		let receiver = Arc::new(Mutex::new(receiver));
		spawn_validation_pool_task("transaction-pool-task-0", receiver.clone(), spawner);
		spawn_validation_pool_task("transaction-pool-task-1", receiver, spawner);

		FullChainApi {
			client,
			validation_pool: Arc::new(Mutex::new(sender)),
			_marker: Default::default(),
			metrics,
		}
	}
}

impl<Client, Block> graph::ChainApi for FullChainApi<Client, Block>
where
	Block: BlockT,
	Client: ProvideRuntimeApi<Block>
		+ BlockBackend<Block>
		+ BlockIdTo<Block>
		+ HeaderBackend<Block>
		+ HeaderMetadata<Block, Error = sp_blockchain::Error>,
	Client: Send + Sync + 'static,
	Client::Api: TaggedTransactionQueue<Block>,
{
	type Block = Block;
	type Error = error::Error;
	type ValidationFuture =
		Pin<Box<dyn Future<Output = error::Result<TransactionValidity>> + Send>>;
	type BodyFuture = Ready<error::Result<Option<Vec<<Self::Block as BlockT>::Extrinsic>>>>;

	fn block_body(&self, id: &BlockId<Self::Block>) -> Self::BodyFuture {
		ready(self.client.block_body(id).map_err(error::Error::from))
	}

	fn validate_transaction(
		&self,
		at: &BlockId<Self::Block>,
		source: TransactionSource,
		uxt: graph::ExtrinsicFor<Self>,
	) -> Self::ValidationFuture {
		let (tx, rx) = oneshot::channel();
		let client = self.client.clone();
		let at = *at;
		let validation_pool = self.validation_pool.clone();
		let metrics = self.metrics.clone();

		async move {
			metrics.report(|m| m.validations_scheduled.inc());

			validation_pool
				.lock()
				.await
				.send(
					async move {
						let res = validate_transaction_blocking(&*client, &at, source, uxt);
						let _ = tx.send(res);
						metrics.report(|m| m.validations_finished.inc());
					}
					.boxed(),
				)
				.await
				.map_err(|e| Error::RuntimeApi(format!("Validation pool down: {:?}", e)))?;

			match rx.await {
				Ok(r) => r,
				Err(_) => Err(Error::RuntimeApi("Validation was canceled".into())),
			}
		}
		.boxed()
	}

	fn block_id_to_number(
		&self,
		at: &BlockId<Self::Block>,
	) -> error::Result<Option<graph::NumberFor<Self>>> {
		self.client.to_number(at).map_err(|e| Error::BlockIdConversion(e.to_string()))
	}

	fn block_id_to_hash(
		&self,
		at: &BlockId<Self::Block>,
	) -> error::Result<Option<graph::BlockHash<Self>>> {
		self.client.to_hash(at).map_err(|e| Error::BlockIdConversion(e.to_string()))
	}

	fn hash_and_length(
		&self,
		ex: &graph::ExtrinsicFor<Self>,
	) -> (graph::ExtrinsicHash<Self>, usize) {
		ex.using_encoded(|x| (<traits::HashFor<Block> as traits::Hash>::hash(x), x.len()))
	}

	fn block_header(
		&self,
		at: &BlockId<Self::Block>,
	) -> Result<Option<<Self::Block as BlockT>::Header>, Self::Error> {
		self.client.header(*at).map_err(Into::into)
	}

	fn tree_route(
		&self,
		from: <Self::Block as BlockT>::Hash,
		to: <Self::Block as BlockT>::Hash,
	) -> Result<TreeRoute<Self::Block>, Self::Error> {
		sp_blockchain::tree_route::<Block, Client>(&*self.client, from, to).map_err(Into::into)
	}
}

/// Helper function to validate a transaction using a full chain API.
/// This method will call into the runtime to perform the validation.
fn validate_transaction_blocking<Client, Block>(
	client: &Client,
	at: &BlockId<Block>,
	source: TransactionSource,
	uxt: graph::ExtrinsicFor<FullChainApi<Client, Block>>,
) -> error::Result<TransactionValidity>
where
	Block: BlockT,
	Client: ProvideRuntimeApi<Block>
		+ BlockBackend<Block>
		+ BlockIdTo<Block>
		+ HeaderBackend<Block>
		+ HeaderMetadata<Block, Error = sp_blockchain::Error>,
	Client: Send + Sync + 'static,
	Client::Api: TaggedTransactionQueue<Block>,
{
	sp_tracing::within_span!(sp_tracing::Level::TRACE, "validate_transaction";
	{
		let runtime_api = client.runtime_api();
		let api_version = sp_tracing::within_span! { sp_tracing::Level::TRACE, "check_version";
			runtime_api
				.api_version::<dyn TaggedTransactionQueue<Block>>(at)
				.map_err(|e| Error::RuntimeApi(e.to_string()))?
				.ok_or_else(|| Error::RuntimeApi(
					format!("Could not find `TaggedTransactionQueue` api for block `{:?}`.", at)
				))
		}?;

		let block_hash = client.to_hash(at)
			.map_err(|e| Error::RuntimeApi(e.to_string()))?
			.ok_or_else(|| Error::RuntimeApi(format!("Could not get hash for block `{:?}`.", at)))?;

		use sp_api::Core;

		sp_tracing::within_span!(
			sp_tracing::Level::TRACE, "runtime::validate_transaction";
		{
			if api_version >= 3 {
				runtime_api.validate_transaction(at, source, uxt, block_hash)
					.map_err(|e| Error::RuntimeApi(e.to_string()))
			} else {
				let block_number = client.to_number(at)
					.map_err(|e| Error::RuntimeApi(e.to_string()))?
					.ok_or_else(||
						Error::RuntimeApi(format!("Could not get number for block `{:?}`.", at))
					)?;

				// The old versions require us to call `initialize_block` before.
				runtime_api.initialize_block(at, &sp_runtime::traits::Header::new(
					block_number + sp_runtime::traits::One::one(),
					Default::default(),
					Default::default(),
					block_hash,
					Default::default()),
				).map_err(|e| Error::RuntimeApi(e.to_string()))?;

				if api_version == 2 {
					#[allow(deprecated)] // old validate_transaction
					runtime_api.validate_transaction_before_version_3(at, source, uxt)
						.map_err(|e| Error::RuntimeApi(e.to_string()))
				} else {
					#[allow(deprecated)] // old validate_transaction
					runtime_api.validate_transaction_before_version_2(at, uxt)
						.map_err(|e| Error::RuntimeApi(e.to_string()))
				}
			}
		})
	})
}

impl<Client, Block> FullChainApi<Client, Block>
where
	Block: BlockT,
	Client: ProvideRuntimeApi<Block>
		+ BlockBackend<Block>
		+ BlockIdTo<Block>
		+ HeaderBackend<Block>
		+ HeaderMetadata<Block, Error = sp_blockchain::Error>,
	Client: Send + Sync + 'static,
	Client::Api: TaggedTransactionQueue<Block>,
{
	/// Validates a transaction by calling into the runtime, same as
	/// `validate_transaction` but blocks the current thread when performing
	/// validation. Only implemented for `FullChainApi` since we can call into
	/// the runtime locally.
	pub fn validate_transaction_blocking(
		&self,
		at: &BlockId<Block>,
		source: TransactionSource,
		uxt: graph::ExtrinsicFor<Self>,
	) -> error::Result<TransactionValidity> {
		validate_transaction_blocking(&*self.client, at, source, uxt)
	}
}
