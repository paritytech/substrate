// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

use std::{marker::PhantomData, pin::Pin, sync::Arc};
use codec::{Decode, Encode};
use futures::{
	channel::{oneshot, mpsc}, future::{Future, FutureExt, ready, Ready}, lock::Mutex, SinkExt,
	StreamExt,
};

use sc_client_api::{
	blockchain::HeaderBackend, light::{Fetcher, RemoteCallRequest, RemoteBodyRequest}, BlockBackend,
};
use sp_runtime::{
	generic::BlockId, traits::{self, Block as BlockT, BlockIdTo, Header as HeaderT, Hash as HashT},
	transaction_validity::{TransactionValidity, TransactionSource},
};
use sp_transaction_pool::runtime_api::TaggedTransactionQueue;
use sp_api::{ProvideRuntimeApi, ApiExt};
use prometheus_endpoint::Registry as PrometheusRegistry;
use sp_core::traits::SpawnEssentialNamed;

use crate::{metrics::{ApiMetrics, ApiMetricsExt}, error::{self, Error}};

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
		async move {
			loop {
				let task = receiver.lock().await.next().await;
				match task {
					None => return,
					Some(task) => task.await,
				}
			}
		}.boxed(),
	);
}

impl<Client, Block> FullChainApi<Client, Block> {
	/// Create new transaction pool logic.
	pub fn new(
		client: Arc<Client>,
		prometheus: Option<&PrometheusRegistry>,
		spawner: &impl SpawnEssentialNamed,
	) -> Self {
		let metrics = prometheus.map(ApiMetrics::register).and_then(|r| {
			match r {
				Err(err) => {
					log::warn!(
						target: "txpool",
						"Failed to register transaction pool api prometheus metrics: {:?}",
						err,
					);
					None
				},
				Ok(api) => Some(Arc::new(api))
			}
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

impl<Client, Block> sc_transaction_graph::ChainApi for FullChainApi<Client, Block>
where
	Block: BlockT,
	Client: ProvideRuntimeApi<Block> + BlockBackend<Block> + BlockIdTo<Block> + HeaderBackend<Block>,
	Client: Send + Sync + 'static,
	Client::Api: TaggedTransactionQueue<Block>,
{
	type Block = Block;
	type Error = error::Error;
	type ValidationFuture = Pin<
		Box<dyn Future<Output = error::Result<TransactionValidity>> + Send>
	>;
	type BodyFuture = Ready<error::Result<Option<Vec<<Self::Block as BlockT>::Extrinsic>>>>;

	fn block_body(&self, id: &BlockId<Self::Block>) -> Self::BodyFuture {
		ready(self.client.block_body(&id).map_err(|e| error::Error::from(e)))
	}

	fn validate_transaction(
		&self,
		at: &BlockId<Self::Block>,
		source: TransactionSource,
		uxt: sc_transaction_graph::ExtrinsicFor<Self>,
	) -> Self::ValidationFuture {
		let (tx, rx) = oneshot::channel();
		let client = self.client.clone();
		let at = at.clone();
		let validation_pool = self.validation_pool.clone();
		let metrics = self.metrics.clone();

		async move {
			metrics.report(|m| m.validations_scheduled.inc());

			validation_pool.lock()
				.await
				.send(
					async move {
						let res = validate_transaction_blocking(&*client, &at, source, uxt);
						let _ = tx.send(res);
						metrics.report(|m| m.validations_finished.inc());
					}.boxed()
				)
				.await
				.map_err(|e| Error::RuntimeApi(format!("Validation pool down: {:?}", e)))?;

			match rx.await {
				Ok(r) => r,
				Err(_) => Err(Error::RuntimeApi("Validation was canceled".into())),
			}
		}.boxed()
	}

	fn block_id_to_number(
		&self,
		at: &BlockId<Self::Block>,
	) -> error::Result<Option<sc_transaction_graph::NumberFor<Self>>> {
		self.client.to_number(at).map_err(|e| Error::BlockIdConversion(format!("{:?}", e)))
	}

	fn block_id_to_hash(
		&self,
		at: &BlockId<Self::Block>,
	) -> error::Result<Option<sc_transaction_graph::BlockHash<Self>>> {
		self.client.to_hash(at).map_err(|e| Error::BlockIdConversion(format!("{:?}", e)))
	}

	fn hash_and_length(
		&self,
		ex: &sc_transaction_graph::ExtrinsicFor<Self>,
	) -> (sc_transaction_graph::ExtrinsicHash<Self>, usize) {
		ex.using_encoded(|x| {
			(<traits::HashFor::<Block> as traits::Hash>::hash(x), x.len())
		})
	}

	fn block_header(
		&self,
		at: &BlockId<Self::Block>,
	) -> Result<Option<<Self::Block as BlockT>::Header>, Self::Error> {
		self.client.header(*at).map_err(Into::into)
	}
}

/// Helper function to validate a transaction using a full chain API.
/// This method will call into the runtime to perform the validation.
fn validate_transaction_blocking<Client, Block>(
	client: &Client,
	at: &BlockId<Block>,
	source: TransactionSource,
	uxt: sc_transaction_graph::ExtrinsicFor<FullChainApi<Client, Block>>,
) -> error::Result<TransactionValidity>
where
	Block: BlockT,
	Client: ProvideRuntimeApi<Block> + BlockBackend<Block> + BlockIdTo<Block> + HeaderBackend<Block>,
	Client: Send + Sync + 'static,
	Client::Api: TaggedTransactionQueue<Block>,
{
	sp_tracing::within_span!(sp_tracing::Level::TRACE, "validate_transaction";
	{
		let runtime_api = client.runtime_api();
		let api_version = sp_tracing::within_span! { sp_tracing::Level::TRACE, "check_version";
			runtime_api
				.api_version::<dyn TaggedTransactionQueue<Block>>(&at)
				.map_err(|e| Error::RuntimeApi(e.to_string()))?
				.ok_or_else(|| Error::RuntimeApi(
					format!("Could not find `TaggedTransactionQueue` api for block `{:?}`.", at)
				))
		}?;

		let block_hash = client.to_hash(at)
			.map_err(|e| Error::RuntimeApi(format!("{:?}", e)))?
			.ok_or_else(|| Error::RuntimeApi(format!("Could not get hash for block `{:?}`.", at)))?;

		use sp_api::Core;

		sp_tracing::within_span!(
			sp_tracing::Level::TRACE, "runtime::validate_transaction";
		{
			if api_version >= 3 {
				runtime_api.validate_transaction(&at, source, uxt, block_hash)
					.map_err(|e| Error::RuntimeApi(e.to_string()))
			} else {
				let block_number = client.to_number(at)
					.map_err(|e| Error::RuntimeApi(format!("{:?}", e)))?
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
					runtime_api.validate_transaction_before_version_3(&at, source, uxt)
						.map_err(|e| Error::RuntimeApi(e.to_string()))
				} else {
					#[allow(deprecated)] // old validate_transaction
					runtime_api.validate_transaction_before_version_2(&at, uxt)
						.map_err(|e| Error::RuntimeApi(e.to_string()))
				}
			}
		})
	})
}

impl<Client, Block> FullChainApi<Client, Block>
where
	Block: BlockT,
	Client: ProvideRuntimeApi<Block> + BlockBackend<Block> + BlockIdTo<Block> + HeaderBackend<Block>,
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
		uxt: sc_transaction_graph::ExtrinsicFor<Self>,
	) -> error::Result<TransactionValidity> {
		validate_transaction_blocking(&*self.client, at, source, uxt)
	}
}

/// The transaction pool logic for light client.
pub struct LightChainApi<Client, F, Block> {
	client: Arc<Client>,
	fetcher: Arc<F>,
	_phantom: PhantomData<Block>,
}

impl<Client, F, Block> LightChainApi<Client, F, Block> {
	/// Create new transaction pool logic.
	pub fn new(client: Arc<Client>, fetcher: Arc<F>) -> Self {
		LightChainApi {
			client,
			fetcher,
			_phantom: Default::default(),
		}
	}
}

impl<Client, F, Block> sc_transaction_graph::ChainApi for
	LightChainApi<Client, F, Block> where
		Block: BlockT,
		Client: HeaderBackend<Block> + 'static,
		F: Fetcher<Block> + 'static,
{
	type Block = Block;
	type Error = error::Error;
	type ValidationFuture = Box<
		dyn Future<Output = error::Result<TransactionValidity>> + Send + Unpin
	>;
	type BodyFuture = Pin<
		Box<
			dyn Future<Output = error::Result<Option<Vec<<Self::Block as BlockT>::Extrinsic>>>>
				+ Send
		>
	>;

	fn validate_transaction(
		&self,
		at: &BlockId<Self::Block>,
		source: TransactionSource,
		uxt: sc_transaction_graph::ExtrinsicFor<Self>,
	) -> Self::ValidationFuture {
		let header_hash = self.client.expect_block_hash_from_id(at);
		let header_and_hash = header_hash
			.and_then(|header_hash| self.client.expect_header(BlockId::Hash(header_hash))
				.map(|header| (header_hash, header)));
		let (block, header) = match header_and_hash {
			Ok((header_hash, header)) => (header_hash, header),
			Err(err) => return Box::new(ready(Err(err.into()))),
		};
		let remote_validation_request = self.fetcher.remote_call(RemoteCallRequest {
			block,
			header,
			method: "TaggedTransactionQueue_validate_transaction".into(),
			call_data: (source, uxt).encode(),
			retry_count: None,
		});
		let remote_validation_request = remote_validation_request.then(move |result| {
			let result: error::Result<TransactionValidity> = result
				.map_err(Into::into)
				.and_then(|result| Decode::decode(&mut &result[..])
					.map_err(|e| Error::RuntimeApi(
						format!("Error decoding tx validation result: {:?}", e)
					))
				);
			ready(result)
		});

		Box::new(remote_validation_request)
	}

	fn block_id_to_number(
		&self,
		at: &BlockId<Self::Block>,
	) -> error::Result<Option<sc_transaction_graph::NumberFor<Self>>> {
		Ok(self.client.block_number_from_id(at)?)
	}

	fn block_id_to_hash(
		&self,
		at: &BlockId<Self::Block>,
	) -> error::Result<Option<sc_transaction_graph::BlockHash<Self>>> {
		Ok(self.client.block_hash_from_id(at)?)
	}

	fn hash_and_length(
		&self,
		ex: &sc_transaction_graph::ExtrinsicFor<Self>,
	) -> (sc_transaction_graph::ExtrinsicHash<Self>, usize) {
		ex.using_encoded(|x| {
			(<<Block::Header as HeaderT>::Hashing as HashT>::hash(x), x.len())
		})
	}

	fn block_body(&self, id: &BlockId<Self::Block>) -> Self::BodyFuture {
		let header = self.client.header(*id)
			.and_then(|h| h.ok_or_else(|| sp_blockchain::Error::UnknownBlock(format!("{}", id))));
		let header = match header {
			Ok(header) => header,
			Err(err) => {
				log::warn!(target: "txpool", "Failed to query header: {:?}", err);
				return Box::pin(ready(Ok(None)));
			}
		};

		let fetcher = self.fetcher.clone();
		async move {
			let transactions = fetcher.remote_body({
					RemoteBodyRequest {
						header,
						retry_count: None,
					}
				})
				.await
				.unwrap_or_else(|e| {
					log::warn!(target: "txpool", "Failed to fetch block body: {:?}", e);
					Vec::new()
				});

			Ok(Some(transactions))
		}.boxed()
	}

	fn block_header(
		&self,
		at: &BlockId<Self::Block>,
	) -> Result<Option<<Self::Block as BlockT>::Header>, Self::Error> {
		self.client.header(*at).map_err(Into::into)
	}
}
