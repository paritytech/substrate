// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! State API backend for light nodes.

use std::sync::Arc;
use codec::Decode;
use futures03::{future::{ready, Either}, FutureExt, TryFutureExt};
use hash_db::Hasher;
use jsonrpc_pubsub::{typed::Subscriber, SubscriptionId};
use rpc::{
	Result as RpcResult,
	futures::future::{result, Future},
};

use api::Subscriptions;
use client::{
	Client, CallExecutor, backend::Backend,
	error::Error as ClientError,
	light::{
		blockchain::{future_header, RemoteBlockchain},
		fetcher::{Fetcher, RemoteCallRequest, RemoteReadRequest, RemoteReadChildRequest},
	},
};
use primitives::{
	H256, Blake2Hasher, Bytes, OpaqueMetadata,
	storage::{StorageKey, StorageData, StorageChangeSet},
};
use runtime_version::RuntimeVersion;
use sr_primitives::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT},
};

use super::{StateBackend, error::{FutureResult, Error}, client_err};

pub struct LightState<Block: BlockT, F: Fetcher<Block>, B, E, RA> {
	client: Arc<Client<B, E, Block, RA>>,
	subscriptions: Subscriptions,
	remote_blockchain: Arc<dyn RemoteBlockchain<Block>>,
	fetcher: Arc<F>,
}

impl<Block: BlockT, F: Fetcher<Block> + 'static, B, E, RA> LightState<Block, F, B, E, RA>
	where
		Block: BlockT<Hash=H256>,
		B: Backend<Block, Blake2Hasher> + Send + Sync + 'static,
		E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static + Clone,
		RA: Send + Sync + 'static,
{
	///
	pub fn new(
		client: Arc<Client<B, E, Block, RA>>,
		subscriptions: Subscriptions,
		remote_blockchain: Arc<dyn RemoteBlockchain<Block>>,
		fetcher: Arc<F>,
	) -> Self {
		Self { client, subscriptions, remote_blockchain, fetcher, }
	}

	/// Returns given block hash or best block hash if None is passed.
	fn block_or_best(&self, hash: Option<Block::Hash>) -> Block::Hash {
		hash.unwrap_or_else(|| self.client.info().chain.best_hash)
	}

	/// Resolve header by hash.
	fn resolve_header(
		&self,
		block: Option<Block::Hash>,
	) -> impl std::future::Future<Output = Result<Block::Header, Error>> {
		let block = self.block_or_best(block);
		let maybe_header = future_header(
			&*self.remote_blockchain,
			&*self.fetcher,
			BlockId::Hash(block),
		);

		maybe_header.then(move |result|
			ready(result.and_then(|maybe_header|
				maybe_header.ok_or(ClientError::UnknownBlock(format!("{}", block)))
			).map_err(client_err)),
		)
	}
}

impl<Block, F, B, E, RA> StateBackend<B, E, Block, RA> for LightState<Block, F, B, E, RA>
	where
		Block: BlockT<Hash=H256>,
		B: Backend<Block, Blake2Hasher> + Send + Sync + 'static,
		E: CallExecutor<Block, Blake2Hasher> + Send + Sync + 'static + Clone,
		RA: Send + Sync + 'static,
		F: Fetcher<Block> + 'static
{
	fn client(&self) -> &Arc<Client<B, E, Block, RA>> {
		&self.client
	}

	fn subscriptions(&self) -> &Subscriptions {
		&self.subscriptions
	}

	fn call(
		&self,
		block: Option<Block::Hash>,
		method: String,
		call_data: Bytes,
	) -> FutureResult<Bytes> {
		let fetcher = self.fetcher.clone();
		let call_result = self.resolve_header(block)
			.then(move |result| match result {
				Ok(header) => Either::Left(fetcher.remote_call(RemoteCallRequest {
					block: header.hash(),
					header,
					method,
					call_data: call_data.0,
					retry_count: Default::default(),
				}).then(|result| ready(result.map(Bytes).map_err(client_err)))),
				Err(error) => Either::Right(ready(Err(error))),
			});

		Box::new(call_result.boxed().compat())
	}

	fn storage_keys(
		&self,
		_block: Option<Block::Hash>,
		_prefix: StorageKey,
	) -> FutureResult<Vec<StorageKey>> {
		Box::new(result(Err(client_err(ClientError::NotAvailableOnLightClient))))
	}

	fn storage(
		&self,
		block: Option<Block::Hash>,
		key: StorageKey,
	) -> FutureResult<Option<StorageData>> {
		let fetcher = self.fetcher.clone();
		let storage = self.resolve_header(block)
			.then(move |result| match result {
				Ok(header) => Either::Left(fetcher.remote_read(RemoteReadRequest {
					block: header.hash(),
					header,
					keys: vec![key.0.clone()],
					retry_count: Default::default(),
				}).then(move |result| ready(result
					.map(|mut data| data
						.remove(&key.0)
						.expect("successful result has entry for all keys; qed")
						.map(StorageData)
					)
					.map_err(client_err)
				))),
				Err(error) => Either::Right(ready(Err(error))),
			});

		Box::new(storage.boxed().compat())
	}

	fn storage_hash(
		&self,
		block: Option<Block::Hash>,
		key: StorageKey,
	) -> FutureResult<Option<Block::Hash>> {
		Box::new(self
			.storage(block, key)
			.and_then(|maybe_storage|
				result(Ok(maybe_storage.map(|storage| Blake2Hasher::hash(&storage.0))))
			)
		)
	}

	fn child_storage_keys(
		&self,
		_block: Option<Block::Hash>,
		_child_storage_key: StorageKey,
		_prefix: StorageKey,
	) -> FutureResult<Vec<StorageKey>> {
		Box::new(result(Err(client_err(ClientError::NotAvailableOnLightClient))))
	}

	fn child_storage(
		&self,
		block: Option<Block::Hash>,
		child_storage_key: StorageKey,
		key: StorageKey,
	) -> FutureResult<Option<StorageData>> {
		let fetcher = self.fetcher.clone();
		let child_storage = self.resolve_header(block)
			.then(move |result| match result {
				Ok(header) => Either::Left(fetcher.remote_read_child(RemoteReadChildRequest {
					block: header.hash(),
					header,
					storage_key: child_storage_key.0,
					keys: vec![key.0.clone()],
					retry_count: Default::default(),
				}).then(move |result| ready(result
					.map(|mut data| data
						.remove(&key.0)
						.expect("successful result has entry for all keys; qed")
						.map(StorageData)
					)
					.map_err(client_err)
				))),
				Err(error) => Either::Right(ready(Err(error))),
			});

		Box::new(child_storage.boxed().compat())
	}

	fn child_storage_hash(
		&self,
		block: Option<Block::Hash>,
		child_storage_key: StorageKey,
		key: StorageKey,
	) -> FutureResult<Option<Block::Hash>> {
		Box::new(self
			.child_storage(block, child_storage_key, key)
			.and_then(|maybe_storage|
				result(Ok(maybe_storage.map(|storage| Blake2Hasher::hash(&storage.0))))
			)
		)
	}

	fn metadata(&self, block: Option<Block::Hash>) -> FutureResult<Bytes> {
		let metadata = self.call(block, "Metadata_metadata".into(), Bytes(Vec::new()))
			.and_then(|metadata| OpaqueMetadata::decode(&mut &metadata.0[..])
				.map(Into::into)
				.map_err(|decode_err| client_err(ClientError::CallResultDecode(
					"Unable to decode metadata",
					decode_err,
				))));

		Box::new(metadata)
	}

	fn runtime_version(&self, block: Option<Block::Hash>) -> FutureResult<RuntimeVersion> {
		let version = self.call(block, "Core_version".into(), Bytes(Vec::new()))
			.and_then(|version| Decode::decode(&mut &version.0[..])
				.map_err(|_| client_err(ClientError::VersionInvalid))
			);

		Box::new(version)
	}

	fn query_storage(
		&self,
		_from: Block::Hash,
		_to: Option<Block::Hash>,
		_keys: Vec<StorageKey>,
	) -> FutureResult<Vec<StorageChangeSet<Block::Hash>>> {
		Box::new(result(Err(client_err(ClientError::NotAvailableOnLightClient))))
	}

	fn subscribe_storage(
		&self,
		_meta: crate::metadata::Metadata,
		_subscriber: Subscriber<StorageChangeSet<Block::Hash>>,
		_keys: Option<Vec<StorageKey>>
	) {
	}

	fn unsubscribe_storage(
		&self,
		_meta: Option<crate::metadata::Metadata>,
		_id: SubscriptionId,
	) -> RpcResult<bool> {
		Ok(false)
	}

	fn subscribe_runtime_version(
		&self,
		_meta: crate::metadata::Metadata,
		_subscriber: Subscriber<RuntimeVersion>,
	) {
	}

	fn unsubscribe_runtime_version(
		&self,
		_meta: Option<crate::metadata::Metadata>,
		_id: SubscriptionId,
	) -> RpcResult<bool> {
		Ok(false)
	}
}
