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

use parking_lot::Mutex;
use sc_client_api::{
	execution_extensions::ExecutionExtensions, BlockBackend, BlockImportNotification,
	BlockchainEvents, CallExecutor, ChildInfo, ExecutorProvider, FinalityNotification,
	FinalityNotifications, FinalizeSummary, ImportNotifications, KeysIter, PairsIter, StorageData,
	StorageEventStream, StorageKey, StorageProvider,
};
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedSender};
use sp_api::{CallApiAt, CallApiAtParams, NumberFor, RuntimeVersion};
use sp_blockchain::{BlockStatus, CachedHeaderMetadata, HeaderBackend, HeaderMetadata, Info};
use sp_consensus::BlockOrigin;
use sp_runtime::{
	generic::SignedBlock,
	traits::{Block as BlockT, Header as HeaderT},
	Justifications,
};
use std::sync::Arc;
use substrate_test_runtime::{Block, Hash, Header};

pub struct ChainHeadMockClient<Client> {
	client: Arc<Client>,
	import_sinks: Mutex<Vec<TracingUnboundedSender<BlockImportNotification<Block>>>>,
	finality_sinks: Mutex<Vec<TracingUnboundedSender<FinalityNotification<Block>>>>,
}

impl<Client> ChainHeadMockClient<Client> {
	pub fn new(client: Arc<Client>) -> Self {
		ChainHeadMockClient {
			client,
			import_sinks: Default::default(),
			finality_sinks: Default::default(),
		}
	}

	pub async fn trigger_import_stream(&self, header: Header) {
		// Ensure the client called the `import_notification_stream`.
		while self.import_sinks.lock().is_empty() {
			tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
		}

		// Build the notification.
		let (sink, _stream) = tracing_unbounded("test_sink", 100_000);
		let notification =
			BlockImportNotification::new(header.hash(), BlockOrigin::Own, header, true, None, sink);

		for sink in self.import_sinks.lock().iter_mut() {
			sink.unbounded_send(notification.clone()).unwrap();
		}
	}

	pub async fn trigger_finality_stream(&self, header: Header) {
		// Ensure the client called the `finality_notification_stream`.
		while self.finality_sinks.lock().is_empty() {
			tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
		}

		// Build the notification.
		let (sink, _stream) = tracing_unbounded("test_sink", 100_000);
		let summary = FinalizeSummary {
			header: header.clone(),
			finalized: vec![header.hash()],
			stale_heads: vec![],
		};
		let notification = FinalityNotification::from_summary(summary, sink);

		for sink in self.finality_sinks.lock().iter_mut() {
			sink.unbounded_send(notification.clone()).unwrap();
		}
	}
}

// ChainHead calls `import_notification_stream` and `finality_notification_stream` in order to
// subscribe to block events.
impl<Client> BlockchainEvents<Block> for ChainHeadMockClient<Client> {
	fn import_notification_stream(&self) -> ImportNotifications<Block> {
		let (sink, stream) = tracing_unbounded("import_notification_stream", 1024);
		self.import_sinks.lock().push(sink);
		stream
	}

	fn every_import_notification_stream(&self) -> ImportNotifications<Block> {
		unimplemented!()
	}

	fn finality_notification_stream(&self) -> FinalityNotifications<Block> {
		let (sink, stream) = tracing_unbounded("finality_notification_stream", 1024);
		self.finality_sinks.lock().push(sink);
		stream
	}

	fn storage_changes_notification_stream(
		&self,
		_filter_keys: Option<&[StorageKey]>,
		_child_filter_keys: Option<&[(StorageKey, Option<Vec<StorageKey>>)]>,
	) -> sp_blockchain::Result<StorageEventStream<Hash>> {
		unimplemented!()
	}
}

// The following implementations are imposed by the `chainHead` trait bounds.

impl<Block: BlockT, E: CallExecutor<Block>, Client: ExecutorProvider<Block, Executor = E>>
	ExecutorProvider<Block> for ChainHeadMockClient<Client>
{
	type Executor = <Client as ExecutorProvider<Block>>::Executor;

	fn executor(&self) -> &Self::Executor {
		self.client.executor()
	}

	fn execution_extensions(&self) -> &ExecutionExtensions<Block> {
		self.client.execution_extensions()
	}
}

impl<
		BE: sc_client_api::backend::Backend<Block> + Send + Sync + 'static,
		Block: BlockT,
		Client: StorageProvider<Block, BE>,
	> StorageProvider<Block, BE> for ChainHeadMockClient<Client>
{
	fn storage(
		&self,
		hash: Block::Hash,
		key: &StorageKey,
	) -> sp_blockchain::Result<Option<StorageData>> {
		self.client.storage(hash, key)
	}

	fn storage_hash(
		&self,
		hash: Block::Hash,
		key: &StorageKey,
	) -> sp_blockchain::Result<Option<Block::Hash>> {
		self.client.storage_hash(hash, key)
	}

	fn storage_keys(
		&self,
		hash: Block::Hash,
		prefix: Option<&StorageKey>,
		start_key: Option<&StorageKey>,
	) -> sp_blockchain::Result<KeysIter<BE::State, Block>> {
		self.client.storage_keys(hash, prefix, start_key)
	}

	fn storage_pairs(
		&self,
		hash: <Block as BlockT>::Hash,
		prefix: Option<&StorageKey>,
		start_key: Option<&StorageKey>,
	) -> sp_blockchain::Result<PairsIter<BE::State, Block>> {
		self.client.storage_pairs(hash, prefix, start_key)
	}

	fn child_storage(
		&self,
		hash: Block::Hash,
		child_info: &ChildInfo,
		key: &StorageKey,
	) -> sp_blockchain::Result<Option<StorageData>> {
		self.client.child_storage(hash, child_info, key)
	}

	fn child_storage_keys(
		&self,
		hash: Block::Hash,
		child_info: ChildInfo,
		prefix: Option<&StorageKey>,
		start_key: Option<&StorageKey>,
	) -> sp_blockchain::Result<KeysIter<BE::State, Block>> {
		self.client.child_storage_keys(hash, child_info, prefix, start_key)
	}

	fn child_storage_hash(
		&self,
		hash: Block::Hash,
		child_info: &ChildInfo,
		key: &StorageKey,
	) -> sp_blockchain::Result<Option<Block::Hash>> {
		self.client.child_storage_hash(hash, child_info, key)
	}
}

impl<Block: BlockT, Client: CallApiAt<Block>> CallApiAt<Block> for ChainHeadMockClient<Client> {
	type StateBackend = <Client as CallApiAt<Block>>::StateBackend;

	fn call_api_at(
		&self,
		params: CallApiAtParams<Block, <Client as CallApiAt<Block>>::StateBackend>,
	) -> Result<Vec<u8>, sp_api::ApiError> {
		self.client.call_api_at(params)
	}

	fn runtime_version_at(&self, hash: Block::Hash) -> Result<RuntimeVersion, sp_api::ApiError> {
		self.client.runtime_version_at(hash)
	}

	fn state_at(&self, at: Block::Hash) -> Result<Self::StateBackend, sp_api::ApiError> {
		self.client.state_at(at)
	}
}

impl<Block: BlockT, Client: BlockBackend<Block>> BlockBackend<Block>
	for ChainHeadMockClient<Client>
{
	fn block_body(
		&self,
		hash: Block::Hash,
	) -> sp_blockchain::Result<Option<Vec<<Block as BlockT>::Extrinsic>>> {
		self.client.block_body(hash)
	}

	fn block(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<SignedBlock<Block>>> {
		self.client.block(hash)
	}

	fn block_status(&self, hash: Block::Hash) -> sp_blockchain::Result<sp_consensus::BlockStatus> {
		self.client.block_status(hash)
	}

	fn justifications(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<Justifications>> {
		self.client.justifications(hash)
	}

	fn block_hash(&self, number: NumberFor<Block>) -> sp_blockchain::Result<Option<Block::Hash>> {
		self.client.block_hash(number)
	}

	fn indexed_transaction(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<Vec<u8>>> {
		self.client.indexed_transaction(hash)
	}

	fn has_indexed_transaction(&self, hash: Block::Hash) -> sp_blockchain::Result<bool> {
		self.client.has_indexed_transaction(hash)
	}

	fn block_indexed_body(&self, hash: Block::Hash) -> sp_blockchain::Result<Option<Vec<Vec<u8>>>> {
		self.client.block_indexed_body(hash)
	}
	fn requires_full_sync(&self) -> bool {
		self.client.requires_full_sync()
	}
}

impl<Block: BlockT, Client: HeaderMetadata<Block> + Send + Sync> HeaderMetadata<Block>
	for ChainHeadMockClient<Client>
{
	type Error = <Client as HeaderMetadata<Block>>::Error;

	fn header_metadata(
		&self,
		hash: Block::Hash,
	) -> Result<CachedHeaderMetadata<Block>, Self::Error> {
		self.client.header_metadata(hash)
	}

	fn insert_header_metadata(
		&self,
		hash: Block::Hash,
		header_metadata: CachedHeaderMetadata<Block>,
	) {
		self.client.insert_header_metadata(hash, header_metadata)
	}

	fn remove_header_metadata(&self, hash: Block::Hash) {
		self.client.remove_header_metadata(hash)
	}
}

impl<Block: BlockT, Client: HeaderBackend<Block> + Send + Sync> HeaderBackend<Block>
	for ChainHeadMockClient<Client>
{
	fn header(
		&self,
		hash: Block::Hash,
	) -> sp_blockchain::Result<Option<<Block as BlockT>::Header>> {
		self.client.header(hash)
	}

	fn info(&self) -> Info<Block> {
		self.client.info()
	}

	fn status(&self, hash: Block::Hash) -> sc_client_api::blockchain::Result<BlockStatus> {
		self.client.status(hash)
	}

	fn number(
		&self,
		hash: Block::Hash,
	) -> sc_client_api::blockchain::Result<Option<<<Block as BlockT>::Header as HeaderT>::Number>> {
		self.client.number(hash)
	}

	fn hash(
		&self,
		number: <<Block as BlockT>::Header as HeaderT>::Number,
	) -> sp_blockchain::Result<Option<Block::Hash>> {
		self.client.hash(number)
	}
}
