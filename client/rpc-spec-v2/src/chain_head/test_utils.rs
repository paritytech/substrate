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
	execution_extensions::ExecutionExtensions, Backend as BackendT, BlockBackend,
	BlockImportNotification, BlockchainEvents, CallExecutor, ChildInfo, ExecutorProvider,
	FinalityNotification, FinalityNotifications, ImportNotifications, KeysIter, PairsIter,
	StorageData, StorageEventStream, StorageKey, StorageProvider,
};
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedSender};
use sp_api::{CallApiAt, CallApiAtParams, NumberFor, RuntimeVersion};
use sp_blockchain::{
	Backend as BackendBlockchain, BlockStatus, CachedHeaderMetadata, HeaderBackend, HeaderMetadata,
	Info,
};
use sp_runtime::{
	generic::SignedBlock,
	traits::{Block as BlockT, Header as HeaderT},
	Justifications,
};
use std::sync::Arc;
use substrate_test_runtime::{Block, Hash};

pub struct ChainHeadMockClient<BE, Client> {
	client: Arc<Client>,
	backend: Arc<BE>,
	import_sink: Mutex<Vec<TracingUnboundedSender<BlockImportNotification<Block>>>>,
	finality_sinks: Mutex<Vec<TracingUnboundedSender<FinalityNotification<Block>>>>,
}

impl<BE, Client> ChainHeadMockClient<BE, Client> {
	pub fn new(client: Arc<Client>, backend: Arc<BE>) -> Self {
		ChainHeadMockClient {
			client,
			backend,
			import_sink: Default::default(),
			finality_sinks: Default::default(),
		}
	}

	pub fn fire_import_stream(&self, notification: BlockImportNotification<Block>) {
		for sink in self.import_sink.lock().iter() {
			sink.unbounded_send(notification.clone()).unwrap();
		}
	}

	pub fn fire_finality_stream(&self, notification: FinalityNotification<Block>) {
		println!("Triggered: {:?}", notification);
		for sink in self.finality_sinks.lock().iter() {
			sink.unbounded_send(notification.clone()).unwrap();
		}
	}
}

impl<
		BE: sc_client_api::backend::Backend<Block> + Send + Sync + 'static,
		Block: BlockT,
		E: CallExecutor<Block>,
		Client: ExecutorProvider<Block, Executor = E>,
	> ExecutorProvider<Block> for ChainHeadMockClient<BE, Client>
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
	> StorageProvider<Block, BE> for ChainHeadMockClient<BE, Client>
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

impl<BE: sc_client_api::backend::Backend<Block> + Send + Sync + 'static, Block: BlockT, Client>
	CallApiAt<Block> for ChainHeadMockClient<BE, Client>
{
	type StateBackend = sc_client_api::backend::StateBackendFor<BE, Block>;

	fn call_api_at(
		&self,
		_params: CallApiAtParams<Block, sc_client_api::backend::StateBackendFor<BE, Block>>,
	) -> Result<Vec<u8>, sp_api::ApiError> {
		unimplemented!()
	}

	fn runtime_version_at(&self, _hash: Block::Hash) -> Result<RuntimeVersion, sp_api::ApiError> {
		unimplemented!()
	}

	fn state_at(&self, _at: Block::Hash) -> Result<Self::StateBackend, sp_api::ApiError> {
		unimplemented!()
	}
}

impl<BE, Block: BlockT, Client: BlockBackend<Block>> BlockBackend<Block>
	for ChainHeadMockClient<BE, Client>
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

impl<BE, Client> BlockchainEvents<Block> for ChainHeadMockClient<BE, Client> {
	fn import_notification_stream(&self) -> ImportNotifications<Block> {
		let (sink, stream) = tracing_unbounded("mpsc_import_notification_stream", 100_000);
		self.import_sink.lock().push(sink);
		stream
	}

	fn every_import_notification_stream(&self) -> ImportNotifications<Block> {
		unimplemented!()
	}

	fn finality_notification_stream(&self) -> FinalityNotifications<Block> {
		let (sink, stream) = tracing_unbounded("mpsc_finality_notification_stream", 100_000);
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

impl<BE: Send + Sync, Block: BlockT, Client: HeaderMetadata<Block> + Send + Sync>
	HeaderMetadata<Block> for ChainHeadMockClient<BE, Client>
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
		_hash: Block::Hash,
		_header_metadata: CachedHeaderMetadata<Block>,
	) {
		todo!()
	}

	fn remove_header_metadata(&self, _hash: Block::Hash) {
		todo!()
	}
}

impl<BE: Send + Sync, Block: BlockT, Client: HeaderBackend<Block> + Send + Sync>
	HeaderBackend<Block> for ChainHeadMockClient<BE, Client>
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
