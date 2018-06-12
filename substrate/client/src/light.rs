// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Light client backend. Only stores headers and justifications of blocks.
//! Everything else is requested from full nodes on demand.

use std::sync::{Arc, Weak};
use futures::Future;
use futures::future::IntoFuture;
use heapsize::HeapSizeOf;
use parking_lot::Mutex;
use primitives::{self, AuthorityId};
use primitives::block::{self, Id as BlockId, HeaderHash};
use state_machine::{self, CodeExecutor, Backend as StateBackend,
	TrieBackend as StateTrieBackend, TryIntoTrieBackend as TryIntoStateTrieBackend};
use blockchain::{self, BlockStatus, Backend as BlockchainBackend, Cache as BlockchainCache};
use backend;
use call_executor::{CallResult, RemoteCallExecutor, check_execution_proof};
use client::{Client, GenesisBuilder};
use error;

/// Remote storage read request.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct RemoteReadRequest {
	/// Read at state of given block.
	pub block: HeaderHash,
	/// Storage key to read.
	pub key: Vec<u8>,
	/// Request retry count before failing. If None, default value is used.
	pub retry_count: Option<usize>,
}

/// Remote call request.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct RemoteCallRequest {
	/// Call at state of given block.
	pub block: HeaderHash,
	/// Method to call.
	pub method: String,
	/// Call data.
	pub call_data: Vec<u8>,
	/// Request retry count before failing. If None, default value is used.
	pub retry_count: Option<usize>,
}

/// Light client data fetcher. Implementations of this trait must check if remote data
/// is correct (see FetchedDataChecker) and return already checked data.
pub trait Fetcher: Send + Sync {
	/// Remote storage read future.
	type RemoteReadResult: IntoFuture<Item=Option<Vec<u8>>, Error=error::Error>;
	/// Remote call result future.
	type RemoteCallResult: IntoFuture<Item=CallResult, Error=error::Error>;

	/// Fetch remote storage value.
	fn remote_read(&self, request: RemoteReadRequest) -> Self::RemoteReadResult;
	/// Fetch remote call result.
	fn remote_call(&self, request: RemoteCallRequest) -> Self::RemoteCallResult;
}

/// Light client remote data checker.
pub trait FetchChecker: Send + Sync {
	/// Check remote storage read proof.
	fn check_read_proof(&self, request: &RemoteReadRequest, remote_proot: Vec<Vec<u8>>) -> error::Result<Option<Vec<u8>>>;
	/// Check remote method execution proof.
	fn check_execution_proof(&self, request: &RemoteCallRequest, remote_proof: (Vec<u8>, Vec<Vec<u8>>)) -> error::Result<CallResult>;
}

/// Light client backend.
pub struct Backend<B, F> {
	blockchain: Arc<Blockchain<B, F>>,
}

/// Light client blockchain.
pub struct Blockchain<B, F> {
	fetcher: Mutex<Weak<F>>,
	storage: B,
}

/// Block (header and justification) import operation.
pub struct BlockImportOperation<O, F> {
	operation: O,
	_phantom: ::std::marker::PhantomData<F>,
}

/// On-demand state.
pub struct OnDemandState<F> {
	fetcher: Weak<F>,
	block: HeaderHash,
}

/// Remote data checker.
pub struct LightDataChecker<B, E, F> {
	blockchain: Arc<Blockchain<B, F>>,
	executor: E,
}

impl<B, F> Backend<B, F> where B: backend::Backend {
	fn id(&self, id: BlockId) -> Option<HeaderHash> {
		match id {
			BlockId::Hash(h) => Some(h),
			BlockId::Number(n) => self.blockchain.storage.blockchain().hash(n).unwrap_or_default(),
		}
	}
}

impl<B, F> backend::Backend for Backend<B, F> where B: backend::Backend, F: Fetcher {
	type BlockImportOperation = BlockImportOperation<<B as backend::Backend>::BlockImportOperation, F>;
	type Blockchain = Blockchain<B, F>;
	type State = OnDemandState<F>;

	fn begin_operation(&self, block: BlockId) -> error::Result<Self::BlockImportOperation> {
		Ok(BlockImportOperation {
			operation: self.blockchain.storage.begin_operation(block)?,
			_phantom: Default::default(),
		})
	}

	fn commit_operation(&self, operation: Self::BlockImportOperation) -> error::Result<()> {
		self.blockchain.storage.commit_operation(operation.operation)
	}

	fn blockchain(&self) -> &Blockchain<B, F> {
		&self.blockchain
	}

	fn state_at(&self, block: BlockId) -> error::Result<Self::State> {
		Ok(OnDemandState {
			block: self.id(block).ok_or(error::ErrorKind::UnknownBlock(block))?,
			fetcher: self.blockchain.fetcher.lock().clone(),
		})
	}
}

impl<B, F> backend::RemoteBackend for Backend<B, F> where B: backend::Backend, F: Fetcher {}

impl<O, F> backend::BlockImportOperation for BlockImportOperation<O, F> where O: backend::BlockImportOperation, F: Fetcher {
	type State = OnDemandState<F>;

	fn state(&self) -> error::Result<Option<&Self::State>> {
		// None means 'locally-stateless' backend
		Ok(None)
	}

	fn set_block_data(&mut self, header: block::Header, _body: Option<block::Body>, justification: Option<primitives::bft::Justification>, is_new_best: bool) -> error::Result<()> {
		self.operation.set_block_data(header, None, justification, is_new_best)
	}

	fn update_authorities(&mut self, authorities: Vec<AuthorityId>) {
		self.operation.update_authorities(authorities);
	}

	fn update_storage(&mut self, _update: <Self::State as StateBackend>::Transaction) -> error::Result<()> {
		// we're not storing anything locally => ignore changes
		Ok(())
	}

	fn reset_storage<I: Iterator<Item=(Vec<u8>, Vec<u8>)>>(&mut self, _iter: I) -> error::Result<()> {
		// we're not storing anything locally => ignore changes
		Ok(())
	}
}

impl<B, F> blockchain::Backend for Blockchain<B, F> where B: backend::Backend, F: Fetcher {
	fn header(&self, id: BlockId) -> error::Result<Option<block::Header>> {
		self.storage.blockchain().header(id)
	}

	fn body(&self, _id: BlockId) -> error::Result<Option<block::Body>> {
		// TODO [light]: fetch from remote node
		Ok(None)
	}

	fn justification(&self, id: BlockId) -> error::Result<Option<primitives::bft::Justification>> {
		self.storage.blockchain().justification(id)
	}

	fn info(&self) -> error::Result<blockchain::Info> {
		self.storage.blockchain().info()
	}

	fn status(&self, id: BlockId) -> error::Result<BlockStatus> {
		self.storage.blockchain().status(id)
	}

	fn hash(&self, number: block::Number) -> error::Result<Option<block::HeaderHash>> {
		self.storage.blockchain().hash(number)
	}

	fn cache(&self) -> Option<&BlockchainCache> {
		self.storage.blockchain().cache()
	}
}

impl<F> Clone for OnDemandState<F> {
	fn clone(&self) -> Self {
		OnDemandState {
			fetcher: self.fetcher.clone(),
			block: self.block,
		}
	}
}

impl<F> StateBackend for OnDemandState<F> where F: Fetcher {
	type Error = error::Error;
	type Transaction = ();

	fn storage(&self, key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		self.fetcher.upgrade().ok_or(error::ErrorKind::NotAvailableOnLightClient)?
			.remote_read(RemoteReadRequest {
				block: self.block,
				key: key.to_vec(),
				..Default::default()
			})
			.into_future().wait()
	}

	fn storage_root<I>(&self, _delta: I) -> ([u8; 32], Self::Transaction)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)> {
		([0; 32], ())
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		// whole state is not available on light node
		Vec::new()
	}
}

impl<F> TryIntoStateTrieBackend for OnDemandState<F> where F: Fetcher {
	fn try_into_trie_backend(self) -> Option<StateTrieBackend> {
		None
	}
}

impl<B, E, F> LightDataChecker<B, E, F> {
	/// Get blockchain reference.
	pub fn blockchain(&self) -> &Arc<Blockchain<B, F>> {
		&self.blockchain
	}
}

impl<B, E, F> FetchChecker for LightDataChecker<B, E, F>
	where
		B: backend::Backend,
		E: CodeExecutor,
		F: Fetcher,
{
	fn check_read_proof(&self, request: &RemoteReadRequest, remote_proof: Vec<Vec<u8>>) -> error::Result<Option<Vec<u8>>> {
		let local_header = self.blockchain.header(BlockId::Hash(request.block))?;
		let local_header = local_header.ok_or_else(|| error::ErrorKind::UnknownBlock(BlockId::Hash(request.block)))?;
		let local_state_root = local_header.state_root;
		state_machine::read_proof_check(local_state_root.0, remote_proof, &request.key).map_err(Into::into)
	}

	fn check_execution_proof(&self, request: &RemoteCallRequest, remote_proof: (Vec<u8>, Vec<Vec<u8>>)) -> error::Result<CallResult> {
		check_execution_proof(&*self.blockchain, &self.executor, request, remote_proof)
	}
}

/// Create an instance of light client blockchain backend.
pub fn new_light_blockchain<B: backend::Backend, F>(storage: B) -> Arc<Blockchain<B, F>> {
	Arc::new(Blockchain { storage, fetcher: Default::default() })
}

/// Create an instance of light client backend.
pub fn new_light_backend<B: backend::Backend, F>(blockchain: Arc<Blockchain<B, F>>, fetcher: Arc<F>) -> Arc<Backend<B, F>> {
	*blockchain.fetcher.lock() = Arc::downgrade(&fetcher);
	Arc::new(Backend { blockchain })
}

/// Create an instance of light client.
pub fn new_light<B, F, GB>(
	backend: Arc<Backend<B, F>>,
	fetcher: Arc<F>,
	genesis_builder: GB,
) -> error::Result<Client<Backend<B, F>, RemoteCallExecutor<Blockchain<B, F>, F>>>
	where
		B: backend::Backend,
		F: Fetcher,
		GB: GenesisBuilder,
{
	let executor = RemoteCallExecutor::new(backend.blockchain.clone(), fetcher);
	Client::new(backend, executor, genesis_builder)
}

/// Create an instance of fetch data checker.
pub fn new_fetch_checker<B, E, F>(
	blockchain: Arc<Blockchain<B, F>>,
	executor: E,
) -> LightDataChecker<B, E, F>
	where
		B: backend::Backend,
		E: CodeExecutor,
{
	LightDataChecker { blockchain, executor }
}

impl HeapSizeOf for RemoteReadRequest {
	fn heap_size_of_children(&self) -> usize {
		self.block.heap_size_of_children() + self.key.heap_size_of_children()
	}
}

impl HeapSizeOf for RemoteCallRequest {
	fn heap_size_of_children(&self) -> usize {
		self.block.heap_size_of_children() + self.method.heap_size_of_children()
			+ self.call_data.heap_size_of_children()
	}
}

#[cfg(test)]
pub mod tests {
	use futures::future::{ok, err, FutureResult};
	use parking_lot::Mutex;
	use executor;
	use test_client;
	use backend::Backend;
	use in_mem::{Backend as InMemoryBackend};
	use super::*;

	pub type OkCallFetcher = Mutex<CallResult>;

	impl Fetcher for OkCallFetcher {
		type RemoteReadResult = FutureResult<Option<Vec<u8>>, error::Error>;
		type RemoteCallResult = FutureResult<CallResult, error::Error>;

		fn remote_read(&self, _request: RemoteReadRequest) -> Self::RemoteReadResult {
			err("Not implemented on test node".into())
		}

		fn remote_call(&self, _request: RemoteCallRequest) -> Self::RemoteCallResult {
			ok((*self.lock()).clone())
		}
	}

	#[test]
	fn storage_read_proof_is_generated_and_checked() {
		// prepare remote client
		let remote_client = test_client::new();
		let remote_block_id = BlockId::Number(0);
		let remote_block_hash = remote_client.block_hash(0).unwrap().unwrap();
		let mut remote_block_header = remote_client.header(&remote_block_id).unwrap().unwrap();
		remote_block_header.state_root = remote_client.state_at(&remote_block_id).unwrap().storage_root(::std::iter::empty()).0.into();

		// 'fetch' read proof from remote node
		let authorities_len = remote_client.authorities_at(&remote_block_id).unwrap().len();
		let remote_read_proof = remote_client.read_proof(&remote_block_id, b":auth:len").unwrap();

		// check remote read proof locally
		let local_storage = InMemoryBackend::new();
		local_storage.blockchain().insert(remote_block_hash, remote_block_header, None, None, true);
		let local_executor = test_client::NativeExecutor::new();
		let local_checker: LightDataChecker<InMemoryBackend, executor::NativeExecutor<test_client::NativeExecutor>, OkCallFetcher> =
			new_fetch_checker(new_light_blockchain(local_storage), local_executor);
		assert_eq!(local_checker.check_read_proof(&RemoteReadRequest {
			block: remote_block_hash,
			key: b":auth:len".to_vec(),
			..Default::default()
		}, remote_read_proof).unwrap().unwrap()[0], authorities_len as u8);
	}
}
