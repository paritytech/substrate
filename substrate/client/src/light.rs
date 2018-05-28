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

use std::sync::Arc;
use futures::future::IntoFuture;
use primitives;
use primitives::block::{self, Id as BlockId, HeaderHash};
use runtime_support::Hashable;
use state_machine::{CodeExecutor, Backend as StateBackend, TrieBackend as StateTrieBackend,
	TryIntoTrieBackend as TryIntoStateTrieBackend};
use blockchain::{self, BlockStatus};
use backend;
use call_executor::{CallResult, RemoteCallExecutor, check_execution_proof};
use client::{Client, GenesisBuilder};
use error;
use in_mem::Blockchain as InMemBlockchain;

/// Remote call request.
pub struct RemoteCallRequest {
	/// Call at state of given block.
	pub block: HeaderHash,
	/// Method to call.
	pub method: String,
	/// Call data.
	pub call_data: Vec<u8>,
}

/// Light client data fetcher. Implementations of this trait must check if remote data
/// is correct (see FetchedDataChecker) and return already checked data.
pub trait Fetcher: Send + Sync {
	/// Remote call result future.
	type RemoteCallResult: IntoFuture<Item=CallResult, Error=error::Error>;

	/// Fetch remote call result.
	fn remote_call(&self, request: RemoteCallRequest) -> Self::RemoteCallResult;
}

/// Light client remote data checker.
pub trait FetchChecker: Send + Sync {
	/// Check remote method execution proof.
	fn check_execution_proof(&self, request: &RemoteCallRequest, remote_proof: (Vec<u8>, Vec<Vec<u8>>)) -> error::Result<CallResult>;
}

/// Light client backend.
pub struct Backend {
	blockchain: Blockchain,
}

/// Light client blockchain.
pub struct Blockchain {
	storage: InMemBlockchain,
}

/// Block (header and justification) import operation.
pub struct BlockImportOperation {
	pending_block: Option<PendingBlock>,
}

/// On-demand state.
#[derive(Clone)]
pub struct OnDemandState {
	/// Hash of the block, state is valid for.
	_block: HeaderHash,
}

/// Remote data checker.
pub struct LightDataChecker<E> {
	/// Backend reference.
	backend: Arc<Backend>,
	/// Executor.
	executor: E,
}

struct PendingBlock {
	header: block::Header,
	justification: Option<primitives::bft::Justification>,
	is_best: bool,
}

impl backend::Backend for Backend {
	type BlockImportOperation = BlockImportOperation;
	type Blockchain = Blockchain;
	type State = OnDemandState;

	fn begin_operation(&self, _block: BlockId) -> error::Result<Self::BlockImportOperation> {
		Ok(BlockImportOperation {
			pending_block: None,
		})
	}

	fn commit_operation(&self, operation: Self::BlockImportOperation) -> error::Result<()> {
		if let Some(pending_block) = operation.pending_block {
			let hash = pending_block.header.blake2_256().into();
			self.blockchain.storage.insert(hash, pending_block.header, pending_block.justification, None, pending_block.is_best);
		}
		Ok(())
	}

	fn blockchain(&self) -> &Blockchain {
		&self.blockchain
	}

	fn state_at(&self, block: BlockId) -> error::Result<Self::State> {
		Ok(OnDemandState {
			_block: self.blockchain.storage.id(block).ok_or(error::ErrorKind::UnknownBlock(block))?,
		})
	}
}

impl backend::RemoteBackend for Backend {}

impl backend::BlockImportOperation for BlockImportOperation {
	type State = OnDemandState;

	fn state(&self) -> error::Result<Option<&Self::State>> {
		// None means 'locally-stateless' backend
		Ok(None)
	}

	fn set_block_data(&mut self, header: block::Header, _body: Option<block::Body>, justification: Option<primitives::bft::Justification>, is_new_best: bool) -> error::Result<()> {
		assert!(self.pending_block.is_none(), "Only one block per operation is allowed");
		self.pending_block = Some(PendingBlock {
			header,
			justification,
			is_best: is_new_best,
		});
		Ok(())
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

impl blockchain::Backend for Blockchain {
	fn header(&self, id: BlockId) -> error::Result<Option<block::Header>> {
		self.storage.header(id)
	}

	fn body(&self, _id: BlockId) -> error::Result<Option<block::Body>> {
		// TODO [light]: fetch from remote node
		Ok(None)
	}

	fn justification(&self, id: BlockId) -> error::Result<Option<primitives::bft::Justification>> {
		self.storage.justification(id)
	}

	fn info(&self) -> error::Result<blockchain::Info> {
		self.storage.info()
	}

	fn status(&self, id: BlockId) -> error::Result<BlockStatus> {
		self.storage.status(id)
	}

	fn hash(&self, number: block::Number) -> error::Result<Option<block::HeaderHash>> {
		self.storage.hash(number)
	}
}

impl StateBackend for OnDemandState {
	type Error = error::Error;
	type Transaction = ();

	fn storage(&self, _key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		// TODO [light]: fetch from remote node
		Err(error::ErrorKind::NotAvailableOnLightClient.into())
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

impl TryIntoStateTrieBackend for OnDemandState {
	fn try_into_trie_backend(self) -> Option<StateTrieBackend> {
		None
	}
}

impl<E> FetchChecker for LightDataChecker<E>
	where
		E: CodeExecutor,
{
	fn check_execution_proof(&self, request: &RemoteCallRequest, remote_proof: (Vec<u8>, Vec<Vec<u8>>)) -> error::Result<CallResult> {
		check_execution_proof(&*self.backend, &self.executor, request, remote_proof)
	}
}

/// Create an instance of light client backend.
pub fn new_light_backend() -> Arc<Backend> {
	let storage = InMemBlockchain::new();
	let blockchain = Blockchain { storage };
	Arc::new(Backend { blockchain })
}

/// Create an instance of light client.
pub fn new_light<F, B>(
	backend: Arc<Backend>,
	fetcher: Arc<F>,
	genesis_builder: B,
) -> error::Result<Client<Backend, RemoteCallExecutor<Backend, F>>>
	where
		F: Fetcher,
		B: GenesisBuilder,
{
	let executor = RemoteCallExecutor::new(backend.clone(), fetcher);
	Client::new(backend, executor, genesis_builder)
}

/// Create an instance of fetch data checker.
pub fn new_fetch_checker<E>(
	backend: Arc<Backend>,
	executor: E,
) -> LightDataChecker<E>
	where
		E: CodeExecutor,
{
	LightDataChecker { backend, executor }
}
