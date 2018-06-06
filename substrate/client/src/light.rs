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
use state_machine::CodeExecutor;
use state_machine::backend::Backend as StateBackend;
use runtime_primitives::generic::BlockId;
use runtime_primitives::bft::Justification;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT};
use blockchain::{self, BlockStatus};
use backend;
use call_executor::{CallResult, RemoteCallExecutor, check_execution_proof};
use client::{Client, GenesisBuilder};
use error;
use in_mem::Blockchain as InMemBlockchain;

/// Remote call request.
pub struct RemoteCallRequest<H> {
	/// Call at state of block referenced by given header hash.
	pub block: H,
	/// Method to call.
	pub method: String,
	/// Call data.
	pub call_data: Vec<u8>,
}

/// Light client data fetcher. Implementations of this trait must check if remote data
/// is correct (see FetchedDataChecker) and return already checked data.
pub trait Fetcher<B: BlockT>: Send + Sync {
	/// Remote call result future.
	type RemoteCallResult: IntoFuture<Item=CallResult, Error=error::Error>;

	/// Fetch remote call result.
	fn remote_call(&self, request: RemoteCallRequest<B::Hash>) -> Self::RemoteCallResult;
}

/// Light client remote data checker.
pub trait FetchChecker<B: BlockT>: Send + Sync {
	/// Check remote method execution proof.
	fn check_execution_proof(&self, request: &RemoteCallRequest<B::Hash>, remote_proof: (Vec<u8>, Vec<Vec<u8>>)) -> error::Result<CallResult>;
}

/// Light client backend.
pub struct Backend<B: BlockT> {
	blockchain: Blockchain<B>,
}

/// Light client blockchain.
pub struct Blockchain<B: BlockT> {
	storage: InMemBlockchain<B>,
}

/// Block (header and justification) import operation.
pub struct BlockImportOperation<B: BlockT> {
	pending_block: Option<PendingBlock<B>>,
}

/// On-demand state.
#[derive(Clone)]
pub struct OnDemandState<H> {
	/// Hash of the block, state is valid for.
	_block: H,
}

/// Remote data checker.
pub struct LightDataChecker<E, B: BlockT> {
	/// Backend reference.
	backend: Arc<Backend<B>>,
	/// Executor.
	executor: E,
}

struct PendingBlock<B: BlockT> {
	header: B::Header,
	justification: Option<Justification<B::Hash>>,
	is_best: bool,
}

impl<B: BlockT> backend::Backend<B> for Backend<B> {
	type BlockImportOperation = BlockImportOperation<B>;
	type Blockchain = Blockchain<B>;
	type State = OnDemandState<B::Hash>;

	fn begin_operation(&self, _block: BlockId<B>) -> error::Result<Self::BlockImportOperation> {
		Ok(BlockImportOperation {
			pending_block: None,
		})
	}

	fn commit_operation(&self, operation: Self::BlockImportOperation) -> error::Result<()> {
		if let Some(pending_block) = operation.pending_block {
			let hash = pending_block.header.hash();
			self.blockchain.storage.insert(hash, pending_block.header, pending_block.justification, None, pending_block.is_best);
		}
		Ok(())
	}

	fn blockchain(&self) -> &Blockchain<B> {
		&self.blockchain
	}

	fn state_at(&self, block: BlockId<B>) -> error::Result<Self::State> {
		Ok(OnDemandState {
			_block: self.blockchain.storage.id(block).ok_or(error::ErrorKind::UnknownBlock(format!("{:?}", block)))?,
		})
	}
}

impl<B: BlockT> backend::RemoteBackend<B> for Backend<B> {}

impl<B: BlockT> backend::BlockImportOperation<B> for BlockImportOperation<B> {
	type State = OnDemandState<B::Hash>;

	fn state(&self) -> error::Result<Option<&Self::State>> {
		// None means 'locally-stateless' backend
		Ok(None)
	}

	fn set_block_data(&mut self, header: B::Header, _body: Option<Vec<B::Extrinsic>>, justification: Option<Justification<B::Hash>>, is_new_best: bool) -> error::Result<()> {
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

impl<B: BlockT> blockchain::Backend<B> for Blockchain<B> {
	fn header(&self, id: BlockId<B>) -> error::Result<Option<B::Header>> {
		self.storage.header(id)
	}

	fn body(&self, _id: BlockId<B>) -> error::Result<Option<Vec<B::Extrinsic>>> {
		// TODO [light]: fetch from remote node
		Ok(None)
	}

	fn justification(&self, id: BlockId<B>) -> error::Result<Option<Justification<B::Hash>>> {
		self.storage.justification(id)
	}

	fn info(&self) -> error::Result<blockchain::Info<B>> {
		self.storage.info()
	}

	fn status(&self, id: BlockId<B>) -> error::Result<BlockStatus> {
		self.storage.status(id)
	}

	fn hash(&self, number: <B::Header as HeaderT>::Number) -> error::Result<Option<B::Hash>> {
		self.storage.hash(number)
	}
}

impl<H: Clone> StateBackend for OnDemandState<H> {
	type Error = error::Error;
	type Transaction = ();

	fn storage(&self, _key: &[u8]) -> Result<Option<Vec<u8>>, Self::Error> {
		// TODO [light]: fetch from remote node
		Err(error::ErrorKind::NotAvailableOnLightClient.into())
	}

	fn storage_root<I>(&self, _delta: I) -> ([u8; 32], Self::Transaction)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)>
	{
		([0; 32], ())
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		// whole state is not available on light node
		Vec::new()
	}
}

impl<E, B> FetchChecker<B> for LightDataChecker<E, B>
	where
		E: CodeExecutor,
		B: BlockT,
{
	fn check_execution_proof(&self, request: &RemoteCallRequest<B::Hash>, remote_proof: (Vec<u8>, Vec<Vec<u8>>)) -> error::Result<CallResult> {
		check_execution_proof(&*self.backend, &self.executor, request, remote_proof)
	}
}

/// Create an instance of light client backend.
pub fn new_light_backend<B: BlockT>() -> Arc<Backend<B>> {
	let storage = InMemBlockchain::new();
	let blockchain = Blockchain { storage };
	Arc::new(Backend { blockchain })
}

/// Create an instance of light client.
pub fn new_light<F, B, Block>(
	backend: Arc<Backend<Block>>,
	fetcher: Arc<F>,
	genesis_builder: B,
) -> error::Result<Client<Backend<Block>, RemoteCallExecutor<Backend<Block>, F>, Block>>
	where
		F: Fetcher<Block>,
		B: GenesisBuilder<Block>,
		Block: BlockT,
{
	let executor = RemoteCallExecutor::new(backend.clone(), fetcher);
	Client::new(backend, executor, genesis_builder)
}

/// Create an instance of fetch data checker.
pub fn new_fetch_checker<E, Block>(
	backend: Arc<Backend<Block>>,
	executor: E,
) -> LightDataChecker<E, Block>
	where
		E: CodeExecutor,
		Block: BlockT,
{
	LightDataChecker { backend, executor }
}
