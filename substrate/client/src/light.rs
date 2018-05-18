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
use primitives;
use primitives::block::{self, Id as BlockId, HeaderHash};
use runtime_support::Hashable;
use state_machine::CodeExecutor;
use state_machine::backend::Backend as StateBackend;
use blockchain::{self, BlockStatus};
use backend;
use call_executor::RemoteCallExecutor;
use client::{Client, GenesisBuilder};
use error;
use in_mem::Blockchain as InMemBlockchain;

/// Light client data fetcher.
pub trait Fetcher: Send + Sync {
	/// Fetch method execution proof.
	fn execution_proof(&self, block: HeaderHash, method: &str, call_data: &[u8]) -> error::Result<(Vec<u8>, Vec<Vec<u8>>)>;
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

/// Create an instance of in-memory client.
pub fn new_light<E, F>(
	fetcher: Arc<Fetcher>,
	executor: E,
	genesis_builder: F
) -> error::Result<Client<Backend, RemoteCallExecutor<Backend, E>>>
	where
		E: CodeExecutor,
		F: GenesisBuilder,
{
	let storage = InMemBlockchain::new();
	let blockchain = Blockchain { storage };
	let backend = Arc::new(Backend { blockchain });
	let executor = RemoteCallExecutor::new(backend.clone(), executor, fetcher);
	Client::new(backend, executor, genesis_builder)
}
