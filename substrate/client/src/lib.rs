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

//! Polkadot Client

#![warn(missing_docs)]

extern crate substrate_primitives as primitives;
extern crate substrate_state_machine as state_machine;
extern crate substrate_serializer as ser;
extern crate substrate_codec as codec;
extern crate substrate_executor;
extern crate ed25519;

extern crate triehash;
extern crate parking_lot;
#[macro_use] extern crate error_chain;
#[macro_use] extern crate log;

pub mod error;
pub mod blockchain;
pub mod backend;
pub mod in_mem;

pub use blockchain::Info as ChainInfo;
pub use blockchain::BlockId;

use primitives::block;
use primitives::storage::{StorageKey, StorageData};

use blockchain::Backend as BlockchainBackend;
use backend::BlockImportOperation;
use state_machine::backend::Backend as StateBackend;

/// Polkadot Client
#[derive(Debug)]
pub struct Client<B, E> where B: backend::Backend {
	backend: B,
	executor: E,
}

/// Client info
#[derive(Debug)]
pub struct ClientInfo {
	/// Best block hash.
	pub chain: ChainInfo,
	/// Best block number in the queue.
	pub best_queued_number: Option<block::Number>,
	/// Best queued block hash.
	pub best_queued_hash: Option<block::HeaderHash>,
}

/// Information regarding the result of a call.
pub struct CallResult {
	/// The data that was returned from the call.
	pub return_data: Vec<u8>,
	/// The changes made to the state by the call.
	pub changes: state_machine::OverlayedChanges,
}

/// Block import result.
#[derive(Debug)]
pub enum ImportResult {
	/// Added to the import queue.
	Queued,
	/// Already in the import queue.
	AlreadyQueued,
	/// Already in the blockchain.
	AlreadyInChain,
	/// Block or parent is known to be bad.
	KnownBad,
	/// Block parent is not in the chain.
	UnknownParent,
}

/// Block status.
#[derive(Debug, PartialEq, Eq)]
pub enum BlockStatus {
	/// Added to the import queue.
	Queued,
	/// Already in the blockchain.
	InChain,
	/// Block or parent is known to be bad.
	KnownBad,
	/// Not in the queue or the blockchain.
	Unknown,
}

/// Create an instance of in-memory client.
pub fn new_in_mem<E, F>(
	executor: E,
	build_genesis: F
) -> error::Result<Client<in_mem::Backend, E>>
	where
		E: state_machine::CodeExecutor,
		F: FnOnce() -> (block::Header, Vec<(Vec<u8>, Vec<u8>)>)
{
	Client::new(in_mem::Backend::new(), executor, build_genesis)
}

impl<B, E> Client<B, E> where
	B: backend::Backend,
	E: state_machine::CodeExecutor,
	error::Error: From<<<B as backend::Backend>::State as state_machine::backend::Backend>::Error>,
{
	/// Creates new Polkadot Client with given blockchain and code executor.
	pub fn new<F>(
		backend: B,
		executor: E,
		build_genesis: F
	) -> error::Result<Self>
		where
			F: FnOnce() -> (block::Header, Vec<(Vec<u8>, Vec<u8>)>)
	{
		if backend.blockchain().header(BlockId::Number(0))?.is_none() {
			trace!("Empty database, writing genesis block");
			let (genesis_header, genesis_store) = build_genesis();
			let mut tx = backend.begin_transaction(BlockId::Hash(block::HeaderHash::default()))?;
			tx.reset_storage(genesis_store.into_iter())?;
			tx.import_block(genesis_header, None, true)?;
			backend.commit_transaction(tx)?;
		}
		Ok(Client {
			backend,
			executor,
		})
	}

	fn state_at(&self, hash: &block::HeaderHash) -> error::Result<B::State> {
		self.backend.state_at(BlockId::Hash(*hash))
	}

	/// Return single storage entry of contract under given address in state in a block of given hash.
	pub fn storage(&self, hash: &block::HeaderHash, key: &StorageKey) -> error::Result<StorageData> {
		Ok(self.state_at(hash)?
			.storage(&key.0)
			.map(|x| StorageData(x.to_vec()))?)
	}

	/// Execute a call to a contract on top of state in a block of given hash.
	///
	/// No changes are made.
	pub fn call(&self, hash: &block::HeaderHash, method: &str, call_data: &[u8]) -> error::Result<CallResult> {
		let state = self.state_at(hash)?;
		let mut changes = state_machine::OverlayedChanges::default();

		let _ = state_machine::execute(
			&state,
			&mut changes,
			&self.executor,
			method,
			call_data,
		)?;
		Ok(CallResult { return_data: vec![], changes })
	}

	/// Queue a block for import.
	pub fn import_block(&self, header: block::Header, body: Option<block::Body>) -> error::Result<ImportResult> {
		// TODO: import lock
		// TODO: validate block
		match self.backend.blockchain().status(BlockId::Hash(header.parent_hash))? {
			blockchain::BlockStatus::InChain => (),
			blockchain::BlockStatus::Unknown => return Ok(ImportResult::UnknownParent),
		}

		let mut transaction = self.backend.begin_transaction(BlockId::Number(header.number))?;
		let mut _state = transaction.state()?;
		// TODO: execute block on _state

		let is_new_best = header.number == self.backend.blockchain().info()?.best_number + 1;
		transaction.import_block(header, body, is_new_best)?;
		self.backend.commit_transaction(transaction)?;
		Ok(ImportResult::Queued)
	}

	/// Get blockchain info.
	pub fn info(&self) -> error::Result<ClientInfo> {
		let info = self.backend.blockchain().info().map_err(|e| error::Error::from_blockchain(Box::new(e)))?;
		Ok(ClientInfo {
			chain: info,
			best_queued_hash: None,
			best_queued_number: None,
		})
	}

	/// Get block status.
	pub fn block_status(&self, hash: &block::HeaderHash) -> error::Result<BlockStatus> {
		// TODO: more efficient implementation
		match self.backend.blockchain().header(BlockId::Hash(*hash)).map_err(|e| error::Error::from_blockchain(Box::new(e)))?.is_some() {
			true => Ok(BlockStatus::InChain),
			false => Ok(BlockStatus::Unknown),
		}
	}

	/// Get block hash by number.
	pub fn block_hash(&self, block_number: block::Number) -> error::Result<Option<block::HeaderHash>> {
		self.backend.blockchain().hash(block_number)
	}

	/// Get block header by hash.
	pub fn header(&self, hash: &block::HeaderHash) -> error::Result<Option<block::Header>> {
		self.backend.blockchain().header(BlockId::Hash(*hash))
	}
}
