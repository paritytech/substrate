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

extern crate polkadot_primitives as primitives;
extern crate polkadot_state_machine as state_machine;

#[macro_use]
extern crate error_chain;

pub mod error;
pub mod blockchain;

pub use blockchain::ChainInfo;

use primitives::{block, Address, H256};
use primitives::contract::{CallData, OutData, StorageData};
use state_machine::backend::Backend;

use self::error::ResultExt;

/// Polkadot Client
#[derive(Debug)]
pub struct Client<B, E> {
	blockchain: B,
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
	/// Import was attempted and ended with an error.
	Err(error::Error),
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

impl<B, E> Client<B, E> {
	/// Creates new Polkadot Client with given blockchain and code executor.
	pub fn new(blockchain: B, executor: E) -> Self {
		Client {
			blockchain,
			executor,
		}
	}
}

impl<B, E> Client<B, E> where
	B: blockchain::Blockchain,
	E: state_machine::CodeExecutor,
{

	fn state_at(&self, _hash: &block::HeaderHash) -> error::Result<state_machine::backend::InMemory> {
		// TODO [ToDr] Actually retrieve the state.
		Ok(state_machine::backend::InMemory::default())
	}

	/// Return single storage entry of contract under given address in state in a block of given hash.
	pub fn storage(&self, hash: &block::HeaderHash, address: &Address, key: &H256) -> error::Result<StorageData> {
		self.state_at(hash)?
			.storage(address, key)
			.map(|x| StorageData(x.to_vec()))
			.chain_err(|| error::ErrorKind::Backend)
	}

	/// Execute a call to a contract on top of state in a block of given hash.
	pub fn call(&self, hash: &block::HeaderHash, address: &Address, method: &str, call_data: &CallData) -> error::Result<OutData> {
		let state = self.state_at(hash)?;
		let mut changes = state_machine::OverlayedChanges::default();

		Ok(state_machine::execute(
			&state,
			&mut changes,
			&self.executor,
			address,
			method,
			call_data,
		)?)
	}

	/// Queue a block for import.
	pub fn import_block(&self, header: block::Header, body: Option<block::Body>) -> ImportResult {
		// TODO: add to queue

		// TODO: validate block here
		match self.blockchain.import(header, body) {
			blockchain::ImportResult::Imported => ImportResult::Queued,
			blockchain::ImportResult::AlreadyInChain => ImportResult::AlreadyInChain,
			blockchain::ImportResult::UnknownParent => ImportResult::UnknownParent,
			blockchain::ImportResult::Err(e) => ImportResult::Err(error::Error::from_blockchain(Box::new(e))),
		}
	}

	/// Get blockchain info.
	pub fn info(&self) -> error::Result<ClientInfo> {
		let info = self.blockchain.info().map_err(|e| error::Error::from_blockchain(Box::new(e)))?;
		Ok(ClientInfo {
			chain: info,
			best_queued_hash: None,
			best_queued_number: None,
		})
	}

	/// Get block status.
	pub fn block_status(&self, hash: &block::HeaderHash) -> error::Result<BlockStatus> {
		// TODO: more efficient implementation
		match self.blockchain.header(hash).map_err(|e| error::Error::from_blockchain(Box::new(e)))?.is_some() {
			true => Ok(BlockStatus::InChain),
			false => Ok(BlockStatus::Unknown),
		}
	}

	/// Get block hash by number.
	pub fn block_hash(&self, block_number: block::Number) -> error::Result<Option<block::HeaderHash>> {
		self.blockchain.hash(block_number).map_err(|e| error::Error::from_blockchain(Box::new(e)))
	}
}
