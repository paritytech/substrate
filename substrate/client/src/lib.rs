// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Substrate Client

#![warn(missing_docs)]

extern crate substrate_primitives as primitives;
extern crate substrate_state_machine as state_machine;
extern crate substrate_serializer as ser;
extern crate substrate_codec as codec;
#[cfg(test)] #[macro_use] extern crate substrate_executor as executor;
extern crate ed25519;
#[cfg(test)] extern crate substrate_runtime_support as runtime_support;
#[cfg(test)] extern crate substrate_test_runtime as test_runtime;
#[cfg(test)] extern crate substrate_keyring as keyring;

extern crate triehash;
extern crate parking_lot;
#[cfg(test)] #[macro_use] extern crate hex_literal;
#[macro_use] extern crate error_chain;
#[macro_use] extern crate log;

pub mod error;
pub mod blockchain;
pub mod backend;
pub mod in_mem;
pub mod genesis;
pub mod block_builder;

pub use blockchain::Info as ChainInfo;
pub use blockchain::BlockId;
pub use block_builder::BlockBuilder;

use primitives::{block, AuthorityId};
use primitives::storage::{StorageKey, StorageData};
use codec::{KeyedVec, Slicable};

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
// TODO: split queue info from chain info and amalgamate into single struct.
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

	/// Get a reference to the state at a given block.
	pub fn state_at(&self, block: &BlockId) -> error::Result<B::State> {
		self.backend.state_at(*block)
	}

	/// Expose backend reference. To be used in tests only
	pub fn backend(&self) -> &B {
		&self.backend
	}

	/// Return single storage entry of contract under given address in state in a block of given hash.
	pub fn storage(&self, id: &BlockId, key: &StorageKey) -> error::Result<StorageData> {
		Ok(self.state_at(id)?
			.storage(&key.0)
			.map(|x| StorageData(x.to_vec()))?)
	}

	/// Get the code at a given block.
	pub fn code_at(&self, id: &BlockId) -> error::Result<Vec<u8>> {
		self.storage(id, &StorageKey(b":code".to_vec())).map(|data| data.0)
	}

	/// Clone a new instance of Executor.
	pub fn clone_executor(&self) -> E where E: Clone {
		self.executor.clone()
	}

	/// Get the current set of authorities from storage.
	pub fn authorities_at(&self, id: &BlockId) -> error::Result<Vec<AuthorityId>> {
		let state = self.state_at(id)?;
		(0..u32::decode(&mut state.storage(b":auth:len")?).ok_or(error::ErrorKind::AuthLen)?)
			.map(|i| state.storage(&i.to_keyed_vec(b":auth:"))
				.map_err(|_| error::ErrorKind::Backend)
				.and_then(|mut s| AuthorityId::decode(&mut s).ok_or(error::ErrorKind::Auth(i)))
				.map_err(Into::into)
			).collect()
	}

	/// Execute a call to a contract on top of state in a block of given hash.
	///
	/// No changes are made.
	pub fn call(&self, id: &BlockId, method: &str, call_data: &[u8]) -> error::Result<CallResult> {
		let mut changes = state_machine::OverlayedChanges::default();
		let return_data = state_machine::execute(
			&self.state_at(id)?,
			&mut changes,
			&self.executor,
			method,
			call_data,
		)?;
		Ok(CallResult { return_data, changes })
	}

	/// Create a new block, built on the head of the chain.
	pub fn new_block(&self) -> error::Result<BlockBuilder<B, E>> where E: Clone {
		BlockBuilder::new(self)
	}

	/// Queue a block for import.
	pub fn import_block(&self, header: block::Header, body: Option<block::Body>) -> error::Result<ImportResult> {
		// TODO: import lock
		// TODO: validate block
		match self.backend.blockchain().status(BlockId::Hash(header.parent_hash))? {
			blockchain::BlockStatus::InChain => (),
			blockchain::BlockStatus::Unknown => return Ok(ImportResult::UnknownParent),
		}

		let mut transaction = self.backend.begin_transaction(BlockId::Hash(header.parent_hash))?;
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
	pub fn block_status(&self, id: &BlockId) -> error::Result<BlockStatus> {
		// TODO: more efficient implementation
		match self.backend.blockchain().header(*id).map_err(|e| error::Error::from_blockchain(Box::new(e)))?.is_some() {
			true => Ok(BlockStatus::InChain),
			false => Ok(BlockStatus::Unknown),
		}
	}

	/// Get block hash by number.
	pub fn block_hash(&self, block_number: block::Number) -> error::Result<Option<block::HeaderHash>> {
		self.backend.blockchain().hash(block_number)
	}

	/// Get block header by id.
	pub fn header(&self, id: &BlockId) -> error::Result<Option<block::Header>> {
		self.backend.blockchain().header(*id)
	}

	/// Get block body by id.
	pub fn body(&self, id: &BlockId) -> error::Result<Option<block::Body>> {
		self.backend.blockchain().body(*id)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::Slicable;
	use keyring::Keyring;
	use test_runtime::genesismap::{GenesisConfig, additional_storage_with_genesis};
	use test_runtime;

	native_executor_instance!(Executor, test_runtime::api::dispatch, include_bytes!("../../test-runtime/wasm/target/wasm32-unknown-unknown/release/substrate_test_runtime.compact.wasm"));

	#[test]
	fn authorities_call_works() {
		let genesis_config = GenesisConfig::new_simple(vec![
			Keyring::Alice.to_raw_public(),
			Keyring::Bob.to_raw_public(),
			Keyring::Charlie.to_raw_public()
		], 1000);

		let prepare_genesis = || {
			let mut storage = genesis_config.genesis_map();
			let block = genesis::construct_genesis_block(&storage);
			storage.extend(additional_storage_with_genesis(&block));
			(primitives::block::Header::decode(&mut block.header.encode().as_ref()).expect("to_vec() always gives a valid serialisation; qed"), storage.into_iter().collect())
		};
		let client = new_in_mem(Executor::new(), prepare_genesis).unwrap();

		assert_eq!(client.authorities_at(&BlockId::Number(0)).unwrap(), vec![
			Keyring::Alice.to_raw_public(),
			Keyring::Bob.to_raw_public(),
			Keyring::Charlie.to_raw_public()
		]);
	}
}
