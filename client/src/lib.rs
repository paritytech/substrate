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

use primitives::{block, Address, H256};
use primitives::contract::{CallData, OutData, StorageData};
use state_machine::backend::Backend;

use self::error::ResultExt;

/// Blockchain access
pub trait Blockchain {
	/// Error Type
	type Error;

	/// Returns the hash of latest block.
	fn latest_hash(&self) -> Result<block::HeaderHash, Self::Error>;

	/// Given a hash return a header
	fn header(&self, hash: &block::HeaderHash) -> Result<Option<block::Header>, Self::Error>;
}

/// Polkadot Client
#[derive(Debug)]
pub struct Client<B,  E> {
	blockchain: B,
	executor: E,
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
	B: Blockchain,
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
}
