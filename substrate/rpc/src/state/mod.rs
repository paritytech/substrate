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

//! Polkadot state API.

mod error;

#[cfg(test)]
mod tests;

use std::sync::Arc;
use client::{ChainHead, StateData, ContractCaller};
use primitives::block;
use primitives::storage::{StorageKey, StorageData};

use self::error::Result;

build_rpc_trait! {
	/// Polkadot state API
	pub trait StateApi {
		/// Returns a storage entry.
		#[rpc(name = "state_getStorageAt")]
		fn storage_at(&self, StorageKey, block::HeaderHash) -> Result<StorageData>;

		/// Call a contract.
		#[rpc(name = "state_callAt")]
		fn call_at(&self, String, Vec<u8>, block::HeaderHash) -> Result<Vec<u8>>;

		/// Returns a storage entry.
		#[rpc(name = "state_getStorage")]
		fn storage(&self, StorageKey) -> Result<StorageData>;

		/// Call a contract.
		#[rpc(name = "state_call")]
		fn call(&self, String, Vec<u8>) -> Result<Vec<u8>>;
	}
}

/// State API.
pub struct State {
	/// Chain head shared instance.
	chain_head: Arc<ChainHead>,
	/// State data shared instance.
	state_data: Arc<StateData>,
	/// Contract caller shared instance.
	contract_caller: Arc<ContractCaller>,
}

impl State {
	/// Create new State API RPC handler.
	pub fn new(chain_head: Arc<ChainHead>, state_data: Arc<StateData>, contract_caller: Arc<ContractCaller>) -> Self {
		State {
			chain_head,
			state_data,
			contract_caller,
		}
	}
}

impl StateApi for State {
	fn storage_at(&self, key: StorageKey, block: block::HeaderHash) -> Result<StorageData> {
		Ok(self.state_data.storage(&block::Id::Hash(block), &key)?)
	}

	fn call_at(&self, method: String, data: Vec<u8>, block: block::HeaderHash) -> Result<Vec<u8>> {
		Ok(self.contract_caller.call(&block::Id::Hash(block), &method, &data)?.return_data)
	}

	fn storage(&self, key: StorageKey) -> Result<StorageData> {
		let at = block::Id::Hash(self.chain_head.best_block_hash()?);
		use primitives::hexdisplay::HexDisplay;
		info!("Querying storage at {:?} for key {}", at, HexDisplay::from(&key.0));
		Ok(self.state_data.storage(&at, &key)?)
	}

	fn call(&self, method: String, data: Vec<u8>) -> Result<Vec<u8>> {
		let at = block::Id::Hash(self.chain_head.best_block_hash()?);
		Ok(self.contract_caller.call(&at, &method, &data)?.return_data)
	}
}
