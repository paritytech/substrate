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

//! Polkadot state API.

mod error;

#[cfg(test)]
mod tests;

use client::{self, Client};
use primitives::{block, Address, H256};
use primitives::contract::{CallData, OutData, StorageData};
use state_machine;

use self::error::Result;

build_rpc_trait! {
	/// Polkadot state API
	pub trait StateApi {
		/// Returns a storage entry.
		#[rpc(name = "state_getStorage")]
		fn storage(&self, Address, H256, block::HeaderHash) -> Result<StorageData>;

		/// Call a contract.
		#[rpc(name = "state_call")]
		fn call(&self, Address, String, CallData, block::HeaderHash) -> Result<OutData>;
	}
}

impl<B, E> StateApi for Client<B, E> where
	B: client::Blockchain + Send + Sync + 'static,
	E: state_machine::CodeExecutor + Send + Sync + 'static,
{
	fn storage(&self, address: Address, key: H256, block: block::HeaderHash) -> Result<StorageData> {
		Ok(self.storage(&block, &address, &key)?)
	}

	fn call(&self, address: Address, method: String, data: CallData, block: block::HeaderHash) -> Result<OutData> {
		Ok(self.call(&block, &address, &method, &data)?)
	}
}
