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
use primitives::{block};
use primitives::contract::{CallData, StorageKey, StorageData};
use state_machine;

use self::error::Result;

build_rpc_trait! {
	/// Polkadot state API
	pub trait StateApi {
		/// Returns a storage entry.
		#[rpc(name = "state_getStorage")]
		fn storage(&self, StorageKey, block::HeaderHash) -> Result<StorageData>;

		/// Call a contract.
		#[rpc(name = "state_call")]
		fn call(&self, String, CallData, block::HeaderHash) -> Result<Vec<u8>>;
	}
}

impl<B, E> StateApi for Client<B, E> where
	B: client::backend::Backend + Send + Sync + 'static,
	E: state_machine::CodeExecutor + Send + Sync + 'static,
	client::error::Error: From<<<B as client::backend::Backend>::State as state_machine::backend::Backend>::Error>,
{
	fn storage(&self, key: StorageKey, block: block::HeaderHash) -> Result<StorageData> {
		Ok(self.storage(&block, &key)?)
	}

	fn call(&self, method: String, data: CallData, block: block::HeaderHash) -> Result<Vec<u8>> {
		Ok(self.call(&block, &method, &data)?.return_data)
	}
}
