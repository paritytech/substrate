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
use client::{self, Client, CallExecutor};
use primitives::{block, Hash, blake2_256};
use primitives::storage::{StorageKey, StorageData};
use primitives::hexdisplay::HexDisplay;
use state_machine;

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

		/// Returns the hash of a storage entry.
		#[rpc(name = "state_getStorageHashAt")]
		fn storage_hash_at(&self, StorageKey, block::HeaderHash) -> Result<Hash>;

		/// Returns the size of a storage entry.
		#[rpc(name = "state_getStorageSizeAt")]
		fn storage_size_at(&self, StorageKey, block::HeaderHash) -> Result<u64>;

		/// Returns the hash of a storage entry.
		#[rpc(name = "state_getStorageHash")]
		fn storage_hash(&self, StorageKey) -> Result<Hash>;

		/// Returns the size of a storage entry.
		#[rpc(name = "state_getStorageSize")]
		fn storage_size(&self, StorageKey) -> Result<u64>;

		/// Returns a storage entry.
		#[rpc(name = "state_getStorage")]
		fn storage(&self, StorageKey) -> Result<StorageData>;

		/// Call a contract.
		#[rpc(name = "state_call")]
		fn call(&self, String, Vec<u8>) -> Result<Vec<u8>>;
	}
}

impl<B, E> StateApi for Arc<Client<B, E>> where
	B: client::backend::Backend + Send + Sync + 'static,
	E: CallExecutor + Send + Sync + 'static,
	client::error::Error: From<<<B as client::backend::Backend>::State as state_machine::backend::Backend>::Error>,
{
	fn storage_at(&self, key: StorageKey, block: block::HeaderHash) -> Result<StorageData> {
		trace!(target: "rpc", "Querying storage at {:?} for key {}", block, HexDisplay::from(&key.0));
		Ok(self.as_ref().storage(&block::Id::Hash(block), &key)?)
	}

	fn call_at(&self, method: String, data: Vec<u8>, block: block::HeaderHash) -> Result<Vec<u8>> {
		trace!(target: "rpc", "Calling runtime at {:?} for method {} ({})", block, method, HexDisplay::from(&data));
		Ok(self.as_ref().executor().call(&block::Id::Hash(block), &method, &data)?.return_data)
	}

	fn storage_hash_at(&self, key: StorageKey, block: block::HeaderHash) -> Result<Hash> {
		self.storage_at(key, block).map(|x| blake2_256(&x.0).into())
	}

	fn storage_size_at(&self, key: StorageKey, block: block::HeaderHash) -> Result<u64> {
		self.storage_at(key, block).map(|x| x.0.len() as u64)
	}

	fn storage_hash(&self, key: StorageKey) -> Result<Hash> {
		self.storage_hash_at(key, self.as_ref().info()?.chain.best_hash)
	}

	fn storage_size(&self, key: StorageKey) -> Result<u64> {
		self.storage_size_at(key, self.as_ref().info()?.chain.best_hash)
	}

	fn storage(&self, key: StorageKey) -> Result<StorageData> {
		self.storage_at(key, self.as_ref().info()?.chain.best_hash)
	}

	fn call(&self, method: String, data: Vec<u8>) -> Result<Vec<u8>> {
		self.call_at(method, data, self.as_ref().info()?.chain.best_hash)
	}
}
