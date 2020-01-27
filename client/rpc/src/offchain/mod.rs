// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Substrate offchain API.

#[cfg(test)]
mod tests;

/// Re-export the API for backward compatibility.
pub use sc_rpc_api::offchain::*;
use self::error::{Error, Result};
use sp_core::offchain::{OffchainStorage, StorageKind};
use parking_lot::Mutex;
use std::sync::Arc;

/// Offchain API
#[derive(Debug)]
pub struct Offchain<T: OffchainStorage> {
	/// Offchain storage
	storage: Arc<Mutex<T>>,
}

impl<T: OffchainStorage> Offchain<T> {
	/// Create new instance of Offchain API.
	pub fn new(storage: T) -> Self {
		Offchain {
			storage: Arc::new(Mutex::new(storage)),
		}
	}
}

impl<T: OffchainStorage + 'static> OffchainApi for Offchain<T> {
	/// Set offchain local storage under given key and prefix.
	fn set_local_storage(&self, kind: StorageKind, key: Vec<u8>, value: Vec<u8>) -> Result<()> {
		let prefix = match kind {
			StorageKind::PERSISTENT => sp_offchain::STORAGE_PREFIX,
			StorageKind::LOCAL => return Err(Error::UnavailableStorageKind),
		};
		self.storage.lock().set(prefix, key.as_slice(), value.as_slice());
		Ok(())
	}

	/// Get offchain local storage under given key and prefix.
	fn get_local_storage(&self, kind: StorageKind, key: Vec<u8>) -> Result<Option<Vec<u8>>> {
		let prefix = match kind {
			StorageKind::PERSISTENT => sp_offchain::STORAGE_PREFIX,
			StorageKind::LOCAL => return Err(Error::UnavailableStorageKind),
		};
		Ok(self.storage.lock().get(prefix, key.as_slice()))
	}
}
