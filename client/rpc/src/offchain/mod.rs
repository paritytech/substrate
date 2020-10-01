// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Substrate offchain API.

#[cfg(test)]
mod tests;

/// Re-export the API for backward compatibility.
pub use sc_rpc_api::offchain::*;
use sc_rpc_api::DenyUnsafe;
use self::error::{Error, Result};
use sp_core::{
	Bytes,
	offchain::{OffchainStorage, BlockChainOffchainStorage, StorageKind},
};
use parking_lot::RwLock;
use std::sync::Arc;

/// Offchain API
#[derive(Debug)]
pub struct Offchain<T: OffchainStorage, LT: BlockChainOffchainStorage> {
	/// Offchain storage
	storage: Arc<RwLock<T>>,
	/// Offchain storage for different blockchain states.
	local_storage: Arc<RwLock<LT>>,
	deny_unsafe: DenyUnsafe,
}

impl<T: OffchainStorage, LT: BlockChainOffchainStorage> Offchain<T, LT> {
	/// Create new instance of Offchain API.
	pub fn new(storage: T, local_storage: LT, deny_unsafe: DenyUnsafe) -> Self {
		Offchain {
			storage: Arc::new(RwLock::new(storage)),
			local_storage: Arc::new(RwLock::new(local_storage)),
			deny_unsafe,
		}
	}
}

impl<T: OffchainStorage + 'static, LT: BlockChainOffchainStorage + 'static> OffchainApi for Offchain<T, LT> {
	/// Set offchain local storage under given key and prefix.
	fn set_local_storage(&self, kind: StorageKind, key: Bytes, value: Bytes) -> Result<()> {
		self.deny_unsafe.check_if_safe()?;

		match kind {
			StorageKind::PERSISTENT => {
				self.storage.write().set(sp_offchain::STORAGE_PREFIX, &*key, &*value)
			},
			StorageKind::LOCAL => {
				let local_storage = self.local_storage.write();
				if let Some(block) = local_storage.latest() {
					if let Some(mut local_storage) = local_storage.at(block) {
						local_storage.set(sp_offchain::LOCAL_STORAGE_PREFIX, &*key, &*value);
						return Ok(())
					}
				}
				return Err(Error::UnavailableStorageState)
			},
		};
		Ok(())
	}

	/// Get offchain local storage under given key and prefix.
	fn get_local_storage(&self, kind: StorageKind, key: Bytes) -> Result<Option<Bytes>> {
		self.deny_unsafe.check_if_safe()?;

		Ok(match kind {
			StorageKind::PERSISTENT => self.storage.read().get(sp_offchain::STORAGE_PREFIX, &*key).map(Into::into),
			StorageKind::LOCAL => {
				let local_storage = self.local_storage.read();
				if let Some(block) = local_storage.latest() {
					if let Some(local_storage) = local_storage.at(block) {
						let v = local_storage.get(sp_offchain::LOCAL_STORAGE_PREFIX, &*key).map(Into::into);
						return Ok(v)
					}
				}
				return Err(Error::UnavailableStorageState)
			},
		})
	}
}
