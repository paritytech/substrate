// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! RocksDB-based offchain workers local storage.

use std::sync::Arc;

use kvdb::KeyValueDB;

/// Offchain local storage
#[derive(Clone)]
pub struct LocalStorage {
	db: Arc<KeyValueDB>,
}

impl std::fmt::Debug for LocalStorage {
	fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
		fmt.debug_struct("LocalStorage")
			.finish()
	}
}

impl LocalStorage {
	#[cfg(any(test, feature = "test-helpers"))]
	pub fn new_test() -> Self {
		let db = Arc::new(::kvdb_memorydb::create(crate::utils::NUM_COLUMNS));
		Self::new(db as _)
	}

	pub fn new(db: Arc<KeyValueDB>) -> Self {
		Self {
			db,
		}
	}
}

