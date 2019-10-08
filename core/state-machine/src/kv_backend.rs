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

//! Backend for storing data without a state.

use std::sync::Arc;
use std::collections::HashMap;
use std::ops::Deref;

/// This covers kv values access.
/// It target a single history state (state machine
/// only run for a single history state).
pub trait KvBackend: Send + Sync {
	/// Retrieve a value from storage under given key.
	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, String>;

	/// Return all values (in memory) for this backend, mainly for
	/// tests. This method should only be use for testing or
	/// for small kv.
	/// It returns a map to be aligned with internal in memory storage
	/// types.
	fn pairs(&self) -> HashMap<Vec<u8>, Option<Vec<u8>>>;
}

/// need to keep multiple block state.
pub type InMemory = HashMap<Vec<u8>, Option<Vec<u8>>>;

impl KvBackend for InMemory {
	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		Ok(self.get(key).map(Clone::clone).unwrap_or(None))
	}

	fn pairs(&self) -> HashMap<Vec<u8>, Option<Vec<u8>>> {
		self.clone()
	}
}

impl KvBackend for Arc<dyn KvBackend> {
	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		KvBackend::get(self.deref(), key)
	}

	fn pairs(&self) -> HashMap<Vec<u8>, Option<Vec<u8>>> {
		KvBackend::pairs(self.deref())
	}
}
