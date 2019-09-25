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

/// TODO EMCH merge offstate storage and offstate backend storage ??

use std::sync::Arc;
use std::ops::Deref;

/// TODO EMCH replace ofstate storage?
pub trait OffstateStorage: Send + Sync {
	/// Retrieve a value from storage under given key.
	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, String>;

	/// Return in memory all values for this backend, mainly for
	/// tests.
	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)>;
}

pub trait OffstateBackendStorage: Send + Sync {
/*	/// state type for querying data
	/// (similar to hash for a trie_backend).
	trait ChanState;*/

	/// Retrieve a value from storage under given key.
	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, String>;

	/// Return in memory all values for this backend, mainly for
	/// tests.
	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)>;

}

/*// TODO EMCH is it use??
pub trait OffstateStorage {

	/// Persist a value in storage under given key.
	fn set(&mut self, key: &[u8], value: &[u8]);

	/// Retrieve a value from storage under given key.
	fn get(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Return in memory all values for this backend, mainly for
	/// tests.
	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)>;

}*/

impl<N: Sync + Send> OffstateBackendStorage for TODO<N> {

	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		unimplemented!()
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		unimplemented!()
	}

}

impl OffstateBackendStorage for TODO2 {

	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		unimplemented!()
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		unimplemented!()
	}

}

// This implementation is used by normal storage trie clients.
impl OffstateBackendStorage for Arc<dyn OffstateStorage> {
	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		OffstateStorage::get(self.deref(), key)
	}
	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		OffstateStorage::pairs(self.deref())
	}
}



impl<N: Send + Sync> OffstateStorage for TODO<N> {

	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		<Self as OffstateBackendStorage>::get(&self, key)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		unimplemented!()
	}

}


impl OffstateStorage for TODO2 {

	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		<Self as OffstateBackendStorage>::get(&self, key)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		unimplemented!()
	}

}


/// TODO EMCH implement, no branch ranges.
pub struct TODO<N>(N);

/// TODO EMCH variant for proof check or no
/// need to keep multiple block state.
/// TODO rename to something like SingleState
pub struct TODO2;

impl<N> TODO<N> {
	/// Build for a given block number.
	/// TODO EMCH may or may not need a branch index to
	pub fn new(block_number: N) -> Self {
		TODO(block_number)
	}
}

impl<N> TODO<N> {
}
