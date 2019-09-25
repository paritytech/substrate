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
use std::ops::Deref;

pub trait OffstateBackendStorage {
/*	/// state type for querying data
	/// (similar to hash for a trie_backend).
	trait ChanState;*/

	/// Retrieve a value from storage under given key and prefix.
	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>>;

	/// Return in memory all values for this backend, mainly for
	/// tests.
	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)>;
}

pub trait OffstateStorage {

	/// Persist a value in storage under given key and prefix.
	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]);

	/// Retrieve a value from storage under given key and prefix.
	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>>;

	/// Return in memory all values for this backend, mainly for
	/// tests.
	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)>;

}

impl<N> OffstateBackendStorage for TODO<N> {

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		unimplemented!()
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		unimplemented!()
	}

}

impl OffstateBackendStorage for TODO2 {

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		unimplemented!()
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		unimplemented!()
	}

}


// This implementation is used by normal storage trie clients.
impl OffstateBackendStorage for Arc<dyn OffstateStorage> {

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		OffstateStorage::get(self.deref(), prefix, key)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		OffstateStorage::pairs(self.deref())
	}

}


impl<N> OffstateStorage for TODO<N> {

	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		unimplemented!()
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		<Self as OffstateBackendStorage>::get(&self, prefix, key)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		<Self as OffstateBackendStorage>::pairs(&self)
	}

}

impl OffstateStorage for TODO2 {

	fn set(&mut self, prefix: &[u8], key: &[u8], value: &[u8]) {
		unimplemented!()
	}

	fn get(&self, prefix: &[u8], key: &[u8]) -> Option<Vec<u8>> {
		<Self as OffstateBackendStorage>::get(&self, prefix, key)
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		<Self as OffstateBackendStorage>::pairs(&self)
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
