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

pub trait OffstateBackend: Send + Sync {
	/// Retrieve a value from storage under given key.
	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, String>;

	/// Return in memory all values for this backend, mainly for
	/// tests.
	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)>;

}

impl OffstateBackend for TODO2 {

	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		unimplemented!()
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		unimplemented!()
	}

}

impl OffstateBackend for Arc<dyn OffstateBackend> {
	fn get(&self, key: &[u8]) -> Result<Option<Vec<u8>>, String> {
		OffstateBackend::get(self.deref(), key)
	}
	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		OffstateBackend::pairs(self.deref())
	}
}


/// need to keep multiple block state.
/// TODO rename to something like SingleState
pub struct TODO2;

