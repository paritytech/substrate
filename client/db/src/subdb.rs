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

/// A `Database` adapter for subdb.

use sp_database::{self, ColumnId};
use parking_lot::RwLock;
use blake2_rfc::blake2b::blake2b;
use codec::Encode;
use subdb::{Database, KeyType};

/// A database hidden behind an RwLock, so that it implements Send + Sync.
///
/// Construct by creating a `Database` and then using `.into()`.
pub struct DbAdapter<H: KeyType>(RwLock<Database<H>>);

/// Wrap RocksDb database into a trait object that implements `sp_database::Database`
pub fn open<H: KeyType + 'static>(
	path: &std::path::Path,
	_num_columns: u32,
) -> Result<std::sync::Arc<dyn sp_database::Database<H>>, subdb::Error> {
	let db = subdb::Options::from_path(path.into()).open()?;
	Ok(std::sync::Arc::new(DbAdapter(RwLock::new(db))))
}

impl<H: KeyType> sp_database::Database<H> for DbAdapter<H> {
	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		let mut hash = H::default();
		(col, key).using_encoded(|d|
			hash.as_mut().copy_from_slice(blake2b(32, &[], d).as_bytes())
		);
		self.0.read().get(&hash)
	}

	fn with_get(&self, col: ColumnId, key: &[u8], f: &mut dyn FnMut(&[u8])) {
		let mut hash = H::default();
		(col, key).using_encoded(|d|
			hash.as_mut().copy_from_slice(blake2b(32, &[], d).as_bytes())
		);
		let _ = self.0.read().get_ref(&hash).map(|d| f(d.as_ref()));
	}

	fn set(&self, col: ColumnId, key: &[u8], value: &[u8]) {
		let mut hash = H::default();
		(col, key).using_encoded(|d|
			hash.as_mut().copy_from_slice(blake2b(32, &[], d).as_bytes())
		);
		self.0.write().insert(&value, &hash);
	}

	fn remove(&self, col: ColumnId, key: &[u8]) {
		let mut hash = H::default();
		(col, key).using_encoded(|d|
			hash.as_mut().copy_from_slice(blake2b(32, &[], d).as_bytes())
		);
		let _ = self.0.write().remove(&hash);
	}

	fn lookup(&self, hash: &H) -> Option<Vec<u8>> {
		self.0.read().get(hash)
	}

	fn with_lookup(&self, hash: &H, f: &mut dyn FnMut(&[u8])) {
		let _ = self.0.read().get_ref(hash).map(|d| f(d.as_ref()));
	}

	fn store(&self, hash: &H, preimage: &[u8]) {
		self.0.write().insert(preimage, hash);
	}

	fn release(&self, hash: &H) {
		let _ = self.0.write().remove(hash);
	}
}
