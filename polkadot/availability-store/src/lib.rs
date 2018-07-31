// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Persistent database for parachain data.

extern crate polkadot_primitives;
extern crate parking_lot;
extern crate substrate_codec as codec;
extern crate substrate_primitives;
extern crate kvdb;
extern crate kvdb_rocksdb;
extern crate kvdb_memorydb;

#[macro_use]
extern crate log;

use codec::{Encode, Decode};
use kvdb::{KeyValueDB, DBTransaction};
use kvdb_rocksdb::{Database, DatabaseConfig};
use polkadot_primitives::Hash;
use polkadot_primitives::parachain::{Id as ParaId, BlockData, Extrinsic};

use std::path::PathBuf;
use std::sync::Arc;
use std::io;

mod columns {
	pub const DATA: Option<u32> = Some(0);
	pub const EXTRINSIC: Option<u32> = Some(1);
	pub const NUM_COLUMNS: u32 = 2;
}

/// Configuration for the availability store.
pub struct Config {
	/// Cache size in bytes. If `None` default is used.
	pub cache_size: Option<usize>,
	/// Path to the database.
	pub path: PathBuf,
}

/// A key for extrinsic data -- relay chain parent hash and parachain ID.
pub struct Key(pub Hash, pub ParaId);

fn extract_io_err(err: ::kvdb::Error) -> io::Error {
	match err {
		::kvdb::Error(::kvdb::ErrorKind::Io(io_err), _) => io_err,
		::kvdb::Error(::kvdb::ErrorKind::Msg(msg), _) => io::Error::new(
			io::ErrorKind::Other,
			msg,
		),
		x => io::Error::new(
			io::ErrorKind::Other,
			format!("Unexpected error variant: {:?}", x), // only necessary because of nonexaustive match.
		)
	}
}

/// Handle to the availability store.
#[derive(Clone)]
pub struct Store {
	inner: Arc<KeyValueDB>,
}

impl Store {
	/// Create a new `Store` with given config on disk.
	pub fn new(config: Config) -> io::Result<Self> {
		let mut db_config = DatabaseConfig::with_columns(Some(columns::NUM_COLUMNS));
		db_config.memory_budget = config.cache_size;
		db_config.wal = true;

		let path = config.path.to_str().ok_or_else(|| io::Error::new(
			io::ErrorKind::Other,
			format!("Bad database path: {:?}", config.path),
		))?;

		let db = Database::open(&db_config, &path).map_err(extract_io_err)?;

		Ok(Store {
			inner: Arc::new(db),
		})
	}

	/// Create a new `Store` in-memory. Useful for tests.
	pub fn new_in_memory() -> Self {
		Store {
			inner: Arc::new(::kvdb_memorydb::create(::columns::NUM_COLUMNS)),
		}
	}

	/// Make some data available.
	pub fn make_available(&self, key: Key, block_data: BlockData, extrinsic: Option<Extrinsic>) -> io::Result<()> {
		let mut tx = DBTransaction::new();
		let encoded_key = (key.0, key.1).encode();

		if let Some(_extrinsic) = extrinsic {
			tx.put_vec(columns::EXTRINSIC, &*encoded_key, Vec::new());
		}

		tx.put_vec(columns::DATA, &encoded_key, block_data.encode());

		self.inner.write(tx).map_err(extract_io_err)
	}

	/// Query block data.
	pub fn block_data(&self, key: Key) -> Option<BlockData> {
		let encoded_key = (key.0, key.1).encode();
		match self.inner.get(columns::DATA, &encoded_key[..]) {
			Ok(Some(raw)) => Some(
				BlockData::decode(&mut &raw[..]).expect("all stored data serialized correctly; qed")
			),
			Ok(None) => None,
			Err(e) => {
				warn!(target: "availability", "Error reading from availability store: {:?}", e);
				None
			}
		}
	}

	/// Query extrinsic data.
	pub fn extrinsic(&self, key: Key) -> Option<Extrinsic> {
		let encoded_key = (key.0, key.1).encode();
		match self.inner.get(columns::EXTRINSIC, &encoded_key[..]) {
			Ok(Some(_raw)) => Some(Extrinsic),
			Ok(None) => None,
			Err(e) => {
				warn!(target: "availability", "Error reading from availability store: {:?}", e);
				None
			}
		}
	}
}

#[cfg(test)]
mod tests {

}
