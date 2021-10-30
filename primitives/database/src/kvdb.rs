// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

/// A wrapper around `kvdb::Database` that implements `sp_database::Database` trait
use ::kvdb::{DBTransaction, KeyValueDB};

use crate::{error, Change, ColumnId, Database, Transaction};

struct DbAdapter<D: KeyValueDB + 'static>(D);

fn handle_err<T>(result: std::io::Result<T>) -> T {
	match result {
		Ok(r) => r,
		Err(e) => {
			panic!("Critical database error: {:?}", e);
		},
	}
}

/// Wrap RocksDb database into a trait object that implements `sp_database::Database`
pub fn as_database<D, H>(db: D) -> std::sync::Arc<dyn Database<H>>
where
	D: KeyValueDB + 'static,
	H: Clone + AsRef<[u8]>,
{
	std::sync::Arc::new(DbAdapter(db))
}

impl<D: KeyValueDB> DbAdapter<D> {
	// Returns counter key and counter value if it exists.
	fn read_counter(&self, col: ColumnId, key: &[u8]) -> error::Result<(Vec<u8>, Option<u32>)> {
		// Add a key suffix for the counter
		let mut counter_key = key.to_vec();
		counter_key.push(0);
		Ok(match self.0.get(col, &counter_key).map_err(|e| error::DatabaseError(Box::new(e)))? {
			Some(data) => {
				let mut counter_data = [0; 4];
				if data.len() != 4 {
					return Err(error::DatabaseError(Box::new(std::io::Error::new(
						std::io::ErrorKind::Other,
						format!("Unexpected counter len {}", data.len()),
					))))
				}
				counter_data.copy_from_slice(&data);
				let counter = u32::from_le_bytes(counter_data);
				(counter_key, Some(counter))
			},
			None => (counter_key, None),
		})
	}
}

impl<D: KeyValueDB, H: Clone + AsRef<[u8]>> Database<H> for DbAdapter<D> {
	fn commit(&self, transaction: Transaction<H>) -> error::Result<()> {
		let mut tx = DBTransaction::new();
		for change in transaction.0.into_iter() {
			match change {
				Change::Set(col, key, value) => tx.put_vec(col, &key, value),
				Change::Remove(col, key) => tx.delete(col, &key),
				Change::Store(col, key, value) => match self.read_counter(col, key.as_ref())? {
					(counter_key, Some(mut counter)) => {
						counter += 1;
						tx.put(col, &counter_key, &counter.to_le_bytes());
					},
					(counter_key, None) => {
						let d = 1u32.to_le_bytes();
						tx.put(col, &counter_key, &d);
						tx.put_vec(col, key.as_ref(), value);
					},
				},
				Change::Reference(col, key) => {
					if let (counter_key, Some(mut counter)) =
						self.read_counter(col, key.as_ref())?
					{
						counter += 1;
						tx.put(col, &counter_key, &counter.to_le_bytes());
					}
				},
				Change::Release(col, key) => {
					if let (counter_key, Some(mut counter)) =
						self.read_counter(col, key.as_ref())?
					{
						counter -= 1;
						if counter == 0 {
							tx.delete(col, &counter_key);
							tx.delete(col, key.as_ref());
						} else {
							tx.put(col, &counter_key, &counter.to_le_bytes());
						}
					}
				},
			}
		}
		self.0.write(tx).map_err(|e| error::DatabaseError(Box::new(e)))
	}

	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		handle_err(self.0.get(col, key))
	}

	fn contains(&self, col: ColumnId, key: &[u8]) -> bool {
		handle_err(self.0.has_key(col, key))
	}
}
