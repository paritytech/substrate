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

/// A `Database` adapter for parity-db.

use sp_database::{Database, DatabaseRef, Change, Transaction, ColumnId, StateCursor};

/// TODO EMCH make it private again (leaked from open input type)
pub struct DbAdapter(
	parity_db::Db,
	StateCursor<DbAdapter, BatchChildDelete>,
);

fn handle_err<T>(result: parity_db::Result<T>) -> T {
	match result {
		Ok(r) => r,
		Err(e) =>  {
			panic!("Critical database eror: {:?}", e);
		}
	}
}

/// Wrap ParityDb database into a trait object that implements `sp_database::Database`
pub fn open<H: Clone>(
	path: &std::path::Path,
	num_columns: u32,
	cursor: StateCursor<DbAdapter, BatchChildDelete>,
) -> parity_db::Result<std::sync::Arc<dyn Database<H>>> {
	let db = parity_db::Db::with_columns(path, num_columns as u8)?;
	Ok(std::sync::Arc::new(DbAdapter(db, cursor)))
}

const BATCH_CHILD_DELETE_SIZE: usize = 256;

/// TODO EMCH make it private (leaked from open input type)
pub struct BatchChildDelete {
	ix: usize,
	batch: Vec<(u8, Vec<u8>)>,
}

impl<H: Clone> Database<H> for DbAdapter {
	fn commit(&self, transaction: Transaction<H>) {
		transaction.0.iter().for_each(|change|
			match change {
				Change::DeleteChild(col, child) => {
					let mut batch = BatchChildDelete {
						ix: 0,
						batch: vec![(0, Vec::new()); 256],
					};

					fn extract_input(i: &mut (u8, Vec<u8>)) -> (u8, Vec<u8>, Option<Vec<u8>>) {
						let key = std::mem::replace(&mut i.1, Vec::new());
						(i.0, key, None)
					};

					self.1(&self, *col, child.clone(), &mut batch, |db, col, key, batch| {
						batch.batch[batch.ix] = (col as u8, key.to_vec());
						batch.ix += 1;
						if batch.ix == BATCH_CHILD_DELETE_SIZE {
							handle_err(db.0.commit(batch.batch[..].iter_mut().map(extract_input)));
							batch.ix = 0;
						}
					});

					if batch.ix > 0 {
						handle_err(self.0.commit(batch.batch[..batch.ix].iter_mut().map(extract_input)));
					}
					
				},
				_ => (),
			}
		);

		handle_err(self.0.commit(transaction.0.into_iter().filter_map(|change|
			match change {
				Change::Set(col, key, value) => Some((col as u8, key, Some(value))),
				Change::Remove(col, key) => Some((col as u8, key, None)),
				Change::DeleteChild(..) => None,
				_ => unimplemented!(),
			}))
		);
	}

	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		handle_err(self.0.get(col as u8, key))
	}

	fn lookup(&self, _hash: &H) -> Option<Vec<u8>> {
		unimplemented!();
	}
}

impl DatabaseRef for DbAdapter {
	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		handle_err(self.0.get(col as u8, key))
	}
}
