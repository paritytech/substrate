// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use crate::utils::DatabaseType;
use sp_database::{error::DatabaseError, Change, ColumnId, Database, Transaction};
use redis::{RedisResult, Commands, ToRedisArgs, RedisWrite};
use parking_lot::Mutex;
use std::ops::DerefMut;

struct DbAdapter(Mutex<redis::Connection>);

fn handle_err<T>(result: RedisResult<T>) -> T {
	match result {
		Ok(r) => r,
		Err(e) => {
			panic!("Critical database error: {:?}", e);
		},
	}
}

pub fn open<H: Clone + AsRef<[u8]>>(
	url: &str,
	db_type: DatabaseType,
) -> RedisResult<std::sync::Arc<dyn Database<H>>> {
	let client = redis::Client::open(url)?;

	match db_type {
		DatabaseType::Full => {
			Ok(std::sync::Arc::new(DbAdapter(Mutex::new(client.get_connection()?))))
		}
	}
}

struct RefColumn(ColumnId);

impl ToRedisArgs for RefColumn {
	fn write_redis_args<W: ?Sized + RedisWrite>(&self, out: &mut W) {
		"ref:".write_redis_args(out);
		self.0.write_redis_args(out);
	}
}

impl<H: Clone + AsRef<[u8]>> Database<H> for DbAdapter {
	fn commit(&self, transaction: Transaction<H>) -> Result<(), DatabaseError> {
		let mut potential_garbages = Vec::new();

		let mut pipe = redis::pipe();
		pipe.atomic();

		for change in transaction.0 {
			match change {
				Change::Set(col, key, value) => {
					pipe.hset(col, key, value);
				},
				Change::Remove(col, key) => {
					pipe.hdel(col, key);
				},
				Change::Store(col, key, value) => {
					pipe.hset(col, key.as_ref(), value);
					pipe.hincr(RefColumn(col), key.as_ref(), 1);
				},
				Change::Reference(col, key) => {
					pipe.hincr(RefColumn(col), key.as_ref(), 1);
				},
				Change::Release(col, key) => {
					pipe.hincr(RefColumn(col), key.as_ref(), -1);
					potential_garbages.push((col, key));
				},
			}
		}

		let mut conn = self.0.lock();
		pipe.query(conn.deref_mut()).map_err(|e| DatabaseError(Box::new(e)))?;

		for (col, key) in potential_garbages {
			let refcount: i64 = conn.hget(RefColumn(col), key.as_ref()).map_err(|e| DatabaseError(Box::new(e)))?;
			if refcount < 1 {
				redis::pipe().atomic().hdel(RefColumn(col), key.as_ref()).hdel(col, key.as_ref())
					.query(conn.deref_mut()).map_err(|e| DatabaseError(Box::new(e)))?;
			}
		}

		Ok(())
	}

	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>> {
		handle_err(self.0.lock().hget(col, key))
	}

	fn contains(&self, col: ColumnId, key: &[u8]) -> bool {
		handle_err(self.0.lock().hexists(col, key))
	}

	fn value_size(&self, col: ColumnId, key: &[u8]) -> Option<usize> {
		let value_size = handle_err(redis::cmd("HSTRLEN").arg(col).arg(key).query(self.0.lock().deref_mut()));
		if value_size == 0 {
			None
		} else {
			Some(value_size)
		}
	}

	fn supports_ref_counting(&self) -> bool {
		true
	}

	fn sanitize_key(&self, _key: &mut Vec<u8>) { }
}
