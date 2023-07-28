// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! The main database trait, allowing Substrate to store data persistently.

pub mod error;
mod kvdb;
mod mem;

pub use crate::kvdb::as_database;
pub use mem::MemDb;

/// An identifier for a column.
pub type ColumnId = u32;

/// An alteration to the database.
#[derive(Clone)]
pub enum Change<H> {
	Set(ColumnId, Vec<u8>, Vec<u8>),
	Remove(ColumnId, Vec<u8>),
	Store(ColumnId, H, Vec<u8>),
	Reference(ColumnId, H),
	Release(ColumnId, H),
}

/// A series of changes to the database that can be committed atomically. They do not take effect
/// until passed into `Database::commit`.
#[derive(Default, Clone)]
pub struct Transaction<H>(pub Vec<Change<H>>);

impl<H> Transaction<H> {
	/// Create a new transaction to be prepared and committed atomically.
	pub fn new() -> Self {
		Transaction(Vec::new())
	}
	/// Set the value of `key` in `col` to `value`, replacing anything that is there currently.
	pub fn set(&mut self, col: ColumnId, key: &[u8], value: &[u8]) {
		self.0.push(Change::Set(col, key.to_vec(), value.to_vec()))
	}
	/// Set the value of `key` in `col` to `value`, replacing anything that is there currently.
	pub fn set_from_vec(&mut self, col: ColumnId, key: &[u8], value: Vec<u8>) {
		self.0.push(Change::Set(col, key.to_vec(), value))
	}
	/// Remove the value of `key` in `col`.
	pub fn remove(&mut self, col: ColumnId, key: &[u8]) {
		self.0.push(Change::Remove(col, key.to_vec()))
	}
	/// Store the `preimage` of `hash` into the database, so that it may be looked up later with
	/// `Database::get`. This may be called multiple times, but subsequent
	/// calls will ignore `preimage` and simply increase the number of references on `hash`.
	pub fn store(&mut self, col: ColumnId, hash: H, preimage: Vec<u8>) {
		self.0.push(Change::Store(col, hash, preimage))
	}
	/// Increase the number of references for `hash` in the database.
	pub fn reference(&mut self, col: ColumnId, hash: H) {
		self.0.push(Change::Reference(col, hash))
	}
	/// Release the preimage of `hash` from the database. An equal number of these to the number of
	/// corresponding `store`s must have been given before it is legal for `Database::get` to
	/// be unable to provide the preimage.
	pub fn release(&mut self, col: ColumnId, hash: H) {
		self.0.push(Change::Release(col, hash))
	}
}

pub trait Database<H: Clone + AsRef<[u8]>>: Send + Sync {
	/// Commit the `transaction` to the database atomically. Any further calls to `get` or `lookup`
	/// will reflect the new state.
	fn commit(&self, transaction: Transaction<H>) -> error::Result<()>;

	/// Retrieve the value previously stored against `key` or `None` if
	/// `key` is not currently in the database.
	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>>;

	/// Check if the value exists in the database without retrieving it.
	fn contains(&self, col: ColumnId, key: &[u8]) -> bool {
		self.get(col, key).is_some()
	}

	/// Check value size in the database possibly without retrieving it.
	fn value_size(&self, col: ColumnId, key: &[u8]) -> Option<usize> {
		self.get(col, key).map(|v| v.len())
	}

	/// Call `f` with the value previously stored against `key`.
	///
	/// This may be faster than `get` since it doesn't allocate.
	/// Use `with_get` helper function if you need `f` to return a value from `f`
	fn with_get(&self, col: ColumnId, key: &[u8], f: &mut dyn FnMut(&[u8])) {
		self.get(col, key).map(|v| f(&v));
	}

	/// Check if database supports internal ref counting for state data.
	///
	/// For backwards compatibility returns `false` by default.
	fn supports_ref_counting(&self) -> bool {
		false
	}

	/// Remove a possible path-prefix from the key.
	///
	/// Not all database implementations use a prefix for keys, so this function may be a noop.
	fn sanitize_key(&self, _key: &mut Vec<u8>) {}
}

impl<H> std::fmt::Debug for dyn Database<H> {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "Database")
	}
}

/// Call `f` with the value previously stored against `key` and return the result, or `None` if
/// `key` is not currently in the database.
///
/// This may be faster than `get` since it doesn't allocate.
pub fn with_get<R, H: Clone + AsRef<[u8]>>(
	db: &dyn Database<H>,
	col: ColumnId,
	key: &[u8],
	mut f: impl FnMut(&[u8]) -> R,
) -> Option<R> {
	let mut result: Option<R> = None;
	let mut adapter = |k: &_| {
		result = Some(f(k));
	};
	db.with_get(col, key, &mut adapter);
	result
}
