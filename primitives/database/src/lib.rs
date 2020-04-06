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

//! The main database trait, allowing Substrate to store data persistently.

/// An identifier for a column.
pub type ColumnId = u32;

/// An alteration to the database.
pub enum Change<H> {
	Set(ColumnId, Vec<u8>, Vec<u8>),
	Remove(ColumnId, Vec<u8>),
	Store(H, Vec<u8>),
	Release(H),
}

/// A series of changes to the database that can be committed atomically. They do not take effect
/// until passed into `Database::commit`.
pub struct Transaction<H>(pub Vec<Change<H>>);

impl<H> Transaction<H> {
	/// Set the value of `key` in `col` to `value`, replacing anything that is there currently.
	pub fn set(&mut self, col: ColumnId, key: &[u8], value: &[u8]) {
		self.0.push(Change::Set(col, key.to_vec(), value.to_vec()))
	}
	/// Remove the value of `key` in `col`.
	pub fn remove(&mut self, col: ColumnId, key: &[u8]) {
		self.0.push(Change::Remove(col, key.to_vec()))
	}
	/// Store the `preimage` of `hash` into the database, so that it may be looked up later with
	/// `Database::lookup`. This may be called multiple times, but `Database::lookup` but subsequent
	/// calls will ignore `preimage` and simply increase the number of references on `hash`.
	pub fn store(&mut self, hash: H, preimage: &[u8]) {
		self.0.push(Change::Store(hash, preimage.to_vec()))
	}
	/// Release the preimage of `hash` from the database. An equal number of these to the number of
	/// corresponding `store`s must have been given before it is legal for `Database::lookup` to
	/// be unable to provide the preimage.
	pub fn release(&mut self, hash: H) {
		self.0.push(Change::Release(hash))
	}
}

pub trait Database<H: Clone> {
	/// Create a new transaction to be prepared and committed atomically.
	fn new_transaction(&self) -> Transaction<H> { Transaction(Vec::new()) }
	/// Commit the `transaction` to the database atomically. Any further calls to `get` or `lookup`
	/// will reflect the new state.
	fn commit(&self, transaction: Transaction<H>) {
		for change in transaction.0.into_iter() {
			match change {
				Change::Set(col, key, value) => self.set(col, &key, &value),
				Change::Remove(col, key) => self.remove(col, &key),
				Change::Store(hash, preimage) => self.store(&hash, &preimage),
				Change::Release(hash) => self.release(&hash),
			}
		}
	}

	/// Retrieve the value previously stored against `key` or `None` if
	/// `key` is not currently in the database.
	fn get(&self, col: ColumnId, key: &[u8]) -> Option<Vec<u8>>;
	/// Call `f` with the value previously stored against `key` and return the result, or `None` if
	/// `key` is not currently in the database.
	///
	/// This may be faster than `get` since it doesn't allocate.
	fn with_get<R>(&self, col: ColumnId, key: &[u8], f: impl FnOnce(&[u8]) -> R) -> Option<R>;
	/// Set the value of `key` in `col` to `value`, replacing anything that is there currently.
	fn set(&self, col: ColumnId, key: &[u8], value: &[u8]) {
		let mut t = self.new_transaction();
		t.set(col, key, value);
		self.commit(t);
	}
	/// Remove the value of `key` in `col`.
	fn remove(&self, col: ColumnId, key: &[u8]) {
		let mut t = self.new_transaction();
		t.remove(col, key);
		self.commit(t);
	}

	/// Retrieve the first preimage previously `store`d for `hash` or `None` if no preimage is
	/// currently stored.
	fn lookup(&self, hash: &H) -> Option<Vec<u8>>;
	/// Call `f` with the preimage stored for `hash` and return the result, or `None` if no preimage
	/// is currently stored.
	///
	/// This may be faster than `get` since it doesn't allocate.
	fn with_lookup<R>(&self, hash: &H, f: impl FnOnce(&[u8]) -> R) -> Option<R>;
	/// Store the `preimage` of `hash` into the database, so that it may be looked up later with
	/// `Database::lookup`. This may be called multiple times, but `Database::lookup` but subsequent
	/// calls will ignore `preimage` and simply increase the number of references on `hash`.
	fn store(&self, hash: &H, preimage: &[u8]) {
		let mut t = self.new_transaction();
		t.store(hash.clone(), preimage);
		self.commit(t);
	}
	/// Release the preimage of `hash` from the database. An equal number of these to the number of
	/// corresponding `store`s must have been given before it is legal for `Database::lookup` to
	/// be unable to provide the preimage.
	fn release(&self, hash: &H) {
		let mut t = self.new_transaction();
		t.release(hash.clone());
		self.commit(t);
	}
}
