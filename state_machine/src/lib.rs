// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Polkadot state machine implementation.

#![warn(missing_docs)]

extern crate polkadot_primitives as primitives;

extern crate hashdb;
extern crate memorydb;
extern crate keccak_hash;

extern crate patricia_trie;
extern crate triehash;

extern crate byteorder;

use std::collections::HashMap;
use std::fmt;

use primitives::contract::{CallData};

pub mod backend;
mod ext;

/// Updates to be committed to the state.
pub enum Update {
	/// Set storage of object at given key -- empty is deletion.
	Storage(u64, Vec<u8>, Vec<u8>),
	/// Set code -- empty is deletion.
	Code(Vec<u8>),
}

// in-memory section of the state.
#[derive(Default)]
struct MemoryState {
	code: Option<Vec<u8>>,	// None is unchanged.
	storage: HashMap<u64, HashMap<Vec<u8>, Vec<u8>>>,
}

impl MemoryState {
	fn code(&self) -> Option<&[u8]> {
		self.code.as_ref().map(|x| &**x)
	}

	fn storage(&self, object: u64, key: &[u8]) -> Option<&[u8]> {
		self.storage.get(&object)
			.and_then(|m| m.get(key))
			.map(|v| &v[..])
	}

	#[allow(unused)]
	fn set_code(&mut self, code: Vec<u8>) {
		self.code = Some(code);
	}

	fn set_storage(&mut self, object: u64, key: Vec<u8>, val: Vec<u8>) {
		self.storage.entry(object)
			.or_insert_with(HashMap::new)
			.insert(key, val);
	}

	fn update<I>(&mut self, changes: I) where I: IntoIterator<Item=Update> {
		for update in changes {
			match update {
				Update::Storage(object, key, val) => {
					if val.is_empty() {
						let mut empty = false;
						if let Some(s) = self.storage.get_mut(&object) {
							s.remove(&key);
							empty = s.is_empty();
						};

						if empty { self.storage.remove(&object); }
					} else {
						self.storage.entry(object)
							.or_insert_with(HashMap::new)
							.insert(key, val);
					}
				}
				Update::Code(code) => {
					self.code = Some(code);
				}
			}
		}
	}
}

/// The overlayed changes to state to be queried on top of the backend.
///
/// A transaction shares all prospective changes within an inner overlay
/// that can be cleared.
#[derive(Default)]
pub struct OverlayedChanges {
	prospective: MemoryState,
	committed: MemoryState,
}

impl OverlayedChanges {
	fn code(&self) -> &[u8] {
		self.prospective.code()
			.or_else(|| self.committed.code())
			.unwrap_or_else(|| &[])
	}

	fn storage(&self, object: u64, key: &[u8]) -> Option<&[u8]> {
		self.prospective.storage(object, key)
			.or_else(|| self.committed.storage(object, key))
			.and_then(|v| if v.is_empty() { None } else { Some(v) })
	}

	#[allow(unused)]
	fn set_code(&mut self, code: Vec<u8>) {
		self.prospective.set_code(code);
	}

	fn set_storage(&mut self, object: u64, key: Vec<u8>, val: Vec<u8>) {
		self.prospective.set_storage(object, key, val);
	}

	/// Discard prospective changes to state.
	pub fn discard_prospective(&mut self) {
		self.prospective.code = None;
		self.prospective.storage.clear();
	}

	/// Commit prospective changes to state.
	pub fn commit_prospective(&mut self) {
		let code_updates = self.prospective.code.take().into_iter()
			.map(|code| Update::Code(code));

		let storage_updates = self.prospective.storage.drain()
			.flat_map(|(object, storages)| storages.into_iter().map(move |(k, v)| (object, k, v)))
			.map(|(object, key, value)| Update::Storage(object, key, value));

		self.committed.update(code_updates.chain(storage_updates));
	}
}

/// State Machine Error bound.
///
/// This should reflect WASM error type bound for future compatibility.
pub trait Error: 'static + fmt::Debug + fmt::Display + Send {}
impl<E> Error for E where E: 'static + fmt::Debug + fmt::Display + Send {}

/// Externalities: pinned to specific active address.
pub trait Externalities {
	/// Externalities error type.
	type Error: Error;

	/// Get the current runtime.
	fn code(&self) -> Result<&[u8], Self::Error>;

	/// Read storage of current contract being called.
	fn storage(&self, index: u64, key: &[u8]) -> Result<&[u8], Self::Error>;

	/// Set the new runtime.
	fn set_code(&mut self, code: Vec<u8>);

	/// Set storage of current contract being called.
	fn set_storage(&mut self, index: u64, key: Vec<u8>, value: Vec<u8>);
}

/// Code execution engine.
pub trait CodeExecutor: Sized {
	/// Externalities error type.
	type Error: Error;

	/// Call a given method in the runtime.
	fn call<E: Externalities>(
		&self,
		ext: &mut E,
		method: &str,
		data: &CallData,
	) -> Result<u64, Self::Error>;
}

/// Execute a call using the given state backend, overlayed changes, and call executor.
///
/// On an error, no prospective changes are written to the overlay.
pub fn execute<B: backend::Backend, Exec: CodeExecutor>(
	backend: &B,
	overlay: &mut OverlayedChanges,
	exec: &Exec,
	method: &str,
	call_data: &CallData,
) -> Result<u64, Box<Error>> {

	let result = {
		let mut externalities = ext::Ext {
			backend,
			overlay: &mut *overlay
		};

		exec.call(
			&mut externalities,
			method,
			call_data,
		)
	};

	match result {
		Ok(out) => {
			overlay.commit_prospective();
			Ok(out)
		}
		Err(e) => {
			overlay.discard_prospective();
			Err(Box::new(e))
		}
	}
}

#[cfg(test)]
mod tests {
	use super::OverlayedChanges;

	#[test]
	fn overlayed_storage_works() {
		let mut overlayed = OverlayedChanges::default();

		let key = vec![42, 69, 169, 142];
		let object = 69;

		assert!(overlayed.storage(object, &key).is_none());

		overlayed.set_storage(object, key, vec![1, 2, 3]);
		assert_eq!(overlayed.storage(object, &key).unwrap(), &[1, 2, 3]);

		overlayed.commit_prospective();
		assert_eq!(overlayed.storage(object, &key).unwrap(), &[1, 2, 3]);

		overlayed.set_storage(object, key, vec![]);
		assert!(overlayed.storage(object, &key).is_none());

		overlayed.discard_prospective();
		assert_eq!(overlayed.storage(object, &key).unwrap(), &[1, 2, 3]);

		overlayed.set_storage(object, key, vec![]);
		overlayed.commit_prospective();
		assert!(overlayed.storage(object, &key).is_none());
	}

	#[test]
	fn overlayed_code_works() {
		let mut overlayed = OverlayedChanges::default();

		let object = 69;

		assert!(overlayed.code(&object).is_none());

		overlayed.set_code(object, vec![1, 2, 3]);
		assert_eq!(overlayed.code(&object).unwrap(), &[1, 2, 3]);

		overlayed.commit_prospective();
		assert_eq!(overlayed.code(&object).unwrap(), &[1, 2, 3]);

		overlayed.set_code(object, vec![]);
		assert!(overlayed.code(&object).is_none());

		overlayed.discard_prospective();
		assert_eq!(overlayed.code(&object).unwrap(), &[1, 2, 3]);

		overlayed.set_code(object, vec![]);
		overlayed.commit_prospective();
		assert!(overlayed.code(&object).is_none());
	}
}
