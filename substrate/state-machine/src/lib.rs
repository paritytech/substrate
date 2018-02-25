// Copyright 2017 Parity Technologies (UK) Ltd.
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

//! Substrate state machine implementation.

#![warn(missing_docs)]

extern crate substrate_primitives as primitives;

#[cfg_attr(test, macro_use)]
extern crate hex_literal;

extern crate hashdb;
extern crate memorydb;

extern crate patricia_trie;
extern crate triehash;

extern crate byteorder;

use std::collections::HashMap;
use std::collections::hash_map::Drain;
use std::fmt;

pub mod backend;
mod ext;
mod testing;

pub use testing::TestExternalities;
pub use ext::Ext;
pub use backend::Backend;

/// The overlayed changes to state to be queried on top of the backend.
///
/// A transaction shares all prospective changes within an inner overlay
/// that can be cleared.
#[derive(Debug, Default, Clone)]
pub struct OverlayedChanges {
	prospective: HashMap<Vec<u8>, Option<Vec<u8>>>,
	committed: HashMap<Vec<u8>, Option<Vec<u8>>>,
}

impl OverlayedChanges {
	/// Returns a double-Option: None if the key is unknown (i.e. and the query should be refered
	/// to the backend); Some(None) if the key has been deleted. Some(Some(...)) for a key whose
	/// value has been set.
	pub fn storage(&self, key: &[u8]) -> Option<Option<&[u8]>> {
		self.prospective.get(key)
			.or_else(|| self.committed.get(key))
			.map(|x| x.as_ref().map(AsRef::as_ref))
	}

	fn set_storage(&mut self, key: Vec<u8>, val: Option<Vec<u8>>) {
		self.prospective.insert(key, val);
	}

	/// Discard prospective changes to state.
	pub fn discard_prospective(&mut self) {
		self.prospective.clear();
	}

	/// Commit prospective changes to state.
	pub fn commit_prospective(&mut self) {
		if self.committed.is_empty() {
			::std::mem::swap(&mut self.prospective, &mut self.committed);
		} else {
			self.committed.extend(self.prospective.drain());
		}
	}

	/// Drain prospective changes to an iterator.
	pub fn drain(&mut self) -> Drain<Vec<u8>, Option<Vec<u8>>> {
		self.committed.drain()
	}
}

/// State Machine Error bound.
///
/// This should reflect WASM error type bound for future compatibility.
pub trait Error: 'static + fmt::Debug + fmt::Display + Send {}
impl<E> Error for E where E: 'static + fmt::Debug + fmt::Display + Send {}

/// Externalities Error.
///
/// Externalities are not really allowed to have errors, since it's assumed that dependent code
/// would not be executed unless externalities were available. This is included for completeness,
/// and as a transition away from the pre-existing framework.
#[derive(Debug, Eq, PartialEq)]
pub enum ExecutionError {
	/// The entry `:code` doesn't exist in storage so there's no way we can execute anything.
	CodeEntryDoesNotExist
}

impl fmt::Display for ExecutionError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "Externalities Error") }
}

/// Externalities: pinned to specific active address.
pub trait Externalities {
	/// Read storage of current contract being called.
	fn storage(&self, key: &[u8]) -> Option<&[u8]>;

	/// Set storage entry `key` of current contract being called (effective immediately).
	fn set_storage(&mut self, key: Vec<u8>, value: Vec<u8>) {
		self.place_storage(key, Some(value));
	}

	/// Clear a storage entry (`key`) of current contract being called (effective immediately).
	fn clear_storage(&mut self, key: &[u8]) {
		self.place_storage(key.to_vec(), None);
	}

	/// Set or clear a storage entry (`key`) of current contract being called (effective immediately).
	fn place_storage(&mut self, key: Vec<u8>, value: Option<Vec<u8>>);

	/// Get the identity of the chain.
	fn chain_id(&self) -> u64;

	/// Get the trie root of the current storage map.
	fn storage_root(&self) -> [u8; 32];
}

/// Code execution engine.
pub trait CodeExecutor: Sized + Send + Sync {
	/// Externalities error type.
	type Error: Error;

	/// Call a given method in the runtime.
	fn call<E: Externalities>(
		&self,
		ext: &mut E,
		code: &[u8],
		method: &str,
		data: &[u8],
	) -> Result<Vec<u8>, Self::Error>;
}

/// Execute a call using the given state backend, overlayed changes, and call executor.
///
/// On an error, no prospective changes are written to the overlay.
///
/// Note: changes to code will be in place if this call is made again. For running partial
/// blocks (e.g. a transaction at a time), ensure a differrent method is used.
pub fn execute<B: backend::Backend, Exec: CodeExecutor>(
	backend: &B,
	overlay: &mut OverlayedChanges,
	exec: &Exec,
	method: &str,
	call_data: &[u8],
) -> Result<Vec<u8>, Box<Error>>
{

	let result = {
		let mut externalities = ext::Ext {
			backend,
			overlay: &mut *overlay
		};
		// make a copy.
		let code = externalities.storage(b":code")
			.ok_or(Box::new(ExecutionError::CodeEntryDoesNotExist) as Box<Error>)?
			.to_vec();

		exec.call(
			&mut externalities,
			&code,
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
	use super::*;
	use super::backend::InMemory;
	use super::ext::Ext;

	#[test]
	fn overlayed_storage_works() {
		let mut overlayed = OverlayedChanges::default();

		let key = vec![42, 69, 169, 142];

		assert!(overlayed.storage(&key).is_none());

		overlayed.set_storage(key.clone(), Some(vec![1, 2, 3]));
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.commit_prospective();
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.set_storage(key.clone(), Some(vec![]));
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[][..]));

		overlayed.set_storage(key.clone(), None);
		assert!(overlayed.storage(&key).unwrap().is_none());

		overlayed.discard_prospective();
		assert_eq!(overlayed.storage(&key).unwrap(), Some(&[1, 2, 3][..]));

		overlayed.set_storage(key.clone(), None);
		overlayed.commit_prospective();
		assert!(overlayed.storage(&key).unwrap().is_none());
	}

	macro_rules! map {
		($( $name:expr => $value:expr ),*) => (
			vec![ $( ( $name, $value ) ),* ].into_iter().collect()
		)
	}

	#[test]
	fn overlayed_storage_root_works() {
		let mut backend = InMemory::from(map![
			b"doe".to_vec() => b"reindeer".to_vec(),
			b"dog".to_vec() => b"puppyXXX".to_vec(),
			b"dogglesworth".to_vec() => b"catXXX".to_vec(),
			b"doug".to_vec() => b"notadog".to_vec()
		]);
		let mut overlay = OverlayedChanges {
			committed: map![
				b"dog".to_vec() => Some(b"puppy".to_vec()),
				b"dogglesworth".to_vec() => Some(b"catYYY".to_vec()),
				b"doug".to_vec() => Some(vec![])
			],
			prospective: map![
				b"dogglesworth".to_vec() => Some(b"cat".to_vec()),
				b"doug".to_vec() => None
			],
		};
		let ext = Ext {
			backend: &mut backend,
			overlay: &mut overlay,
		};
		const ROOT: [u8; 32] = hex!("8aad789dff2f538bca5d8ea56e8abe10f4c7ba3a5dea95fea4cd6e7c3a1168d3");
		assert_eq!(ext.storage_root(), ROOT);
	}
}
