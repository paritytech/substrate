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
#[macro_use]
extern crate hex_literal;

extern crate hashdb;
extern crate memorydb;

extern crate patricia_trie;
extern crate triehash;

extern crate byteorder;

use std::collections::HashMap;
use std::fmt;

use primitives::contract::{CallData};

pub mod backend;
mod ext;
mod testing;

pub use testing::TestExternalities;

/// Updates to be committed to the state.
pub enum Update {
	/// Set storage of object at given key -- empty is deletion.
	Storage(Vec<u8>, Vec<u8>),
}

// in-memory section of the state.
#[derive(Default, Clone)]
struct MemoryState {
	storage: HashMap<Vec<u8>, Vec<u8>>,
}

impl MemoryState {
	fn storage(&self, key: &[u8]) -> Option<&[u8]> {
		self.storage.get(key).map(|v| &v[..])
	}

	fn set_storage(&mut self, key: Vec<u8>, val: Vec<u8>) {
		self.storage.insert(key, val);
	}

	fn update<I>(&mut self, changes: I) where I: IntoIterator<Item=Update> {
		for update in changes {
			match update {
				Update::Storage(key, val) => {
					if val.is_empty() {
						self.storage.remove(&key);
					} else {
						self.storage.insert(key, val);
					}
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
	fn storage(&self, key: &[u8]) -> Option<&[u8]> {
		self.prospective.storage(key)
			.or_else(|| self.committed.storage(key))
			.and_then(|v| if v.is_empty() { None } else { Some(v) })
	}

	fn set_storage(&mut self, key: Vec<u8>, val: Vec<u8>) {
		self.prospective.set_storage(key, val);
	}

	/// Discard prospective changes to state.
	pub fn discard_prospective(&mut self) {
		self.prospective.storage.clear();
	}

	/// Commit prospective changes to state.
	pub fn commit_prospective(&mut self) {
		let storage_updates = self.prospective.storage.drain()
			.map(|(key, value)| Update::Storage(key, value));

		self.committed.update(storage_updates);
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
pub struct ExternalitiesError;

impl fmt::Display for ExternalitiesError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "Externalities Error") }
}

fn to_keyed_vec(value: u32, mut prepend: Vec<u8>) -> Vec<u8> {
	prepend.extend((0..::std::mem::size_of::<u32>()).into_iter().map(|i| (value >> (i * 8)) as u8));
	prepend
}

/// Externalities: pinned to specific active address.
pub trait Externalities {
	/// Read storage of current contract being called.
	fn storage(&self, key: &[u8]) -> Result<&[u8], ExternalitiesError>;

	/// Set storage of current contract being called (effective immediately).
	fn set_storage(&mut self, key: Vec<u8>, value: Vec<u8>);

	/// Get the identity of the chain.
	fn chain_id(&self) -> u64;

	/// Get the trie root of the current storage map.
	fn storage_root(&self) -> [u8; 32];

	/// Get the current set of authorities from storage.
	fn authorities(&self) -> Result<Vec<&[u8]>, ExternalitiesError> {
		(0..self.storage(b"con:aut:len")?.into_iter()
				.rev()
				.fold(0, |acc, &i| (acc << 8) + (i as u32)))
			.map(|i| self.storage(&to_keyed_vec(i, b"con:aut:".to_vec())))
			.collect()
	}
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
		data: &CallData,
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
	call_data: &CallData,
) -> Result<Vec<u8>, Box<Error>> {

	let result = {
		let mut externalities = ext::Ext {
			backend,
			overlay: &mut *overlay
		};
		// make a copy.
		let code = externalities.storage(b":code").unwrap_or(&[]).to_vec();

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

		overlayed.set_storage(key.clone(), vec![1, 2, 3]);
		assert_eq!(overlayed.storage(&key).unwrap(), &[1, 2, 3]);

		overlayed.commit_prospective();
		assert_eq!(overlayed.storage(&key).unwrap(), &[1, 2, 3]);

		overlayed.set_storage(key.clone(), vec![]);
		assert!(overlayed.storage(&key).is_none());

		overlayed.discard_prospective();
		assert_eq!(overlayed.storage(&key).unwrap(), &[1, 2, 3]);

		overlayed.set_storage(key.clone(), vec![]);
		overlayed.commit_prospective();
		assert!(overlayed.storage(&key).is_none());
	}

	#[test]
	fn authorities_call_works() {
		let mut ext = TestExternalities::default();

		assert_eq!(ext.authorities(), Ok(vec![]));

		ext.set_storage(b"con:aut:len".to_vec(), vec![0u8; 4]);
		assert_eq!(ext.authorities(), Ok(vec![]));

		ext.set_storage(b"con:aut:len".to_vec(), vec![1u8, 0, 0, 0]);
		assert_eq!(ext.authorities(), Ok(vec![&[][..]]));

		ext.set_storage(b"con:aut:\0\0\0\0".to_vec(), b"first".to_vec());
		assert_eq!(ext.authorities(), Ok(vec![&b"first"[..]]));

		ext.set_storage(b"con:aut:len".to_vec(), vec![2u8, 0, 0, 0]);
		ext.set_storage(b"con:aut:\x01\0\0\0".to_vec(), b"second".to_vec());
		assert_eq!(ext.authorities(), Ok(vec![&b"first"[..], &b"second"[..]]));
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
			b"dogglesworth".to_vec() => b"catXXX".to_vec()
		]);
		let mut overlay = OverlayedChanges {
			committed: MemoryState { storage: map![
				b"dog".to_vec() => b"puppy".to_vec(),
				b"dogglesworth".to_vec() => b"catYYY".to_vec()
			], },
			prospective: MemoryState { storage: map![
				b"dogglesworth".to_vec() => b"cat".to_vec()
			], },
		};
		let ext = Ext {
			backend: &mut backend,
			overlay: &mut overlay,
		};
		const ROOT: [u8; 32] = hex!("8aad789dff2f538bca5d8ea56e8abe10f4c7ba3a5dea95fea4cd6e7c3a1168d3");
		assert_eq!(ext.storage_root(), ROOT);
	}
}
