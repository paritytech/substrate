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

use std::collections::HashMap;
use std::fmt;

use primitives::Address;
use primitives::contract::{CallData, OutData};
use primitives::hash::H256;

pub mod backend;
mod ext;

/// Updates to be committed to the state.
pub enum Update {
	/// Set storage of address at given key -- empty is deletion.
	Storage(Address, H256, Vec<u8>),
	/// Set code of address -- empty is deletion.
	Code(Address, Vec<u8>),
}

// in-memory section of the state.
#[derive(Default)]
struct MemoryState {
	code: HashMap<Address, Vec<u8>>,
	storage: HashMap<Address, HashMap<H256, Vec<u8>>>,
}

impl MemoryState {
	fn code(&self, address: &Address) -> Option<&[u8]> {
		self.code.get(address).map(|v| &v[..])
	}

	fn storage(&self, address: &Address, key: &H256) -> Option<&[u8]> {
		self.storage.get(address)
			.and_then(|m| m.get(key))
			.map(|v| &v[..])
	}

	#[allow(unused)]
	fn set_code(&mut self, address: Address, code: Vec<u8>) {
		self.code.insert(address, code);
	}

	fn set_storage(&mut self, address: Address, key: H256, val: Vec<u8>) {
		self.storage.entry(address)
			.or_insert_with(HashMap::new)
			.insert(key, val);
	}

	fn update<I>(&mut self, changes: I) where I: IntoIterator<Item=Update> {
		for update in changes {
			match update {
				Update::Storage(addr, key, val) => {
					if val.is_empty() {
						let mut empty = false;
						if let Some(s) = self.storage.get_mut(&addr) {
							s.remove(&key);
							empty = s.is_empty();
						};

						if empty { self.storage.remove(&addr); }
					} else {
						self.storage.entry(addr)
							.or_insert_with(HashMap::new)
							.insert(key, val);
					}
				}
				Update::Code(addr, code) => {
					if code.is_empty() {
						self.code.remove(&addr);
					} else {
						self.code.insert(addr, code);
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
	fn code(&self, address: &Address) -> Option<&[u8]> {
		self.prospective.code(address)
			.or_else(|| self.committed.code(address))
			.and_then(|v| if v.is_empty() { None } else { Some(v) })
	}

	fn storage(&self, address: &Address, key: &H256) -> Option<&[u8]> {
		self.prospective.storage(address, key)
			.or_else(|| self.committed.storage(address, key))
			.and_then(|v| if v.is_empty() { None } else { Some(v) })
	}

	#[allow(unused)]
	fn set_code(&mut self, address: Address, code: Vec<u8>) {
		self.prospective.set_code(address, code);
	}

	fn set_storage(&mut self, address: Address, key: H256, val: Vec<u8>) {
		self.prospective.set_storage(address, key, val);
	}

	/// Discard prospective changes to state.
	pub fn discard_prospective(&mut self) {
		self.prospective.code.clear();
		self.prospective.storage.clear();
	}

	/// Commit prospective changes to state.
	pub fn commit_prospective(&mut self) {
		let code_updates = self.prospective.code.drain()
			.map(|(addr, code)| Update::Code(addr, code));

		let storage_updates = self.prospective.storage.drain()
			.flat_map(|(addr, storages)| storages.into_iter().map(move |(k, v)| (addr, k, v)))
			.map(|(addr, key, value)| Update::Storage(addr, key, value));

		self.committed.update(code_updates.chain(storage_updates));
	}
}

/// State Machine Error bound.
///
/// This should reflect WASM error type bound for future compatibility.
pub trait Error: 'static + fmt::Debug + fmt::Display + Send {}
impl<E> Error for E where E: 'static + fmt::Debug + fmt::Display + Send {}

/// Externalities: pinned to specific active address.
pub trait Externalities<CodeExecutor>: StaticExternalities<CodeExecutor> {
	/// Read storage of current contract being called.
	fn storage(&self, key: &H256) -> Result<&[u8], Self::Error> {
		StaticExternalities::storage(self, key)
	}

	/// Set storage of current contract being called.
	fn set_storage(&mut self, key: H256, value: Vec<u8>);

	/// Make a sub-call to another contract.
	fn call(&mut self, address: &Address, method: &str, data: &CallData) -> Result<OutData, Self::Error>;

	/// Make a static (read-only) call to another contract.
	fn call_static(&self, address: &Address, method: &str, data: &CallData) -> Result<OutData, Self::Error> {
		StaticExternalities::call_static(self, address, method, data)
	}
}

/// Static externalities: used only for read-only requests.
pub trait StaticExternalities<CodeExecutor> {
	/// Externalities error type.
	type Error: Error;

	/// Read storage of current contract being called.
	fn storage(&self, key: &H256) -> Result<&[u8], Self::Error>;

	/// Make a static (read-only) call to another contract.
	fn call_static(&self, address: &Address, method: &str, data: &CallData) -> Result<OutData, Self::Error>;
}

/// Contract code executor.
pub trait CodeExecutor: Sized {
	/// Error type for contract execution.
	type Error: Error;

	/// Execute a contract in read-only mode.
	/// The execution is not allowed to modify the state.
	fn call_static<E: StaticExternalities<Self>>(
		&self,
		ext: &E,
		code: &[u8],
		method: &str,
		data: &CallData,
	) -> Result<OutData, Self::Error>;

	/// Execute a contract.
	fn call<E: Externalities<Self>>(
		&self,
		ext: &mut E,
		code: &[u8],
		method: &str,
		data: &CallData,
	) -> Result<OutData, Self::Error>;
}

/// Execute a call using the given state backend, overlayed changes, and call executor.
///
/// On an error, no prospective changes are written to the overlay.
pub fn execute<B: backend::Backend, Exec: CodeExecutor>(
	backend: &B,
	overlay: &mut OverlayedChanges,
	exec: &Exec,
	address: &Address,
	method: &str,
	call_data: &CallData,
) -> Result<OutData, Box<Error>> {
	let code = match overlay.code(address) {
		Some(x) => x.to_owned(),
		None => backend.code(address).map_err(|e| Box::new(e) as _)?.to_owned(),
	};

	let result = {
		let mut externalities = ext::Ext {
			backend,
			exec,
			overlay: &mut *overlay,
			local: *address,
		};

		exec.call(
			&mut externalities,
			&code[..],
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

	use primitives::hash::H256;
	use primitives::Address;

	#[test]
	fn overlayed_storage_works() {
		let mut overlayed = OverlayedChanges::default();

		let key = H256::random();
		let addr = Address::random();

		assert!(overlayed.storage(&addr, &key).is_none());

		overlayed.set_storage(addr, key, vec![1, 2, 3]);
		assert_eq!(overlayed.storage(&addr, &key).unwrap(), &[1, 2, 3]);

		overlayed.commit_prospective();
		assert_eq!(overlayed.storage(&addr, &key).unwrap(), &[1, 2, 3]);

		overlayed.set_storage(addr, key, vec![]);
		assert!(overlayed.storage(&addr, &key).is_none());

		overlayed.discard_prospective();
		assert_eq!(overlayed.storage(&addr, &key).unwrap(), &[1, 2, 3]);

		overlayed.set_storage(addr, key, vec![]);
		overlayed.commit_prospective();
		assert!(overlayed.storage(&addr, &key).is_none());
	}

	#[test]
	fn overlayed_code_works() {
		let mut overlayed = OverlayedChanges::default();

		let addr = Address::random();

		assert!(overlayed.code(&addr).is_none());

		overlayed.set_code(addr, vec![1, 2, 3]);
		assert_eq!(overlayed.code(&addr).unwrap(), &[1, 2, 3]);

		overlayed.commit_prospective();
		assert_eq!(overlayed.code(&addr).unwrap(), &[1, 2, 3]);

		overlayed.set_code(addr, vec![]);
		assert!(overlayed.code(&addr).is_none());

		overlayed.discard_prospective();
		assert_eq!(overlayed.code(&addr).unwrap(), &[1, 2, 3]);

		overlayed.set_code(addr, vec![]);
		overlayed.commit_prospective();
		assert!(overlayed.code(&addr).is_none());
	}
}
