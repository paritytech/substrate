// Copyright 2018 Parity Technologies (UK) Ltd.
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
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

//! Crate for executing smart-contracts.
//!
//! It provides an means for executing contracts represented in WebAssembly (Wasm for short).
//! Contracts are able to create other contracts, transfer funds to each other and operate on a simple key-value storage.

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

#[cfg(feature = "std")]
#[macro_use]
extern crate serde_derive;

#[cfg(feature = "std")]
extern crate serde;

extern crate parity_wasm;
extern crate pwasm_utils;

extern crate substrate_runtime_io as runtime_io;
extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_sandbox as sandbox;
extern crate substrate_codec as codec;

extern crate substrate_runtime_system as system;
extern crate substrate_runtime_staking as staking;
extern crate substrate_runtime_consensus as consensus;

#[macro_use]
extern crate substrate_runtime_support as runtime_support;

extern crate substrate_runtime_primitives as runtime_primitives;

#[cfg(test)]
#[macro_use]
extern crate assert_matches;

#[cfg(test)]
extern crate wabt;

mod vm;
mod double_map;

// TODO: Remove this
pub use vm::Ext;
pub use vm::execute;

use runtime_support::dispatch::Result;
use runtime_primitives::traits::{RefInto, MaybeEmpty};

use rstd::collections::btree_map::{BTreeMap, Entry};

pub trait Trait: system::Trait + staking::Trait + consensus::Trait {
}

decl_module! {
	/// Contracts module.
	pub struct Module<T: Trait>;

	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum Call where aux: T::PublicAux {
		// TODO: Change AccountId to staking::Address
		fn transact(
			aux,
			dest: T::AccountId,
			value: T::Balance,
			gas_price: u64,
			gas_limit: u64,
			data: Vec<u8>
		) -> Result = 0;
	}
}

decl_storage! {
	trait Store for Module<T: Trait>;

	// The code associated with an account.
	pub CodeOf: b"con:cod:" => default map [ T::AccountId => Vec<u8> ];	// TODO Vec<u8> values should be optimised to not do a length prefix.
}

/// The storage items associated with an account/key.
///
/// TODO: keys should also be able to take AsRef<KeyType> to ensure Vec<u8>s can be passed as &[u8]
pub(crate) struct StorageOf<T>(::rstd::marker::PhantomData<T>);
impl<T: Trait> double_map::StorageDoubleMap for StorageOf<T> {
	const PREFIX: &'static [u8] = b"con:sto:";
	type Key1 = T::AccountId;
	type Key2 = Vec<u8>;
	type Value = Vec<u8>;
}

struct ExecutionContext<T: Trait> {
	_marker: ::rstd::marker::PhantomData<T>,
	gas_price: u64,
}

impl<T: Trait> ExecutionContext<T> {
	/// Make a call to the specified address.
	fn call(
		&mut self,
		dest: T::AccountId,
		value: T::Balance,
		gas_price: u64,
		gas_limit: u64,
		data: Vec<u8>,
	) {

	}
}

/// Call externalities provide an interface for the VM
/// to interact with and query the state.
///
/// Should be able to create `ExecutionContext` since it can be used for nested
/// calls.
struct CallExternalities<T: Trait> {
	self_account_id: T::AccountId,
	_marker: ::rstd::marker::PhantomData<T>,
}

impl<T: Trait> Ext for CallExternalities<T> {
	type AccountId = T::AccountId;
	type Balance = T::Balance;

	fn get_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		panic!()
	}

	/// Sets the storage entry by the given key to the specified value.
	fn set_storage(&mut self, key: &[u8], value: Option<Vec<u8>>) {
		panic!()
	}

	fn create(&mut self, code: &[u8], value: Self::Balance) {
		panic!()
	}

	fn call(&mut self, to: &Self::AccountId, value: Self::Balance) {
		// TODO: check call depth.
		// TODO: calculate how much gas is available
		panic!()
	}
}

struct Account {
	code: Option<Vec<u8>>,
	storage: BTreeMap<Vec<u8>, Vec<u8>>,
	
}

struct AccountDb<T: Trait> {
	/// Current world state view.
	///
	/// If the account db is flushed, then all entries will be
	/// written into the db.
	world_state: BTreeMap<T::AccountId, Account>,

	///
	backups: Vec<BTreeMap<T::AccountId, Account>>,
}

impl<T: Trait> AccountDb<T> {
	fn new() -> AccountDb<T> {
		AccountDb {
			world_state: BTreeMap::new(),
			backups: Vec::new(),
		}
	}

	fn flush(self) {

	}
}

impl<T: Trait> Module<T> {
	fn transact(
		aux: &<T as consensus::Trait>::PublicAux,
		dest: T::AccountId,
		value: T::Balance,
		gas_price: u64,
		gas_limit: u64,
		data: Vec<u8>,
	) -> Result {
		// TODO: an additional fee, based upon gaslimit/gasprice.

		// TODO: consider storing upper-bound for contract's gas limit in fixed-length runtime
		// code in contract itself and use that.

		// TODO: Get code and runtime::execute it.

		let account_db = AccountDb::new();


		Ok(())
	}
}

// TODO: on removal of an account call:
//
// - <CodeOf<T>>::remove(who);
// - <StorageOf<T>>::remove_prefix(who.clone());
