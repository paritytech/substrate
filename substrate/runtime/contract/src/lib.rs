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

extern crate substrate_codec as codec;
extern crate substrate_runtime_io as runtime_io;
extern crate substrate_runtime_sandbox as sandbox;
extern crate substrate_runtime_std as rstd;

extern crate substrate_runtime_consensus as consensus;
extern crate substrate_runtime_staking as staking;
extern crate substrate_runtime_system as system;

#[macro_use]
extern crate substrate_runtime_support as runtime_support;

extern crate substrate_runtime_primitives as runtime_primitives;

#[cfg(test)]
#[macro_use]
extern crate assert_matches;

#[cfg(test)]
extern crate wabt;

mod double_map;
mod vm;
mod account_db;

// TODO: Remove this
pub use vm::execute;
pub use vm::Ext;

use double_map::StorageDoubleMap;
use account_db::{AccountDb, OverlayAccountDb};

use runtime_support::StorageMap;
use runtime_primitives::traits::{MaybeEmpty, RefInto};
use runtime_support::dispatch::Result;

use rstd::collections::btree_map::{BTreeMap, Entry};

pub trait Trait: system::Trait + staking::Trait + consensus::Trait {}

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

struct TransactionData {
	// tx_origin
	// tx_gas_price
	// block_number
	// timestamp
	// etc
}

struct ExecutionContext<'a, T: Trait + 'a> {
	// aux for the first transaction.
	_caller: T::AccountId,
	// typically should be dest
	self_account: T::AccountId,
	account_db: &'a mut OverlayAccountDb<'a, T>,
	gas_price: u64,
	depth: usize,
}

impl<'a, T: Trait> ExecutionContext<'a, T> {
	/// Make a call to the specified address.
	fn call(
		&mut self,
		dest: T::AccountId,
		value: T::Balance,
		gas_limit: u64,
		data: Vec<u8>,
	) -> Result {
		let dest_code = <CodeOf<T>>::get(&dest);

		let mut overlay = OverlayAccountDb::new(self.account_db);

		// TODO: transfer value using `overlay`. Return an error if failed.

		if !dest_code.is_empty() {
			let mut nested = ExecutionContext {
				account_db: &mut overlay,
				_caller: self.self_account.clone(),
				self_account: dest.clone(),
				gas_price: self.gas_price,
				depth: self.depth + 1,
			};

			vm::execute(&dest_code, &mut nested, gas_limit).unwrap();
		}

		Ok(())
	}

	// TODO: fn create
}

impl<'a, T: Trait + 'a> vm::Ext for ExecutionContext<'a, T> {
	type AccountId = T::AccountId;
	type Balance = T::Balance;

	fn get_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.account_db.get_storage(&self.self_account, key)
	}

	fn set_storage(&mut self, key: &[u8], value: Option<Vec<u8>>) {
		self.account_db.set_storage(&self.self_account, key.to_vec(), value)
	}

	fn create(&mut self, code: &[u8], value: Self::Balance) {
		panic!()
	}

	fn call(&mut self, to: &Self::AccountId, value: Self::Balance) {
		// TODO: Pass these thru parameters
		let mut gas_limit = 100_000;
		let data = Vec::new();

		let result = self.call(
			to.clone(),
			value,
			gas_limit,
			data,
		);
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
		// This fee should be taken in any way and not reverted.

		// TODO: consider storing upper-bound for contract's gas limit in fixed-length runtime
		// code in contract itself and use that.

		let aux = aux.ref_into();

		let mut overlay = OverlayAccountDb::<T>::new(&account_db::DirectAccountDb);

		let mut ctx = ExecutionContext {
			// TODO: fuck
			_caller: aux.clone(),
			self_account: aux.clone(),
			gas_price,
			depth: 0,
			account_db: &mut overlay,
		};

		ctx.call(
			dest,
			value,
			gas_limit,
			data,
		);

		// TODO: commit changes from `overlay` to DirectAccountDb.
		// TODO: finalization: refund `gas_left`.

		Ok(())
	}
}

// TODO: on removal of an account call:
//
// - <CodeOf<T>>::remove(who);
// - <StorageOf<T>>::remove_prefix(who.clone());
