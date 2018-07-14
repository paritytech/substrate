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

// TODO: Disable for now
// #![warn(missing_docs)]

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

mod account_db;
mod double_map;
mod vm;
mod exec;

// TODO: Remove this
pub use vm::execute;
pub use vm::Ext;

use exec::ExecutionContext;

use account_db::OverlayAccountDb;

use runtime_primitives::traits::RefInto;
use runtime_support::dispatch::Result;

pub trait Trait: system::Trait + staking::Trait + consensus::Trait {
	// TODO: Rename it from DetermineContractAddress2 to DetermineContractAddress, and clean up
	// the staking module.
	/// Function type to get the contract address given the creator.
	type DetermineContractAddress2: ContractAddressFor<Self::AccountId>;
}

pub trait ContractAddressFor<AccountId: Sized> {
	fn contract_address_for(code: &[u8], origin: &AccountId) -> AccountId;
}

decl_module! {
	/// Contracts module.
	pub struct Module<T: Trait>;

	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	pub enum Call where aux: T::PublicAux {
		// TODO: Change AccountId to staking::Address
		fn send(
			aux,
			dest: T::AccountId,
			value: T::Balance,
			gas_price: u64,
			gas_limit: u64,
			data: Vec<u8>
		) -> Result = 0;

		fn create(
			aux,
			value: T::Balance,
			gas_price: u64,
			gas_limit: u64,
			ctor: Vec<u8>,
			data: Vec<u8>
		) -> Result = 1;
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


impl<T: Trait> Module<T> {
	fn send(
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
		ctx.call(dest, value, gas_limit, data);

		// TODO: commit changes from `overlay` to DirectAccountDb.
		// TODO: finalization: refund `gas_left`.

		Ok(())
	}

	fn create(
		aux: &<T as consensus::Trait>::PublicAux,
		endownment: T::Balance,
		gas_price: u64,
		gas_limit: u64,
		ctor_code: Vec<u8>,
		data: Vec<u8>,
	) -> Result {
		// TODO: an additional fee, based upon gaslimit/gasprice.
		// This fee should be taken in any way and not reverted.

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
		ctx.create(endownment, gas_limit, &ctor_code, &data);

		// TODO: commit changes from `overlay` to DirectAccountDb.
		// TODO: finalization: refund `gas_left`.

		Ok(())
	}
}

// TODO: on removal of an account call:
//
// - <CodeOf<T>>::remove(who);
// - <StorageOf<T>>::remove_prefix(who.clone());
