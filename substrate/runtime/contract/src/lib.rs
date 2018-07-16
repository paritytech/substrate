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

// TODO: rewrite docs.

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

#[cfg_attr(feature = "std", macro_use)]
extern crate substrate_runtime_std as rstd;

extern crate substrate_runtime_consensus as consensus;
extern crate substrate_runtime_staking as staking;
extern crate substrate_runtime_system as system;

#[cfg(test)]
extern crate substrate_runtime_timestamp as timestamp;
#[cfg(test)]
extern crate substrate_runtime_session as session;

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
mod exec;
mod vm;
mod gas;
mod genesis_config;

#[cfg(test)]
mod tests;

pub use genesis_config::GenesisConfig;
use exec::ExecutionContext;
use account_db::{AccountDb, OverlayAccountDb};
use double_map::StorageDoubleMap;

use codec::Slicable;
use runtime_primitives::traits::{As, RefInto, SimpleArithmetic};
use runtime_support::dispatch::Result;
use runtime_support::{Parameter, StorageMap};

pub trait Trait: system::Trait + staking::Trait + consensus::Trait {
	/// Function type to get the contract address given the creator.
	type DetermineContractAddress: ContractAddressFor<Self::AccountId>;

	// As<u32> is needed for wasm-utils
	type Gas: Parameter + Slicable + SimpleArithmetic + Copy + As<Self::Balance> + As<u64> + As<u32>;
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
		fn call(
			aux,
			dest: T::AccountId,
			value: T::Balance,
			gas_limit: T::Gas,
			data: Vec<u8>
		) -> Result = 0;

		fn create(
			aux,
			value: T::Balance,
			gas_limit: T::Gas,
			ctor: Vec<u8>,
			data: Vec<u8>
		) -> Result = 1;
	}
}

decl_storage! {
	trait Store for Module<T: Trait>;

	// The fee required to create a contract. At least as big as staking ReclaimRebate.
	ContractFee get(contract_fee): b"con:contract_fee" => required T::Balance;
	CallBaseFee get(call_base_fee): b"con:base_call_fee" => required T::Gas;
	CreateBaseFee get(create_base_fee): b"con:base_create_fee" => required T::Gas;
	GasPrice get(gas_price): b"con:gas_price" => required T::Balance;
	MaxDepth get(max_depth): b"con:max_depth" => required u32;

	// The code associated with an account.
	pub CodeOf: b"con:cod:" => default map [ T::AccountId => Vec<u8> ];	// TODO Vec<u8> values should be optimised to not do a length prefix.
}

// TODO: consider storing upper-bound for contract's gas limit in fixed-length runtime
// code in contract itself and use that.

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
	fn call(
		aux: &<T as consensus::Trait>::PublicAux,
		dest: T::AccountId,
		value: T::Balance,
		gas_limit: T::Gas,
		data: Vec<u8>,
	) -> Result {
		let aux = aux.ref_into();

		// Pay for the gas upfront.
		//
		// NOTE: it is very important to avoid any state changes before
		// paying for the gas.
		let mut gas_meter = gas::buy_gas::<T>(aux, gas_limit)?;

		let mut overlay = OverlayAccountDb::<T>::new(&account_db::DirectAccountDb);

		let result = {
			let mut ctx = ExecutionContext {
				self_account: aux.clone(),
				depth: 0,
				account_db: &mut overlay,
			};
			ctx.call(aux.clone(), dest, value, &mut gas_meter, data)
		};

		if let Ok(_) = result {
			// Commit all changes that made it thus far into the persistant storage.
			account_db::DirectAccountDb.commit(overlay.into_change_set());
		}

		// Refund cost of the unused gas.
		//
		// NOTE: this should go after the commit to the storage, since the storage changes
		// can alter the balance of the caller.
		gas::refund_unused_gas::<T>(aux, gas_meter);

		result.map(|_| ())
	}

	fn create(
		aux: &<T as consensus::Trait>::PublicAux,
		endownment: T::Balance,
		gas_limit: T::Gas,
		ctor_code: Vec<u8>,
		data: Vec<u8>,
	) -> Result {
		let aux = aux.ref_into();

		// Pay for the gas upfront.
		//
		// NOTE: it is very important to avoid any state changes before
		// paying for the gas.
		let mut gas_meter = gas::buy_gas::<T>(aux, gas_limit)?;

		let mut overlay = OverlayAccountDb::<T>::new(&account_db::DirectAccountDb);

		let result = {
			let mut ctx = ExecutionContext {
				self_account: aux.clone(),
				depth: 0,
				account_db: &mut overlay,
			};

			ctx.create(aux.clone(), endownment, &mut gas_meter, &ctor_code, &data)
		};

		if let Ok(_) = result {
			// Commit all changes that made it thus far into the persistant storage.
			account_db::DirectAccountDb.commit(overlay.into_change_set());
		}

		// Refund cost of the unused gas.
		//
		// NOTE: this should go after the commit to the storage, since the storage changes
		// can alter the balance of the caller.
		gas::refund_unused_gas::<T>(aux, gas_meter);

		result.map(|_| ())
	}
}

impl<T: Trait> staking::OnAccountKill<T::AccountId> for Module<T> {
	fn on_account_kill(address: &T::AccountId) {
		<CodeOf<T>>::remove(address);
		<StorageOf<T>>::remove_prefix(address.clone());
	}
}
