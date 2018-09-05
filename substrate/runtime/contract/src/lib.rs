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

//! Smart-contract module for runtime; Allows deployment and execution of smart-contracts
//! expressed in WebAssembly.
//!
//! This module provides an ability to create smart-contract accounts and send them messages.
//! A smart-contract is an account with associated code and storage. When such an account receives a message,
//! the code associated with that account gets executed.
//!
//! The code is allowed to alter the storage entries of the associated account,
//! create smart-contracts or send messages to existing smart-contracts.
//!
//! For any actions invoked by the smart-contracts fee must be paid. The fee is paid in gas.
//! Gas is bought upfront up to the, specified in transaction, limit. Any unused gas is refunded
//! after the transaction (regardless of the execution outcome). If all gas is used,
//! then changes made for the specific call or create are reverted (including balance transfers).
//!
//! Failures are typically not cascading. That, for example, means that if contract A calls B and B errors
//! somehow, then A can decide if it should proceed or error.
//!
//! # Interaction with the system
//!
//! ## Finalization
//!
//! This module requires performing some finalization steps at the end of the block. If not performed
//! the module will have incorrect behavior.
//!
//! Call [`Module::execute`] at the end of the block. The order in relation to
//! the other module doesn't matter.
//!
//! ## Account killing
//!
//! When `staking` module determines that account is dead (e.g. account's balance fell below
//! exsistential deposit) then it reaps the account. That will lead to deletion of the associated
//! code and storage of the account.
//!
//! [`Module::execute`]: struct.Module.html#impl-OnFinalise

#![cfg_attr(not(feature = "std"), no_std)]

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

extern crate substrate_runtime_balances as balances;
extern crate substrate_runtime_system as system;

#[macro_use]
extern crate substrate_runtime_support as runtime_support;

extern crate substrate_runtime_primitives as runtime_primitives;
extern crate substrate_primitives;

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

use codec::Codec;
use runtime_primitives::traits::{As, RefInto, SimpleArithmetic, OnFinalise};
use runtime_support::dispatch::Result;
use runtime_support::{Parameter, StorageMap, StorageValue};

pub trait Trait: balances::Trait {
	/// Function type to get the contract address given the creator.
	type DetermineContractAddress: ContractAddressFor<Self::AccountId>;

	// As<u32> is needed for wasm-utils
	type Gas: Parameter + Default + Codec + SimpleArithmetic + Copy + As<Self::Balance> + As<u64> + As<u32>;
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
		) -> Result;

		fn create(
			aux,
			value: T::Balance,
			gas_limit: T::Gas,
			ctor: Vec<u8>,
			data: Vec<u8>
		) -> Result;
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as Contract {
		/// The fee required to create a contract. At least as big as staking's ReclaimRebate.
		ContractFee get(contract_fee): required T::Balance;
		/// The fee charged for a call into a contract.
		CallBaseFee get(call_base_fee): required T::Gas;
		/// The fee charged for a create of a contract.
		CreateBaseFee get(create_base_fee): required T::Gas;
		/// The price of one unit of gas.
		GasPrice get(gas_price): required T::Balance;
		/// The maximum nesting level of a call/create stack.
		MaxDepth get(max_depth): required u32;
		/// The maximum amount of gas that could be expended per block.
		BlockGasLimit get(block_gas_limit): required T::Gas;
		/// Gas spent so far in this block.
		GasSpent get(gas_spent): default T::Gas;

		/// The code associated with an account.
		pub CodeOf: default map [ T::AccountId => Vec<u8> ];	// TODO Vec<u8> values should be optimised to not do a length prefix.
	}
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
	/// Make a call to a specified account, optionally transferring some balance.
	fn call(
		aux: &<T as system::Trait>::PublicAux,
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

		let mut ctx = ExecutionContext {
			self_account: aux.clone(),
			depth: 0,
			overlay: OverlayAccountDb::<T>::new(&account_db::DirectAccountDb),
		};
		let result = ctx.call(aux.clone(), dest, value, &mut gas_meter, &data);

		if let Ok(_) = result {
			// Commit all changes that made it thus far into the persistant storage.
			account_db::DirectAccountDb.commit(ctx.overlay.into_change_set());
		}

		// Refund cost of the unused gas.
		//
		// NOTE: this should go after the commit to the storage, since the storage changes
		// can alter the balance of the caller.
		gas::refund_unused_gas::<T>(aux, gas_meter);

		result.map(|_| ())
	}

	/// Create a new contract, optionally transfering some balance to the created account.
	///
	/// Creation is executed as follows:ExecutionContext
	///
	/// - the destination address is computed based on the sender and hash of the code.
	/// - account is created at the computed address.
	/// - the `ctor_code` is executed in the context of the newly created account. Buffer returned
	///   after the execution is saved as the `code` of the account. That code will be invoked
	///   upon any message received by this account.
	fn create(
		aux: &<T as system::Trait>::PublicAux,
		endowment: T::Balance,
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

		let mut ctx = ExecutionContext {
			self_account: aux.clone(),
			depth: 0,
			overlay: OverlayAccountDb::<T>::new(&account_db::DirectAccountDb),
		};
		let result = ctx.create(aux.clone(), endowment, &mut gas_meter, &ctor_code, &data);

		if let Ok(_) = result {
			// Commit all changes that made it thus far into the persistant storage.
			account_db::DirectAccountDb.commit(ctx.overlay.into_change_set());
		}

		// Refund cost of the unused gas.
		//
		// NOTE: this should go after the commit to the storage, since the storage changes
		// can alter the balance of the caller.
		gas::refund_unused_gas::<T>(aux, gas_meter);

		result.map(|_| ())
	}
}

impl<T: Trait> balances::OnFreeBalanceZero<T::AccountId> for Module<T> {
	fn on_free_balance_zero(who: &T::AccountId) {
		<CodeOf<T>>::remove(who);
		<StorageOf<T>>::remove_prefix(who.clone());
	}
}

/// Finalization hook for the smart-contract module.
impl<T: Trait> OnFinalise<T::BlockNumber> for Module<T> {
	fn on_finalise(_n: T::BlockNumber) {
		<GasSpent<T>>::kill();
	}
}
