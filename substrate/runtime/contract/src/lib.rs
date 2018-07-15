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
mod exec;
mod vm;

// TODO: Remove this
pub use vm::execute;
pub use vm::Ext;

use exec::ExecutionContext;

use account_db::{AccountDb, OverlayAccountDb};

use double_map::StorageDoubleMap;
use runtime_primitives::traits::{As, RefInto};
use runtime_support::dispatch::Result;
use runtime_support::StorageMap;

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
		// TODO: Gav says it better to be called `call`
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

fn pay_for_gas<T: Trait>(transactor: &T::AccountId, gas_limit: u64, gas_price: u64) -> Result {
	let b = <staking::Module<T>>::free_balance(transactor);
	let cost = gas_limit
		.checked_mul(gas_price)
		.ok_or("overflow multiplying gas limit by price")?;
	let cost = <T::Balance as As<u64>>::sa(cost);
	if b < cost + <staking::Module<T>>::existential_deposit() {
		return Err("not enough funds for transaction fee");
	}
	<staking::Module<T>>::set_free_balance(transactor, b - cost);
	Ok(())
}

fn refund_unused_gas<T: Trait>(transactor: &T::AccountId, gas_left: u64, gas_price: u64) {
	let b = <staking::Module<T>>::free_balance(transactor);
	let refund = gas_left * gas_price;
	let refund = <T::Balance as As<u64>>::sa(refund);
	<staking::Module<T>>::set_free_balance(transactor, b +  refund);
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
		let aux = aux.ref_into();

		// Pay for the gas upfront.
		//
		// NOTE: it is very important to avoid any state changes before
		// paying for the gas.
		pay_for_gas::<T>(aux, gas_limit, gas_price)?;

		let mut overlay = OverlayAccountDb::<T>::new(&account_db::DirectAccountDb);

		let result = {
			let mut ctx = ExecutionContext {
				// TODO: avoid this
				_caller: aux.clone(),
				self_account: aux.clone(),
				gas_price,
				depth: 0,
				account_db: &mut overlay,
			};
			ctx.call(dest, value, gas_limit, data)
		// TODO: Can we return early or we always need to do some finalization steps?
		}?;

		// Refund cost of the unused gas.
		refund_unused_gas::<T>(aux, result.gas_left, gas_price);

		// Commit all changes that made it thus far into the persistant storage.
		account_db::DirectAccountDb.commit(overlay.into_change_set());

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

		let exec_result = {
			let mut ctx = ExecutionContext {
				// TODO: avoid this
				_caller: aux.clone(),
				self_account: aux.clone(),
				gas_price,
				depth: 0,
				account_db: &mut overlay,
			};
			ctx.create(endownment, gas_limit, &ctor_code, &data)
				.map_err(|_| "create failed")
		};

		// TODO: Can we return early or do we always need to do some finalization steps?
		exec_result?;

		account_db::DirectAccountDb.commit(overlay.into_change_set());

		// TODO: finalization: refund `gas_left`.

		Ok(())
	}
}

impl<T: Trait> staking::OnAccountKill<T::AccountId> for Module<T> {
	fn on_account_kill(address: &T::AccountId) {
		<CodeOf<T>>::remove(address);
		<StorageOf<T>>::remove_prefix(address.clone());
	}
}

#[cfg(test)]
mod tests {
	// TODO: Remove `new_test_ext`
	use runtime_io::with_externalities;
	use runtime_support::StorageMap;
	use staking::mock::{new_test_ext, Test};
	use wabt;
	use {CodeOf, ContractAddressFor, Module, Trait};

	pub struct DummyContractAddressFor;
	impl ContractAddressFor<u64> for DummyContractAddressFor {
		fn contract_address_for(_code: &[u8], origin: &u64) -> u64 {
			origin + 1
		}
	}

	// TODO: Define own `Test`.

	impl Trait for Test {
		type DetermineContractAddress2 = DummyContractAddressFor;
	}

	type Contract = Module<Test>;
	type Staking = ::staking::Module<Test>;

	const CODE_TRANSFER: &str = r#"
(module
	;; ext_transfer(transfer_to: u32, transfer_to_len: u32, value_ptr: u32, value_len: u32)
	(import "env" "ext_transfer" (func $ext_transfer (param i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(call $ext_transfer
			(i32.const 4)  ;; Pointer to "Transfer to" address.
			(i32.const 8)  ;; Length of "Transfer to" address.
			(i32.const 12)  ;; Pointer to the buffer with value to transfer
			(i32.const 8)   ;; Length of the buffer with value to transfer.
		)
	)
	;; Destination AccountId to transfer the funds.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 4) "\09\00\00\00\00\00\00\00")
	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 12) "\06\00\00\00\00\00\00\00")
)
"#;

	#[test]
	fn contract_transfer() {
		const CONTRACT_SHOULD_TRANSFER_VALUE: u64 = 6;
		const CONTRACT_SHOULD_TRANSFER_TO: u64 = 9;

		let code_transfer = wabt::wat2wasm(CODE_TRANSFER).unwrap();

		with_externalities(&mut new_test_ext(0, 1, 3, 1, false, 1), || {
			<CodeOf<Test>>::insert(1, code_transfer.to_vec());

			Staking::set_free_balance(&0, 100_000_000);
			Staking::set_free_balance(&1, 11);

			assert_ok!(Contract::send(
				&0,
				1,
				3,
				2,
				100_000,
				Vec::new()
			));

			// TODO: refund
			assert_eq!(
				Staking::free_balance(&0),
				100_000_000 - 200_000 - 3,
			);
			assert_eq!(
				Staking::free_balance(&1),
				11 + 3 - CONTRACT_SHOULD_TRANSFER_VALUE,
			);
			assert_eq!(
				Staking::free_balance(&CONTRACT_SHOULD_TRANSFER_TO),
				CONTRACT_SHOULD_TRANSFER_VALUE,
			);
		});
	}

	/// Convert a byte slice to a string with hex values.
	///
	/// Each value is preceeded with a `\` character.
	fn escaped_bytestring(bytes: &[u8]) -> String {
		use std::fmt::Write;
		let mut result = String::new();
		for b in bytes {
			write!(result, "\\{:02x}", b).unwrap();
		}
		result
	}

	/// Create a constructor for the specified code.
	///
	/// When constructor is executed, it will call `ext_return` with code that
	/// specified in `child_bytecode`.
	fn code_ctor(child_bytecode: &[u8]) -> String {
		format!(
			r#"
(module
	;; ext_return(data_ptr: u32, data_len: u32) -> !
	(import "env" "ext_return" (func $ext_return (param i32 i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(call $ext_return
			(i32.const 4)
			(i32.const {code_len})
		)
		;; ext_return is diverging, i.e. doesn't return.
		unreachable
	)
	(data (i32.const 4) "{escaped_bytecode}")
)
"#,
			escaped_bytecode = escaped_bytestring(child_bytecode),
			code_len = child_bytecode.len(),
		)
	}

	/// Returns code that uses `ext_create` runtime call.
	///
	/// Takes bytecode of the contract that needs to be deployed.
	fn code_create(constructor: &[u8]) -> String {
		format!(
			r#"
(module
	;; ext_create(code_ptr: u32, code_len: u32, value_ptr: u32, value_len: u32)
	(import "env" "ext_create" (func $ext_create (param i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(call $ext_create
			(i32.const 12)   ;; Pointer to `code`
			(i32.const {code_len}) ;; Length of `code`
			(i32.const 4)   ;; Pointer to the buffer with value to transfer
			(i32.const 8)   ;; Length of the buffer with value to transfer
		)
	)
	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 4) "\03\00\00\00\00\00\00\00")
	;; Embedded wasm code.
	(data (i32.const 12) "{escaped_constructor}")
)
"#,
			escaped_constructor = escaped_bytestring(constructor),
			code_len = constructor.len(),
		)
	}

	// TODO: Rename somehow to emphasize this test exercises `ext_create` rather
	// than top level create.
	#[test]
	fn contract_create() {
		let code_transfer = wabt::wat2wasm(CODE_TRANSFER).unwrap();
		let code_ctor_transfer = wabt::wat2wasm(&code_ctor(&code_transfer)).unwrap();
		let code_create = wabt::wat2wasm(&code_create(&code_ctor_transfer)).unwrap();

		with_externalities(&mut new_test_ext(0, 1, 3, 1, false, 1), || {
			Staking::set_free_balance(&0, 100_000_000);
			Staking::set_free_balance(&1, 0);
			Staking::set_free_balance(&9, 30);

			<CodeOf<Test>>::insert(1, code_create.to_vec());

			// When invoked, the contract at address `1` must create a contract with 'transfer' code.
			assert_ok!(Contract::send(&0, 1, 11, 1, 100_000, Vec::new()));

			let derived_address = <Test as Trait>::DetermineContractAddress2::contract_address_for(
				&code_ctor_transfer,
				&1,
			);

			// TODO: refund
			assert_eq!(Staking::free_balance(&0), 100_000_000 - 100_000 - 11);
			assert_eq!(Staking::free_balance(&1), 8);
			assert_eq!(Staking::free_balance(&derived_address), 3);

			// Initiate transfer to the newly created contract.
			assert_ok!(Contract::send(
				&0,
				derived_address,
				11,
				1,
				100_000,
				Vec::new()
			));

			// TODO: refund
			assert_eq!(Staking::free_balance(&0), 100_000_000 - 100_000 - 100_000 - 11 - 11);
			assert_eq!(Staking::free_balance(&derived_address), 8);
			assert_eq!(Staking::free_balance(&9), 36);
		});
	}

	#[test]
	fn top_level_create() {
		let code_transfer = wabt::wat2wasm(CODE_TRANSFER).unwrap();
		let code_ctor_transfer = wabt::wat2wasm(&code_ctor(&code_transfer)).unwrap();

		with_externalities(&mut new_test_ext(0, 1, 3, 1, false, 1), || {
			let derived_address = <Test as Trait>::DetermineContractAddress2::contract_address_for(
				&code_ctor_transfer,
				&0,
			);

			Staking::set_free_balance(&0, 100_000_000);
			Staking::set_free_balance(&derived_address, 30);

			// When invoked, the contract at address `1` must create a contract with 'transfer' code.`
			assert_ok!(Contract::create(
				&0,
				11,
				1,
				100_000,
				code_ctor_transfer.clone(),
				Vec::new()
			));

			// TODO: refund
			assert_eq!(Staking::free_balance(&0), 100_000_000 - 11);
			assert_eq!(Staking::free_balance(&derived_address), 30 + 11);

			assert_eq!(<CodeOf<Test>>::get(&derived_address), code_transfer);
		});
	}


	const CODE_NOP: &'static str =
r#"
(module
	(func (export "call")
		nop
	)
)
"#;

	#[test]
	fn refunds_unused_gas() {
		let code_nop = wabt::wat2wasm(CODE_NOP).unwrap();

		with_externalities(&mut new_test_ext(0, 1, 3, 1, false, 1), || {
			<CodeOf<Test>>::insert(1, code_nop.to_vec());

			Staking::set_free_balance(&0, 100_000_000);

			assert_ok!(Contract::send(
				&0,
				1,
				0,
				2,
				100_000,
				Vec::new(),
			));

			assert_eq!(
				Staking::free_balance(&0),
				100_000_000 - 4,
			);
		});
	}

	#[test]
	fn call_with_zero_value() {
		with_externalities(&mut new_test_ext(0, 1, 3, 1, false, 1), || {
			<CodeOf<Test>>::insert(1, vec![]);

			Staking::set_free_balance(&0, 100_000_000);

			assert_ok!(Contract::send(
				&0,
				1,
				0,
				2,
				100_000,
				Vec::new(),
			));

			// TODO: balance is unchanged after call without value. But is this correct? This means
			// that this transfer is basically free (apart from base transaction fee).
			assert_eq!(
				Staking::free_balance(&0),
				100_000_000,
			);
		});
	}

	#[test]
	fn create_with_zero_endownment() {
		let code_nop = wabt::wat2wasm(CODE_NOP).unwrap();

		with_externalities(&mut new_test_ext(0, 1, 3, 1, false, 1), || {
			Staking::set_free_balance(&0, 100_000_000);

			assert_ok!(Contract::create(
				&0,
				0,
				2,
				100_000,
				code_nop,
				Vec::new(),
			));

			// TODO: balance is unchanged after create without endownment. But is this correct? This means
			// that this transfer is basically free (apart from base transaction fee).
			assert_eq!(
				Staking::free_balance(&0),
				100_000_000,
			);
		});
	}
}
