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

		{
			let mut ctx = ExecutionContext {
				// TODO: avoid this
				_caller: aux.clone(),
				self_account: aux.clone(),
				depth: 0,
				account_db: &mut overlay,
			};
			ctx.call(dest, value, &mut gas_meter, data)?;

			// TODO: Most of the value should be returned even if it is returned an error
		}

		// Commit all changes that made it thus far into the persistant storage.
		account_db::DirectAccountDb.commit(overlay.into_change_set());

		// Refund cost of the unused gas.
		//
		// NOTE: this should go after the commit to the storage, since the storage changes
		// can alter the balance of the caller.
		gas::refund_unused_gas::<T>(aux, gas_meter);

		Ok(())
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

		{
			let mut ctx = ExecutionContext {
				// TODO: avoid this
				_caller: aux.clone(),
				self_account: aux.clone(),
				depth: 0,
				account_db: &mut overlay,
			};
			ctx.create(endownment, &mut gas_meter, &ctor_code, &data)
				.map_err(|_| "create failed")?;

			// TODO: Most of the value should be returned even if it is returned an error
		}

		// Commit all changes that made it thus far into the persistant storage.
		account_db::DirectAccountDb.commit(overlay.into_change_set());

		// Refund cost of the unused gas.
		//
		// NOTE: this should go after the commit to the storage, since the storage changes
		// can alter the balance of the caller.
		gas::refund_unused_gas::<T>(aux, gas_meter);

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
	use {
		StorageOf, CodeOf, ContractAddressFor, Module, Trait,
		GenesisConfig, staking, system, session, consensus, timestamp, runtime_io,
	};
	use runtime_io::with_externalities;
	use runtime_support::StorageMap;
	use runtime_primitives::traits::{HasPublicAux, Identity, BlakeTwo256};
	use runtime_primitives::testing::{Digest, Header, H256};
	use runtime_primitives::BuildStorage;
	use wabt;
	use double_map::StorageDoubleMap;

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	impl HasPublicAux for Test {
		type PublicAux = u64;
	}
	impl consensus::Trait for Test {
		type PublicAux = <Self as HasPublicAux>::PublicAux;
		type SessionKey = u64;
	}
	impl system::Trait for Test {
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Header = Header;
	}
	impl timestamp::Trait for Test {
		const TIMESTAMP_SET_POSITION: u32 = 0;
		type Moment = u64;
	}
	impl staking::Trait for Test {
		type Balance = u64;
		type AccountIndex = u64;
		type OnAccountKill = Contract;
	}
	impl session::Trait for Test {
		type ConvertAccountIdToSessionKey = Identity;
		type OnSessionChange = Staking;
	}
	impl Trait for Test {
		type Gas = u64;
		type DetermineContractAddress = DummyContractAddressFor;
	}

	type Staking = staking::Module<Test>;
	type Contract = Module<Test>;

	pub struct DummyContractAddressFor;
	impl ContractAddressFor<u64> for DummyContractAddressFor {
		fn contract_address_for(_code: &[u8], origin: &u64) -> u64 {
			origin + 1
		}
	}

	fn new_test_ext(existential_deposit: u64, gas_price: u64) -> runtime_io::TestExternalities {
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap();
		t.extend(consensus::GenesisConfig::<Test>{
			code: vec![],
			authorities: vec![],
		}.build_storage().unwrap());
		t.extend(session::GenesisConfig::<Test>{
			session_length: 1,
			validators: vec![10, 20],
			broken_percent_late: 100,
		}.build_storage().unwrap());
		t.extend(staking::GenesisConfig::<Test>{
			sessions_per_era: 1,
			current_era: 0,
			balances: vec![],
			intentions: vec![],
			validator_count: 2,
			bonding_duration: 0,
			transaction_base_fee: 0,
			transaction_byte_fee: 0,
			existential_deposit: existential_deposit,
			transfer_fee: 0,
			creation_fee: 0,
			reclaim_rebate: 0,
			early_era_slash: 0,
			session_reward: 0,
		}.build_storage().unwrap());
		t.extend(timestamp::GenesisConfig::<Test>::default().build_storage().unwrap());
		t.extend(GenesisConfig::<Test> {
			contract_fee: 21,
			call_base_fee: 135,
			create_base_fee: 175,
			gas_price,
		}.build_storage().unwrap());
		t
	}


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

		with_externalities(&mut new_test_ext(0, 2), || {
			<CodeOf<Test>>::insert(1, code_transfer.to_vec());

			Staking::set_free_balance(&0, 100_000_000);
			Staking::set_free_balance(&1, 11);

			assert_ok!(Contract::call(
				&0,
				1,
				3,
				100_000,
				Vec::new()
			));

			assert_eq!(
				Staking::free_balance(&0),
				// 3 - value sent with the transaction
				// 2 * 6 - gas used by the contract (6) multiplied by gas price (2)
				// 2 * 135 - base gas fee for call (by transaction)
				// 2 * 135 - base gas fee for call (by the contract)
				100_000_000 - 3 - (2 * 6) - (2 * 135) - (2 * 135),
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

	#[test]
	fn contract_create() {
		let code_transfer = wabt::wat2wasm(CODE_TRANSFER).unwrap();
		let code_ctor_transfer = wabt::wat2wasm(&code_ctor(&code_transfer)).unwrap();
		let code_create = wabt::wat2wasm(&code_create(&code_ctor_transfer)).unwrap();

		with_externalities(&mut new_test_ext(0, 2), || {
			Staking::set_free_balance(&0, 100_000_000);
			Staking::set_free_balance(&1, 0);
			Staking::set_free_balance(&9, 30);

			<CodeOf<Test>>::insert(1, code_create.to_vec());

			// When invoked, the contract at address `1` must create a contract with 'transfer' code.
			assert_ok!(Contract::call(&0, 1, 11, 100_000, Vec::new()));

			let derived_address = <Test as Trait>::DetermineContractAddress::contract_address_for(
				&code_ctor_transfer,
				&1,
			);

			// 11 - value sent with the transaction
			// 2 * 128 - gas spent by the deployer contract (128) multiplied by gas price (2)
			// 2 * 135 - base gas fee for call (top level)
			// 2 * 175 - base gas fee for create (by contract)
			// ((21 / 2) * 2) - price per account creation
			let expected_gas_after_create = 100_000_000 - 11 - (2 * 128) - (2 * 135) - (2 * 175) - ((21 / 2) * 2);
			assert_eq!(Staking::free_balance(&0), expected_gas_after_create);
			assert_eq!(Staking::free_balance(&1), 8);
			assert_eq!(Staking::free_balance(&derived_address), 3);

			// Initiate transfer to the newly created contract.
			assert_ok!(Contract::call(
				&0,
				derived_address,
				22,
				100_000,
				Vec::new()
			));

			assert_eq!(
				Staking::free_balance(&0),
				// 22 - value sent with the transaction
				// (2 * 6) - gas used by the contract
				// (2 * 135) - base gas fee for call (top level)
				// (2 * 135) - base gas fee for call (by transfer contract)
				expected_gas_after_create - 22 - (2 * 6) - (2 * 135) - (2 * 135),
			);
			assert_eq!(Staking::free_balance(&derived_address), 22 - 3);
			assert_eq!(Staking::free_balance(&9), 36);
		});
	}

	#[test]
	fn top_level_create() {
		let code_transfer = wabt::wat2wasm(CODE_TRANSFER).unwrap();
		let code_ctor_transfer = wabt::wat2wasm(&code_ctor(&code_transfer)).unwrap();

		with_externalities(&mut new_test_ext(0, 3), || {
			let derived_address = <Test as Trait>::DetermineContractAddress::contract_address_for(
				&code_ctor_transfer,
				&0,
			);

			Staking::set_free_balance(&0, 100_000_000);
			Staking::set_free_balance(&derived_address, 30);

			assert_ok!(Contract::create(
				&0,
				11,
				100_000,
				code_ctor_transfer.clone(),
				Vec::new(),
			));

			// 11 - value sent with the transaction
			// (3 * 122) - gas spent by the ctor
			// (3 * 175) - base gas fee for create (175) (top level) multipled by gas price (3)
			// ((21 / 3) * 3) - price for contract creation
			assert_eq!(Staking::free_balance(&0), 100_000_000 - 11 - (3 * 122) - (3 * 175) - ((21 / 3) * 3));
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

		with_externalities(&mut new_test_ext(0, 2), || {
			<CodeOf<Test>>::insert(1, code_nop.to_vec());

			Staking::set_free_balance(&0, 100_000_000);

			assert_ok!(Contract::call(
				&0,
				1,
				0,
				100_000,
				Vec::new(),
			));

			assert_eq!(
				Staking::free_balance(&0),
				100_000_000 - 4 - (2 * 135),
			);
		});
	}

	#[test]
	fn call_with_zero_value() {
		with_externalities(&mut new_test_ext(0, 2), || {
			<CodeOf<Test>>::insert(1, vec![]);

			Staking::set_free_balance(&0, 100_000_000);

			assert_ok!(Contract::call(
				&0,
				1,
				0,
				100_000,
				Vec::new(),
			));

			assert_eq!(
				Staking::free_balance(&0),
				100_000_000 - (2 * 135),
			);
		});
	}

	#[test]
	fn create_with_zero_endownment() {
		let code_nop = wabt::wat2wasm(CODE_NOP).unwrap();

		with_externalities(&mut new_test_ext(0, 2), || {
			Staking::set_free_balance(&0, 100_000_000);

			assert_ok!(Contract::create(
				&0,
				0,
				100_000,
				code_nop,
				Vec::new(),
			));

			// TODO: balance is unchanged after create without endownment. But is this correct? This means
			// that this transfer is basically free (apart from base transaction fee).
			assert_eq!(
				Staking::free_balance(&0),
				// 4 - for the gas spent by the constructor
				// 2 * 175 - base gas fee for create (175) multiplied by gas price (2) (top level)
				100_000_000 - 4 - (2 * 175),
			);
		});
	}

	#[test]
	fn account_removal_removes_storage() {
		with_externalities(&mut new_test_ext(100, 2), || {
			// Setup two accounts with free balance above than exsistential threshold.
			{
				Staking::set_free_balance(&1, 110);
				<StorageOf<Test>>::insert(1, b"foo".to_vec(), b"1".to_vec());
				<StorageOf<Test>>::insert(1, b"bar".to_vec(), b"2".to_vec());

				Staking::set_free_balance(&2, 110);
				<StorageOf<Test>>::insert(2, b"hello".to_vec(), b"3".to_vec());
				<StorageOf<Test>>::insert(2, b"world".to_vec(), b"4".to_vec());
			}

			// Transfer funds from account 1 of such amount that after this transfer
			// the balance of account 1 is will be below than exsistential threshold.
			//
			// This should lead to the removal of all storage associated with this account.
			assert_ok!(Staking::transfer(&1, 2.into(), 20));

			// Verify that all entries from account 1 is removed, while
			// entries from account 2 is in place.
			{
				assert_eq!(<StorageOf<Test>>::get(1, b"foo".to_vec()), None);
				assert_eq!(<StorageOf<Test>>::get(1, b"bar".to_vec()), None);

				assert_eq!(<StorageOf<Test>>::get(2, b"hello".to_vec()), Some(b"3".to_vec()));
				assert_eq!(<StorageOf<Test>>::get(2, b"world".to_vec()), Some(b"4".to_vec()));
			}
		});
	}
}
