// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! This module provides a means for executing contracts
//! represented in wasm.

use crate::{
	CodeHash, Schedule, Config,
	wasm::env_def::FunctionImplProvider,
	exec::Ext,
	gas::GasMeter,
};
use sp_std::prelude::*;
use sp_core::crypto::UncheckedFrom;
use codec::{Encode, Decode};

#[macro_use]
mod env_def;
mod code_cache;
mod prepare;
mod runtime;

use self::code_cache::load as load_code;
use pallet_contracts_primitives::ExecResult;

pub use self::code_cache::save as save_code;
#[cfg(feature = "runtime-benchmarks")]
pub use self::code_cache::save_raw as save_code_raw;
pub use self::runtime::{ReturnCode, Runtime, RuntimeToken};

/// A prepared wasm module ready for execution.
#[derive(Clone, Encode, Decode)]
pub struct PrefabWasmModule {
	/// Version of the schedule with which the code was instrumented.
	#[codec(compact)]
	schedule_version: u32,
	#[codec(compact)]
	initial: u32,
	#[codec(compact)]
	maximum: u32,
	/// This field is reserved for future evolution of format.
	///
	/// Basically, for now this field will be serialized as `None`. In the future
	/// we would be able to extend this structure with.
	_reserved: Option<()>,
	/// Code instrumented with the latest schedule.
	code: Vec<u8>,
}

/// Wasm executable loaded by `WasmLoader` and executed by `WasmVm`.
pub struct WasmExecutable {
	entrypoint_name: &'static str,
	prefab_module: PrefabWasmModule,
}

/// Loader which fetches `WasmExecutable` from the code cache.
pub struct WasmLoader<'a, T: Config> {
	schedule: &'a Schedule<T>,
}

impl<'a, T: Config> WasmLoader<'a, T> where T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]> {
	pub fn new(schedule: &'a Schedule<T>) -> Self {
		WasmLoader { schedule }
	}
}

impl<'a, T: Config> crate::exec::Loader<T> for WasmLoader<'a, T>
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>
{
	type Executable = WasmExecutable;

	fn load_init(&self, code_hash: &CodeHash<T>) -> Result<WasmExecutable, &'static str> {
		let prefab_module = load_code::<T>(code_hash, self.schedule)?;
		Ok(WasmExecutable {
			entrypoint_name: "deploy",
			prefab_module,
		})
	}
	fn load_main(&self, code_hash: &CodeHash<T>) -> Result<WasmExecutable, &'static str> {
		let prefab_module = load_code::<T>(code_hash, self.schedule)?;
		Ok(WasmExecutable {
			entrypoint_name: "call",
			prefab_module,
		})
	}
}

/// Implementation of `Vm` that takes `WasmExecutable` and executes it.
pub struct WasmVm<'a, T: Config> where T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]> {
	schedule: &'a Schedule<T>,
}

impl<'a, T: Config> WasmVm<'a, T> where T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]> {
	pub fn new(schedule: &'a Schedule<T>) -> Self {
		WasmVm { schedule }
	}
}

impl<'a, T: Config> crate::exec::Vm<T> for WasmVm<'a, T>
where
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>
{
	type Executable = WasmExecutable;

	fn execute<E: Ext<T = T>>(
		&self,
		exec: &WasmExecutable,
		mut ext: E,
		input_data: Vec<u8>,
		gas_meter: &mut GasMeter<E::T>,
	) -> ExecResult {
		let memory =
			sp_sandbox::Memory::new(exec.prefab_module.initial, Some(exec.prefab_module.maximum))
				.unwrap_or_else(|_| {
				// unlike `.expect`, explicit panic preserves the source location.
				// Needed as we can't use `RUST_BACKTRACE` in here.
					panic!(
						"exec.prefab_module.initial can't be greater than exec.prefab_module.maximum;
						thus Memory::new must not fail;
						qed"
					)
				});

		let mut imports = sp_sandbox::EnvironmentDefinitionBuilder::new();
		imports.add_memory(self::prepare::IMPORT_MODULE_MEMORY, "memory", memory.clone());
		runtime::Env::impls(&mut |name, func_ptr| {
			imports.add_host_func(self::prepare::IMPORT_MODULE_FN, name, func_ptr);
		});

		let mut runtime = Runtime::new(
			&mut ext,
			input_data,
			&self.schedule,
			memory,
			gas_meter,
		);

		// Instantiate the instance from the instrumented module code and invoke the contract
		// entrypoint.
		let result = sp_sandbox::Instance::new(&exec.prefab_module.code, &imports, &mut runtime)
			.and_then(|mut instance| instance.invoke(exec.entrypoint_name, &[], &mut runtime));
		runtime.to_execution_result(result)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		CodeHash, BalanceOf, Error, Module as Contracts,
		exec::{Ext, StorageKey, AccountIdOf},
		gas::{Gas, GasMeter},
		tests::{Test, Call, ALICE, BOB},
		wasm::prepare::prepare_contract,
	};
	use std::collections::HashMap;
	use sp_core::H256;
	use hex_literal::hex;
	use sp_runtime::DispatchError;
	use frame_support::{dispatch::DispatchResult, weights::Weight};
	use assert_matches::assert_matches;
	use pallet_contracts_primitives::{ExecReturnValue, ReturnFlags, ExecError, ErrorOrigin};

	const GAS_LIMIT: Gas = 10_000_000_000;

	#[derive(Debug, PartialEq, Eq)]
	struct DispatchEntry(Call);

	#[derive(Debug, PartialEq, Eq)]
	struct RestoreEntry {
		dest: AccountIdOf<Test>,
		code_hash: H256,
		rent_allowance: u64,
		delta: Vec<StorageKey>,
	}

	#[derive(Debug, PartialEq, Eq)]
	struct InstantiateEntry {
		code_hash: H256,
		endowment: u64,
		data: Vec<u8>,
		gas_left: u64,
		salt: Vec<u8>,
	}

	#[derive(Debug, PartialEq, Eq)]
	struct TerminationEntry {
		beneficiary: AccountIdOf<Test>,
	}

	#[derive(Debug, PartialEq, Eq)]
	struct TransferEntry {
		to: AccountIdOf<Test>,
		value: u64,
		data: Vec<u8>,
	}

	#[derive(Default)]
	pub struct MockExt {
		storage: HashMap<StorageKey, Vec<u8>>,
		rent_allowance: u64,
		instantiates: Vec<InstantiateEntry>,
		terminations: Vec<TerminationEntry>,
		transfers: Vec<TransferEntry>,
		restores: Vec<RestoreEntry>,
		// (topics, data)
		events: Vec<(Vec<H256>, Vec<u8>)>,
	}

	impl Ext for MockExt {
		type T = Test;

		fn get_storage(&self, key: &StorageKey) -> Option<Vec<u8>> {
			self.storage.get(key).cloned()
		}
		fn set_storage(&mut self, key: StorageKey, value: Option<Vec<u8>>) -> DispatchResult {
			*self.storage.entry(key).or_insert(Vec::new()) = value.unwrap_or(Vec::new());
			Ok(())
		}
		fn instantiate(
			&mut self,
			code_hash: &CodeHash<Test>,
			endowment: u64,
			gas_meter: &mut GasMeter<Test>,
			data: Vec<u8>,
			salt: &[u8],
		) -> Result<(AccountIdOf<Self::T>, ExecReturnValue), ExecError> {
			self.instantiates.push(InstantiateEntry {
				code_hash: code_hash.clone(),
				endowment,
				data: data.to_vec(),
				gas_left: gas_meter.gas_left(),
				salt: salt.to_vec(),
			});
			Ok((
				Contracts::<Test>::contract_address(&ALICE, code_hash, salt),
				ExecReturnValue {
					flags: ReturnFlags::empty(),
					data: Vec::new(),
				},
			))
		}
		fn transfer(
			&mut self,
			to: &AccountIdOf<Self::T>,
			value: u64,
		) -> Result<(), DispatchError> {
			self.transfers.push(TransferEntry {
				to: to.clone(),
				value,
				data: Vec::new(),
			});
			Ok(())
		}
		fn call(
			&mut self,
			to: &AccountIdOf<Self::T>,
			value: u64,
			_gas_meter: &mut GasMeter<Test>,
			data: Vec<u8>,
		) -> ExecResult {
			self.transfers.push(TransferEntry {
				to: to.clone(),
				value,
				data: data,
			});
			// Assume for now that it was just a plain transfer.
			// TODO: Add tests for different call outcomes.
			Ok(ExecReturnValue { flags: ReturnFlags::empty(), data: Vec::new() })
		}
		fn terminate(
			&mut self,
			beneficiary: &AccountIdOf<Self::T>,
		) -> Result<(), DispatchError> {
			self.terminations.push(TerminationEntry {
				beneficiary: beneficiary.clone(),
			});
			Ok(())
		}
		fn restore_to(
			&mut self,
			dest: AccountIdOf<Self::T>,
			code_hash: H256,
			rent_allowance: u64,
			delta: Vec<StorageKey>,
		) -> Result<(), DispatchError> {
			self.restores.push(RestoreEntry {
				dest,
				code_hash,
				rent_allowance,
				delta,
			});
			Ok(())
		}
		fn caller(&self) -> &AccountIdOf<Self::T> {
			&ALICE
		}
		fn address(&self) -> &AccountIdOf<Self::T> {
			&BOB
		}
		fn balance(&self) -> u64 {
			228
		}
		fn value_transferred(&self) -> u64 {
			1337
		}

		fn now(&self) -> &u64 {
			&1111
		}

		fn minimum_balance(&self) -> u64 {
			666
		}

		fn tombstone_deposit(&self) -> u64 {
			16
		}

		fn random(&self, subject: &[u8]) -> H256 {
			H256::from_slice(subject)
		}

		fn deposit_event(&mut self, topics: Vec<H256>, data: Vec<u8>) {
			self.events.push((topics, data))
		}

		fn set_rent_allowance(&mut self, rent_allowance: u64) {
			self.rent_allowance = rent_allowance;
		}

		fn rent_allowance(&self) -> u64 {
			self.rent_allowance
		}

		fn block_number(&self) -> u64 { 121 }

		fn max_value_size(&self) -> u32 { 16_384 }

		fn get_weight_price(&self, weight: Weight) -> BalanceOf<Self::T> {
			BalanceOf::<Self::T>::from(1312_u32).saturating_mul(weight.into())
		}
	}

	impl Ext for &mut MockExt {
		type T = <MockExt as Ext>::T;

		fn get_storage(&self, key: &[u8; 32]) -> Option<Vec<u8>> {
			(**self).get_storage(key)
		}
		fn set_storage(&mut self, key: [u8; 32], value: Option<Vec<u8>>) -> DispatchResult {
			(**self).set_storage(key, value)
		}
		fn instantiate(
			&mut self,
			code: &CodeHash<Test>,
			value: u64,
			gas_meter: &mut GasMeter<Test>,
			input_data: Vec<u8>,
			salt: &[u8],
		) -> Result<(AccountIdOf<Self::T>, ExecReturnValue), ExecError> {
			(**self).instantiate(code, value, gas_meter, input_data, salt)
		}
		fn transfer(
			&mut self,
			to: &AccountIdOf<Self::T>,
			value: u64,
		) -> Result<(), DispatchError> {
			(**self).transfer(to, value)
		}
		fn terminate(
			&mut self,
			beneficiary: &AccountIdOf<Self::T>,
		) -> Result<(), DispatchError> {
			(**self).terminate(beneficiary)
		}
		fn call(
			&mut self,
			to: &AccountIdOf<Self::T>,
			value: u64,
			gas_meter: &mut GasMeter<Test>,
			input_data: Vec<u8>,
		) -> ExecResult {
			(**self).call(to, value, gas_meter, input_data)
		}
		fn restore_to(
			&mut self,
			dest: AccountIdOf<Self::T>,
			code_hash: H256,
			rent_allowance: u64,
			delta: Vec<StorageKey>,
		) -> Result<(), DispatchError> {
			(**self).restore_to(
				dest,
				code_hash,
				rent_allowance,
				delta,
			)
		}
		fn caller(&self) -> &AccountIdOf<Self::T> {
			(**self).caller()
		}
		fn address(&self) -> &AccountIdOf<Self::T> {
			(**self).address()
		}
		fn balance(&self) -> u64 {
			(**self).balance()
		}
		fn value_transferred(&self) -> u64 {
			(**self).value_transferred()
		}
		fn now(&self) -> &u64 {
			(**self).now()
		}
		fn minimum_balance(&self) -> u64 {
			(**self).minimum_balance()
		}
		fn tombstone_deposit(&self) -> u64 {
			(**self).tombstone_deposit()
		}
		fn random(&self, subject: &[u8]) -> H256 {
			(**self).random(subject)
		}
		fn deposit_event(&mut self, topics: Vec<H256>, data: Vec<u8>) {
			(**self).deposit_event(topics, data)
		}
		fn set_rent_allowance(&mut self, rent_allowance: u64) {
			(**self).set_rent_allowance(rent_allowance)
		}
		fn rent_allowance(&self) -> u64 {
			(**self).rent_allowance()
		}
		fn block_number(&self) -> u64 {
			(**self).block_number()
		}
		fn max_value_size(&self) -> u32 {
			(**self).max_value_size()
		}
		fn get_weight_price(&self, weight: Weight) -> BalanceOf<Self::T> {
			(**self).get_weight_price(weight)
		}
	}

	fn execute<E: Ext>(
		wat: &str,
		input_data: Vec<u8>,
		ext: E,
		gas_meter: &mut GasMeter<E::T>,
	) -> ExecResult
	where
		<E::T as frame_system::Config>::AccountId:
			UncheckedFrom<<E::T as frame_system::Config>::Hash> + AsRef<[u8]>
	{
		use crate::exec::Vm;

		let wasm = wat::parse_str(wat).unwrap();
		let schedule = crate::Schedule::default();
		let prefab_module =
			prepare_contract::<super::runtime::Env, E::T>(&wasm, &schedule).unwrap();

		let exec = WasmExecutable {
			// Use a "call" convention.
			entrypoint_name: "call",
			prefab_module,
		};

		let cfg = Default::default();
		let vm = WasmVm::new(&cfg);

		vm.execute(&exec, ext, input_data, gas_meter)
	}

	const CODE_TRANSFER: &str = r#"
(module
	;; seal_transfer(
	;;    account_ptr: u32,
	;;    account_len: u32,
	;;    value_ptr: u32,
	;;    value_len: u32,
	;;) -> u32
	(import "seal0" "seal_transfer" (func $seal_transfer (param i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $seal_transfer
				(i32.const 4)  ;; Pointer to "account" address.
				(i32.const 32)  ;; Length of "account" address.
				(i32.const 36) ;; Pointer to the buffer with value to transfer
				(i32.const 8)  ;; Length of the buffer with value to transfer.
			)
		)
	)
	(func (export "deploy"))

	;; Destination AccountId (ALICE)
	(data (i32.const 4)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)

	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 36) "\99\00\00\00\00\00\00\00")
)
"#;

	#[test]
	fn contract_transfer() {
		let mut mock_ext = MockExt::default();
		let _ = execute(
			CODE_TRANSFER,
			vec![],
			&mut mock_ext,
			&mut GasMeter::new(GAS_LIMIT),
		).unwrap();

		assert_eq!(
			&mock_ext.transfers,
			&[TransferEntry {
				to: ALICE,
				value: 153,
				data: Vec::new(),
			}]
		);
	}

	const CODE_CALL: &str = r#"
(module
	;; seal_call(
	;;    callee_ptr: u32,
	;;    callee_len: u32,
	;;    gas: u64,
	;;    value_ptr: u32,
	;;    value_len: u32,
	;;    input_data_ptr: u32,
	;;    input_data_len: u32,
	;;    output_ptr: u32,
	;;    output_len_ptr: u32
	;;) -> u32
	(import "seal0" "seal_call" (func $seal_call (param i32 i32 i64 i32 i32 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $seal_call
				(i32.const 4)  ;; Pointer to "callee" address.
				(i32.const 32)  ;; Length of "callee" address.
				(i64.const 0)  ;; How much gas to devote for the execution. 0 = all.
				(i32.const 36) ;; Pointer to the buffer with value to transfer
				(i32.const 8)  ;; Length of the buffer with value to transfer.
				(i32.const 44) ;; Pointer to input data buffer address
				(i32.const 4)  ;; Length of input data buffer
				(i32.const 4294967295) ;; u32 max value is the sentinel value: do not copy output
				(i32.const 0) ;; Length is ignored in this case
			)
		)
	)
	(func (export "deploy"))

	;; Destination AccountId (ALICE)
	(data (i32.const 4)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)

	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 36) "\06\00\00\00\00\00\00\00")

	(data (i32.const 44) "\01\02\03\04")
)
"#;

	#[test]
	fn contract_call() {
		let mut mock_ext = MockExt::default();
		let _ = execute(
			CODE_CALL,
			vec![],
			&mut mock_ext,
			&mut GasMeter::new(GAS_LIMIT),
		).unwrap();

		assert_eq!(
			&mock_ext.transfers,
			&[TransferEntry {
				to: ALICE,
				value: 6,
				data: vec![1, 2, 3, 4],
			}]
		);
	}

	const CODE_INSTANTIATE: &str = r#"
(module
	;; seal_instantiate(
	;;     code_ptr: u32,
	;;     code_len: u32,
	;;     gas: u64,
	;;     value_ptr: u32,
	;;     value_len: u32,
	;;     input_data_ptr: u32,
	;;     input_data_len: u32,
	;;     input_data_len: u32,
	;;     address_ptr: u32,
	;;     address_len_ptr: u32,
	;;     output_ptr: u32,
	;;     output_len_ptr: u32
	;; ) -> u32
	(import "seal0" "seal_instantiate" (func $seal_instantiate
		(param i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32 i32 i32) (result i32)
	))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $seal_instantiate
				(i32.const 16)   ;; Pointer to `code_hash`
				(i32.const 32)   ;; Length of `code_hash`
				(i64.const 0)    ;; How much gas to devote for the execution. 0 = all.
				(i32.const 4)    ;; Pointer to the buffer with value to transfer
				(i32.const 8)    ;; Length of the buffer with value to transfer
				(i32.const 12)   ;; Pointer to input data buffer address
				(i32.const 4)    ;; Length of input data buffer
				(i32.const 4294967295) ;; u32 max value is the sentinel value: do not copy address
				(i32.const 0) ;; Length is ignored in this case
				(i32.const 4294967295) ;; u32 max value is the sentinel value: do not copy output
				(i32.const 0) ;; Length is ignored in this case
				(i32.const 0) ;; salt_ptr
				(i32.const 4) ;; salt_len
			)
		)
	)
	(func (export "deploy"))

	;; Salt
	(data (i32.const 0) "\42\43\44\45")
	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 4) "\03\00\00\00\00\00\00\00")
	;; Input data to pass to the contract being instantiated.
	(data (i32.const 12) "\01\02\03\04")
	;; Hash of code.
	(data (i32.const 16)
		"\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11"
		"\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11"
	)
)
"#;

	#[test]
	fn contract_instantiate() {
		let mut mock_ext = MockExt::default();
		let _ = execute(
			CODE_INSTANTIATE,
			vec![],
			&mut mock_ext,
			&mut GasMeter::new(GAS_LIMIT),
		).unwrap();

		assert_matches!(
			&mock_ext.instantiates[..],
			[InstantiateEntry {
				code_hash,
				endowment: 3,
				data,
				gas_left: _,
				salt,
			}] if
				code_hash == &[0x11; 32].into() &&
				data == &vec![1, 2, 3, 4] &&
				salt == &vec![0x42, 0x43, 0x44, 0x45]
		);
	}

	const CODE_TERMINATE: &str = r#"
(module
	;; seal_terminate(
	;;     beneficiary_ptr: u32,
	;;     beneficiary_len: u32,
	;; )
	(import "seal0" "seal_terminate" (func $seal_terminate (param i32 i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(call $seal_terminate
			(i32.const 4)  ;; Pointer to "beneficiary" address.
			(i32.const 32)  ;; Length of "beneficiary" address.
		)
	)
	(func (export "deploy"))

	;; Beneficiary AccountId to transfer the funds.
	(data (i32.const 4)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)
)
"#;

	#[test]
	fn contract_terminate() {
		let mut mock_ext = MockExt::default();
		execute(
			CODE_TERMINATE,
			vec![],
			&mut mock_ext,
			&mut GasMeter::new(GAS_LIMIT),
		).unwrap();

		assert_eq!(
			&mock_ext.terminations,
			&[TerminationEntry {
				beneficiary: ALICE,
			}]
		);
	}

	const CODE_TRANSFER_LIMITED_GAS: &str = r#"
(module
	;; seal_call(
	;;    callee_ptr: u32,
	;;    callee_len: u32,
	;;    gas: u64,
	;;    value_ptr: u32,
	;;    value_len: u32,
	;;    input_data_ptr: u32,
	;;    input_data_len: u32,
	;;    output_ptr: u32,
	;;    output_len_ptr: u32
	;;) -> u32
	(import "seal0" "seal_call" (func $seal_call (param i32 i32 i64 i32 i32 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $seal_call
				(i32.const 4)  ;; Pointer to "callee" address.
				(i32.const 32)  ;; Length of "callee" address.
				(i64.const 228)  ;; How much gas to devote for the execution.
				(i32.const 36)  ;; Pointer to the buffer with value to transfer
				(i32.const 8)   ;; Length of the buffer with value to transfer.
				(i32.const 44)   ;; Pointer to input data buffer address
				(i32.const 4)   ;; Length of input data buffer
				(i32.const 4294967295) ;; u32 max value is the sentinel value: do not copy output
				(i32.const 0) ;; Length is ignored in this cas
			)
		)
	)
	(func (export "deploy"))

	;; Destination AccountId to transfer the funds.
	(data (i32.const 4)
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
		"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
	)
	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 36) "\06\00\00\00\00\00\00\00")

	(data (i32.const 44) "\01\02\03\04")
)
"#;

	#[test]
	fn contract_call_limited_gas() {
		let mut mock_ext = MockExt::default();
		let _ = execute(
			&CODE_TRANSFER_LIMITED_GAS,
			vec![],
			&mut mock_ext,
			&mut GasMeter::new(GAS_LIMIT),
		).unwrap();

		assert_eq!(
			&mock_ext.transfers,
			&[TransferEntry {
				to: ALICE,
				value: 6,
				data: vec![1, 2, 3, 4],
			}]
		);
	}

	const CODE_GET_STORAGE: &str = r#"
(module
	(import "seal0" "seal_get_storage" (func $seal_get_storage (param i32 i32 i32) (result i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 32) key for get storage
	(data (i32.const 0)
		"\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11"
		"\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11"
	)

	;; [32, 36) buffer size = 128 bytes
	(data (i32.const 32) "\80")

	;; [36; inf) buffer where the result is copied

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		(local $buf_size i32)

		;; Load a storage value into contract memory.
		(call $assert
			(i32.eq
				(call $seal_get_storage
					(i32.const 0)		;; The pointer to the storage key to fetch
					(i32.const 36)		;; Pointer to the output buffer
					(i32.const 32)		;; Pointer to the size of the buffer
				)

				;; Return value 0 means that the value is found and there were
				;; no errors.
				(i32.const 0)
			)
		)

		;; Find out the size of the buffer
		(set_local $buf_size
			(i32.load (i32.const 32))
		)

		;; Return the contents of the buffer
		(call $seal_return
			(i32.const 0)
			(i32.const 36)
			(get_local $buf_size)
		)

		;; env:seal_return doesn't return, so this is effectively unreachable.
		(unreachable)
	)

	(func (export "deploy"))
)
"#;

	#[test]
	fn get_storage_puts_data_into_buf() {
		let mut mock_ext = MockExt::default();
		mock_ext
			.storage
			.insert([0x11; 32], [0x22; 32].to_vec());

		let output = execute(
			CODE_GET_STORAGE,
			vec![],
			mock_ext,
			&mut GasMeter::new(GAS_LIMIT),
		).unwrap();

		assert_eq!(output, ExecReturnValue { flags: ReturnFlags::empty(), data: [0x22; 32].to_vec() });
	}

	/// calls `seal_caller` and compares the result with the constant 42.
	const CODE_CALLER: &str = r#"
(module
	(import "seal0" "seal_caller" (func $seal_caller (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; fill the buffer with the caller.
		(call $seal_caller (i32.const 0) (i32.const 32))

		;; assert len == 32
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 32)
			)
		)

		;; assert that the first 64 byte are the beginning of "ALICE"
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 0x0101010101010101)
			)
		)
	)

	(func (export "deploy"))
)
"#;

	#[test]
	fn caller() {
		let _ = execute(
			CODE_CALLER,
			vec![],
			MockExt::default(),
			&mut GasMeter::new(GAS_LIMIT),
		).unwrap();
	}

	/// calls `seal_address` and compares the result with the constant 69.
	const CODE_ADDRESS: &str = r#"
(module
	(import "seal0" "seal_address" (func $seal_address (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; fill the buffer with the self address.
		(call $seal_address (i32.const 0) (i32.const 32))

		;; assert size == 32
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 32)
			)
		)

		;; assert that the first 64 byte are the beginning of "BOB"
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 0x0202020202020202)
			)
		)
	)

	(func (export "deploy"))
)
"#;

	#[test]
	fn address() {
		let _ = execute(
			CODE_ADDRESS,
			vec![],
			MockExt::default(),
			&mut GasMeter::new(GAS_LIMIT),
		).unwrap();
	}

	const CODE_BALANCE: &str = r#"
(module
	(import "seal0" "seal_balance" (func $seal_balance (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the balance in the buffer
		(call $seal_balance (i32.const 0) (i32.const 32))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 8)
			)
		)

		;; assert that contents of the buffer is equal to the i64 value of 228.
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 228)
			)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn balance() {
		let mut gas_meter = GasMeter::new(GAS_LIMIT);
		let _ = execute(
			CODE_BALANCE,
			vec![],
			MockExt::default(),
			&mut gas_meter,
		).unwrap();
	}

	const CODE_GAS_PRICE: &str = r#"
(module
	(import "seal0" "seal_weight_to_fee" (func $seal_weight_to_fee (param i64 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the gas price in the buffer
		(call $seal_weight_to_fee (i64.const 2) (i32.const 0) (i32.const 32))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 8)
			)
		)

		;; assert that contents of the buffer is equal to the i64 value of 2 * 1312.
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 2624)
			)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn gas_price() {
		let mut gas_meter = GasMeter::new(GAS_LIMIT);
		let _ = execute(
			CODE_GAS_PRICE,
			vec![],
			MockExt::default(),
			&mut gas_meter,
		).unwrap();
	}

	const CODE_GAS_LEFT: &str = r#"
(module
	(import "seal0" "seal_gas_left" (func $seal_gas_left (param i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the gas left in the buffer
		(call $seal_gas_left (i32.const 0) (i32.const 32))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 8)
			)
		)

		;; return gas left
		(call $seal_return (i32.const 0) (i32.const 0) (i32.const 8))

		(unreachable)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn gas_left() {
		let mut gas_meter = GasMeter::new(GAS_LIMIT);

		let output = execute(
			CODE_GAS_LEFT,
			vec![],
			MockExt::default(),
			&mut gas_meter,
		).unwrap();

		let gas_left = Gas::decode(&mut output.data.as_slice()).unwrap();
		assert!(gas_left < GAS_LIMIT, "gas_left must be less than initial");
		assert!(gas_left > gas_meter.gas_left(), "gas_left must be greater than final");
	}

	const CODE_VALUE_TRANSFERRED: &str = r#"
(module
	(import "seal0" "seal_value_transferred" (func $seal_value_transferred (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the value transferred in the buffer
		(call $seal_value_transferred (i32.const 0) (i32.const 32))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 8)
			)
		)

		;; assert that contents of the buffer is equal to the i64 value of 1337.
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 1337)
			)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn value_transferred() {
		let mut gas_meter = GasMeter::new(GAS_LIMIT);
		let _ = execute(
			CODE_VALUE_TRANSFERRED,
			vec![],
			MockExt::default(),
			&mut gas_meter,
		).unwrap();
	}

	const CODE_RETURN_FROM_START_FN: &str = r#"
(module
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(start $start)
	(func $start
		(call $seal_return
			(i32.const 0)
			(i32.const 8)
			(i32.const 4)
		)
		(unreachable)
	)

	(func (export "call")
		(unreachable)
	)
	(func (export "deploy"))

	(data (i32.const 8) "\01\02\03\04")
)
"#;

	#[test]
	fn return_from_start_fn() {
		let output = execute(
			CODE_RETURN_FROM_START_FN,
			vec![],
			MockExt::default(),
			&mut GasMeter::new(GAS_LIMIT),
		).unwrap();

		assert_eq!(output, ExecReturnValue { flags: ReturnFlags::empty(), data: vec![1, 2, 3, 4] });
	}

	const CODE_TIMESTAMP_NOW: &str = r#"
(module
	(import "seal0" "seal_now" (func $seal_now (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the block timestamp in the buffer
		(call $seal_now (i32.const 0) (i32.const 32))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 8)
			)
		)

		;; assert that contents of the buffer is equal to the i64 value of 1111.
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 1111)
			)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn now() {
		let mut gas_meter = GasMeter::new(GAS_LIMIT);
		let _ = execute(
			CODE_TIMESTAMP_NOW,
			vec![],
			MockExt::default(),
			&mut gas_meter,
		).unwrap();
	}

	const CODE_MINIMUM_BALANCE: &str = r#"
(module
	(import "seal0" "seal_minimum_balance" (func $seal_minimum_balance (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		(call $seal_minimum_balance (i32.const 0) (i32.const 32))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 8)
			)
		)

		;; assert that contents of the buffer is equal to the i64 value of 666.
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 666)
			)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn minimum_balance() {
		let mut gas_meter = GasMeter::new(GAS_LIMIT);
		let _ = execute(
			CODE_MINIMUM_BALANCE,
			vec![],
			MockExt::default(),
			&mut gas_meter,
		).unwrap();
	}

	const CODE_TOMBSTONE_DEPOSIT: &str = r#"
(module
	(import "seal0" "seal_tombstone_deposit" (func $seal_tombstone_deposit (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		(call $seal_tombstone_deposit (i32.const 0) (i32.const 32))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 8)
			)
		)

		;; assert that contents of the buffer is equal to the i64 value of 16.
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 16)
			)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn tombstone_deposit() {
		let mut gas_meter = GasMeter::new(GAS_LIMIT);
		let _ = execute(
			CODE_TOMBSTONE_DEPOSIT,
			vec![],
			MockExt::default(),
			&mut gas_meter,
		).unwrap();
	}

	const CODE_RANDOM: &str = r#"
(module
	(import "seal0" "seal_random" (func $seal_random (param i32 i32 i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0,128) is reserved for the result of PRNG.

	;; the subject used for the PRNG. [128,160)
	(data (i32.const 128)
		"\00\01\02\03\04\05\06\07\08\09\0A\0B\0C\0D\0E\0F"
		"\00\01\02\03\04\05\06\07\08\09\0A\0B\0C\0D\0E\0F"
	)

	;; size of our buffer is 128 bytes
	(data (i32.const 160) "\80")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the block random seed in the buffer
		(call $seal_random
			(i32.const 128) ;; Pointer in memory to the start of the subject buffer
			(i32.const 32) ;; The subject buffer's length
			(i32.const 0) ;; Pointer to the output buffer
			(i32.const 160) ;; Pointer to the output buffer length
		)

		;; assert len == 32
		(call $assert
			(i32.eq
				(i32.load (i32.const 160))
				(i32.const 32)
			)
		)

		;; return the random data
		(call $seal_return
			(i32.const 0)
			(i32.const 0)
			(i32.const 32)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn random() {
		let mut gas_meter = GasMeter::new(GAS_LIMIT);

		let output = execute(
			CODE_RANDOM,
			vec![],
			MockExt::default(),
			&mut gas_meter,
		).unwrap();

		// The mock ext just returns the same data that was passed as the subject.
		assert_eq!(
			output,
			ExecReturnValue {
				flags: ReturnFlags::empty(),
				data: hex!("000102030405060708090A0B0C0D0E0F000102030405060708090A0B0C0D0E0F").to_vec(),
			},
		);
	}

	const CODE_DEPOSIT_EVENT: &str = r#"
(module
	(import "seal0" "seal_deposit_event" (func $seal_deposit_event (param i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call")
		(call $seal_deposit_event
			(i32.const 32) ;; Pointer to the start of topics buffer
			(i32.const 33) ;; The length of the topics buffer.
			(i32.const 8) ;; Pointer to the start of the data buffer
			(i32.const 13) ;; Length of the buffer
		)
	)
	(func (export "deploy"))

	(data (i32.const 8) "\00\01\2A\00\00\00\00\00\00\00\E5\14\00")

	;; Encoded Vec<TopicOf<T>>, the buffer has length of 33 bytes.
	(data (i32.const 32) "\04\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33\33"
	"\33\33\33\33\33\33\33\33\33")
)
"#;

	#[test]
	fn deposit_event() {
		let mut mock_ext = MockExt::default();
		let mut gas_meter = GasMeter::new(GAS_LIMIT);
		let _ = execute(
			CODE_DEPOSIT_EVENT,
			vec![],
			&mut mock_ext,
			&mut gas_meter
		).unwrap();

		assert_eq!(mock_ext.events, vec![
			(vec![H256::repeat_byte(0x33)],
			vec![0x00, 0x01, 0x2a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe5, 0x14, 0x00])
		]);

		assert!(gas_meter.gas_left() > 0);
	}

	const CODE_DEPOSIT_EVENT_MAX_TOPICS: &str = r#"
(module
	(import "seal0" "seal_deposit_event" (func $seal_deposit_event (param i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call")
		(call $seal_deposit_event
			(i32.const 32) ;; Pointer to the start of topics buffer
			(i32.const 161) ;; The length of the topics buffer.
			(i32.const 8) ;; Pointer to the start of the data buffer
			(i32.const 13) ;; Length of the buffer
		)
	)
	(func (export "deploy"))

	(data (i32.const 8) "\00\01\2A\00\00\00\00\00\00\00\E5\14\00")

	;; Encoded Vec<TopicOf<T>>, the buffer has length of 161 bytes.
	(data (i32.const 32) "\14"
"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
"\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02"
"\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03\03"
"\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04"
"\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05\05")
)
"#;

	#[test]
	fn deposit_event_max_topics() {
		// Checks that the runtime traps if there are more than `max_topic_events` topics.
		let mut gas_meter = GasMeter::new(GAS_LIMIT);

		assert_eq!(
			execute(
				CODE_DEPOSIT_EVENT_MAX_TOPICS,
				vec![],
				MockExt::default(),
				&mut gas_meter
			),
			Err(ExecError {
				error: Error::<Test>::TooManyTopics.into(),
				origin: ErrorOrigin::Caller,
			})
		);
	}

	const CODE_DEPOSIT_EVENT_DUPLICATES: &str = r#"
(module
	(import "seal0" "seal_deposit_event" (func $seal_deposit_event (param i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call")
		(call $seal_deposit_event
			(i32.const 32) ;; Pointer to the start of topics buffer
			(i32.const 129) ;; The length of the topics buffer.
			(i32.const 8) ;; Pointer to the start of the data buffer
			(i32.const 13) ;; Length of the buffer
		)
	)
	(func (export "deploy"))

	(data (i32.const 8) "\00\01\2A\00\00\00\00\00\00\00\E5\14\00")

	;; Encoded Vec<TopicOf<T>>, the buffer has length of 129 bytes.
	(data (i32.const 32) "\10"
"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
"\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02\02"
"\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01"
"\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04")
)
"#;

	#[test]
	fn deposit_event_duplicates() {
		// Checks that the runtime traps if there are duplicates.
		let mut gas_meter = GasMeter::new(GAS_LIMIT);

		assert_eq!(
			execute(
				CODE_DEPOSIT_EVENT_DUPLICATES,
				vec![],
				MockExt::default(),
				&mut gas_meter
			),
			Err(ExecError {
				error: Error::<Test>::DuplicateTopics.into(),
				origin: ErrorOrigin::Caller,
			})
		);
	}

	/// calls `seal_block_number` compares the result with the constant 121.
	const CODE_BLOCK_NUMBER: &str = r#"
(module
	(import "seal0" "seal_block_number" (func $seal_block_number (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; size of our buffer is 32 bytes
	(data (i32.const 32) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the block height in the buffer
		(call $seal_block_number (i32.const 0) (i32.const 32))

		;; assert len == 8
		(call $assert
			(i32.eq
				(i32.load (i32.const 32))
				(i32.const 8)
			)
		)

		;; assert that contents of the buffer is equal to the i64 value of 121.
		(call $assert
			(i64.eq
				(i64.load (i32.const 0))
				(i64.const 121)
			)
		)
	)

	(func (export "deploy"))
)
"#;

	#[test]
	fn block_number() {
		let _ = execute(
			CODE_BLOCK_NUMBER,
			vec![],
			MockExt::default(),
			&mut GasMeter::new(GAS_LIMIT),
		).unwrap();
	}

	const CODE_RETURN_WITH_DATA: &str = r#"
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_return" (func $seal_return (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(data (i32.const 32) "\20")

	;; Deploy routine is the same as call.
	(func (export "deploy")
		(call $call)
	)

	;; Call reads the first 4 bytes (LE) as the exit status and returns the rest as output data.
	(func $call (export "call")
		;; Copy input data this contract memory.
		(call $seal_input
			(i32.const 0)	;; Pointer where to store input
			(i32.const 32)	;; Pointer to the length of the buffer
		)

		;; Copy all but the first 4 bytes of the input data as the output data.
		(call $seal_return
			(i32.load (i32.const 0))
			(i32.const 4)
			(i32.sub (i32.load (i32.const 32)) (i32.const 4))
		)
		(unreachable)
	)
)
"#;

	#[test]
	fn seal_return_with_success_status() {
		let output = execute(
			CODE_RETURN_WITH_DATA,
			hex!("00000000445566778899").to_vec(),
			MockExt::default(),
			&mut GasMeter::new(GAS_LIMIT),
		).unwrap();

		assert_eq!(output, ExecReturnValue { flags: ReturnFlags::empty(), data: hex!("445566778899").to_vec() });
		assert!(output.is_success());
	}

	#[test]
	fn return_with_revert_status() {
		let output = execute(
			CODE_RETURN_WITH_DATA,
			hex!("010000005566778899").to_vec(),
			MockExt::default(),
			&mut GasMeter::new(GAS_LIMIT),
		).unwrap();

		assert_eq!(output, ExecReturnValue { flags: ReturnFlags::REVERT, data: hex!("5566778899").to_vec() });
		assert!(!output.is_success());
	}

	const CODE_OUT_OF_BOUNDS_ACCESS: &str = r#"
(module
	(import "seal0" "seal_terminate" (func $seal_terminate (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "deploy"))

	(func (export "call")
		(call $seal_terminate
			(i32.const 65536)  ;; Pointer to "account" address (out of bound).
			(i32.const 8)  ;; Length of "account" address.
		)
	)
)
"#;

	#[test]
	fn contract_out_of_bounds_access() {
		let mut mock_ext = MockExt::default();
		let result = execute(
			CODE_OUT_OF_BOUNDS_ACCESS,
			vec![],
			&mut mock_ext,
			&mut GasMeter::new(GAS_LIMIT),
		);

		assert_eq!(
			result,
			Err(ExecError {
				error: Error::<Test>::OutOfBounds.into(),
				origin: ErrorOrigin::Caller,
			})
		);
	}

	const CODE_DECODE_FAILURE: &str = r#"
(module
	(import "seal0" "seal_terminate" (func $seal_terminate (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "deploy"))

	(func (export "call")
		(call $seal_terminate
			(i32.const 0)  ;; Pointer to "account" address.
			(i32.const 4)  ;; Length of "account" address (too small -> decode fail).
		)
	)
)
"#;

	#[test]
	fn contract_decode_failure() {
		let mut mock_ext = MockExt::default();
		let result = execute(
			CODE_DECODE_FAILURE,
			vec![],
			&mut mock_ext,
			&mut GasMeter::new(GAS_LIMIT),
		);

		assert_eq!(
			result,
			Err(ExecError {
				error: Error::<Test>::DecodingFailed.into(),
				origin: ErrorOrigin::Caller,
			})
		);
	}

}
