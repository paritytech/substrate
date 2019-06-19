// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! This module provides a means for executing contracts
//! represented in wasm.

use crate::{CodeHash, Schedule, Trait};
use crate::wasm::env_def::FunctionImplProvider;
use crate::exec::{Ext, EmptyOutputBuf, VmExecResult};
use crate::gas::GasMeter;

use rstd::prelude::*;
use parity_codec::{Encode, Decode};
use sandbox;

#[macro_use]
mod env_def;
mod code_cache;
mod prepare;
mod runtime;

use self::runtime::{to_execution_result, Runtime};
use self::code_cache::load as load_code;

pub use self::code_cache::save as save_code;

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
	entrypoint_name: &'static [u8],
	prefab_module: PrefabWasmModule,
}

/// Loader which fetches `WasmExecutable` from the code cache.
pub struct WasmLoader<'a, T: Trait> {
	schedule: &'a Schedule<T::Gas>,
}

impl<'a, T: Trait> WasmLoader<'a, T> {
	pub fn new(schedule: &'a Schedule<T::Gas>) -> Self {
		WasmLoader { schedule }
	}
}

impl<'a, T: Trait> crate::exec::Loader<T> for WasmLoader<'a, T> {
	type Executable = WasmExecutable;

	fn load_init(&self, code_hash: &CodeHash<T>) -> Result<WasmExecutable, &'static str> {
		let prefab_module = load_code::<T>(code_hash, self.schedule)?;
		Ok(WasmExecutable {
			entrypoint_name: b"deploy",
			prefab_module,
		})
	}
	fn load_main(&self, code_hash: &CodeHash<T>) -> Result<WasmExecutable, &'static str> {
		let prefab_module = load_code::<T>(code_hash, self.schedule)?;
		Ok(WasmExecutable {
			entrypoint_name: b"call",
			prefab_module,
		})
	}
}

/// Implementation of `Vm` that takes `WasmExecutable` and executes it.
pub struct WasmVm<'a, T: Trait> {
	schedule: &'a Schedule<T::Gas>,
}

impl<'a, T: Trait> WasmVm<'a, T> {
	pub fn new(schedule: &'a Schedule<T::Gas>) -> Self {
		WasmVm { schedule }
	}
}

impl<'a, T: Trait> crate::exec::Vm<T> for WasmVm<'a, T> {
	type Executable = WasmExecutable;

	fn execute<E: Ext<T = T>>(
		&self,
		exec: &WasmExecutable,
		ext: &mut E,
		input_data: &[u8],
		empty_output_buf: EmptyOutputBuf,
		gas_meter: &mut GasMeter<E::T>,
	) -> VmExecResult {
		let memory =
			sandbox::Memory::new(exec.prefab_module.initial, Some(exec.prefab_module.maximum))
				.unwrap_or_else(|_| {
				// unlike `.expect`, explicit panic preserves the source location.
				// Needed as we can't use `RUST_BACKTRACE` in here.
					panic!(
						"exec.prefab_module.initial can't be greater than exec.prefab_module.maximum;
						thus Memory::new must not fail;
						qed"
					)
				});

		let mut imports = sandbox::EnvironmentDefinitionBuilder::new();
		imports.add_memory("env", "memory", memory.clone());
		runtime::Env::impls(&mut |name, func_ptr| {
			imports.add_host_func("env", name, func_ptr);
		});

		let mut runtime = Runtime::new(
			ext,
			input_data,
			empty_output_buf,
			&self.schedule,
			memory,
			gas_meter,
		);

		// Instantiate the instance from the instrumented module code.
		match sandbox::Instance::new(&exec.prefab_module.code, &imports, &mut runtime) {
			// No errors or traps were generated on instantiation! That
			// means we can now invoke the contract entrypoint.
			Ok(mut instance) => {
				let err = instance
					.invoke(exec.entrypoint_name, &[], &mut runtime)
					.err();
				to_execution_result(runtime, err)
			}
			// `start` function trapped. Treat it in the same manner as an execution error.
			Err(err @ sandbox::Error::Execution) => to_execution_result(runtime, Some(err)),
			Err(_err @ sandbox::Error::Module) => {
				// `Error::Module` is returned only if instantiation or linking failed (i.e.
				// wasm binary tried to import a function that is not provided by the host).
				// This shouldn't happen because validation process ought to reject such binaries.
				//
				// Because panics are really undesirable in the runtime code, we treat this as
				// a trap for now. Eventually, we might want to revisit this.
				return VmExecResult::Trap("validation error");
			}
			// Other instantiation errors.
			// Return without executing anything.
			Err(_) => return VmExecResult::Trap("during start function"),
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::collections::HashMap;
	use substrate_primitives::H256;
	use crate::exec::{CallReceipt, Ext, InstantiateReceipt, EmptyOutputBuf, StorageKey};
	use crate::gas::GasMeter;
	use crate::tests::{Test, Call};
	use crate::wasm::prepare::prepare_contract;
	use crate::CodeHash;
	use wabt;
	use hex_literal::hex;

	#[derive(Debug, PartialEq, Eq)]
	struct DispatchEntry(Call);
	#[derive(Debug, PartialEq, Eq)]
	struct CreateEntry {
		code_hash: H256,
		endowment: u64,
		data: Vec<u8>,
		gas_left: u64,
	}
	#[derive(Debug, PartialEq, Eq)]
	struct TransferEntry {
		to: u64,
		value: u64,
		data: Vec<u8>,
		gas_left: u64,
	}
	#[derive(Default)]
	pub struct MockExt {
		storage: HashMap<StorageKey, Vec<u8>>,
		rent_allowance: u64,
		creates: Vec<CreateEntry>,
		transfers: Vec<TransferEntry>,
		dispatches: Vec<DispatchEntry>,
		// (topics, data)
		events: Vec<(Vec<H256>, Vec<u8>)>,
		next_account_id: u64,
	}
	impl Ext for MockExt {
		type T = Test;

		fn get_storage(&self, key: &StorageKey) -> Option<Vec<u8>> {
			self.storage.get(key).cloned()
		}
		fn set_storage(&mut self, key: StorageKey, value: Option<Vec<u8>>) {
			*self.storage.entry(key).or_insert(Vec::new()) = value.unwrap_or(Vec::new());
		}
		fn instantiate(
			&mut self,
			code_hash: &CodeHash<Test>,
			endowment: u64,
			gas_meter: &mut GasMeter<Test>,
			data: &[u8],
		) -> Result<InstantiateReceipt<u64>, &'static str> {
			self.creates.push(CreateEntry {
				code_hash: code_hash.clone(),
				endowment,
				data: data.to_vec(),
				gas_left: gas_meter.gas_left(),
			});
			let address = self.next_account_id;
			self.next_account_id += 1;

			Ok(InstantiateReceipt { address })
		}
		fn call(
			&mut self,
			to: &u64,
			value: u64,
			gas_meter: &mut GasMeter<Test>,
			data: &[u8],
			_output_data: EmptyOutputBuf,
		) -> Result<CallReceipt, &'static str> {
			self.transfers.push(TransferEntry {
				to: *to,
				value,
				data: data.to_vec(),
				gas_left: gas_meter.gas_left(),
			});
			// Assume for now that it was just a plain transfer.
			// TODO: Add tests for different call outcomes.
			Ok(CallReceipt {
				output_data: Vec::new(),
			})
		}
		fn note_dispatch_call(&mut self, call: Call) {
			self.dispatches.push(DispatchEntry(call));
		}
		fn caller(&self) -> &u64 {
			&42
		}
		fn address(&self) -> &u64 {
			&69
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
	}

	fn execute<E: Ext>(
		wat: &str,
		input_data: &[u8],
		output_data: &mut Vec<u8>,
		ext: &mut E,
		gas_meter: &mut GasMeter<E::T>,
	) -> Result<(), &'static str> {
		use crate::exec::Vm;

		let wasm = wabt::wat2wasm(wat).unwrap();
		let schedule = crate::Schedule::<u64>::default();
		let prefab_module =
			prepare_contract::<Test, super::runtime::Env>(&wasm, &schedule).unwrap();

		let exec = WasmExecutable {
			// Use a "call" convention.
			entrypoint_name: b"call",
			prefab_module,
		};

		let cfg = Default::default();
		let vm = WasmVm::new(&cfg);

		*output_data = vm
			.execute(&exec, ext, input_data, EmptyOutputBuf::new(), gas_meter)
			.into_result()?;

		Ok(())
	}

	const CODE_TRANSFER: &str = r#"
(module
	;; ext_call(
	;;    callee_ptr: u32,
	;;    callee_len: u32,
	;;    gas: u64,
	;;    value_ptr: u32,
	;;    value_len: u32,
	;;    input_data_ptr: u32,
	;;    input_data_len: u32
	;;) -> u32
	(import "env" "ext_call" (func $ext_call (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $ext_call
				(i32.const 4)  ;; Pointer to "callee" address.
				(i32.const 8)  ;; Length of "callee" address.
				(i64.const 0)  ;; How much gas to devote for the execution. 0 = all.
				(i32.const 12) ;; Pointer to the buffer with value to transfer
				(i32.const 8)  ;; Length of the buffer with value to transfer.
				(i32.const 20) ;; Pointer to input data buffer address
				(i32.const 4)  ;; Length of input data buffer
			)
		)
	)
	(func (export "deploy"))

	;; Destination AccountId to transfer the funds.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 4) "\09\00\00\00\00\00\00\00")
	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 12) "\06\00\00\00\00\00\00\00")

	(data (i32.const 20) "\01\02\03\04")
)
"#;

	#[test]
	fn contract_transfer() {
		let mut mock_ext = MockExt::default();
		execute(
			CODE_TRANSFER,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&mut GasMeter::with_limit(50_000, 1),
		)
		.unwrap();

		assert_eq!(
			&mock_ext.transfers,
			&[TransferEntry {
				to: 9,
				value: 6,
				data: vec![1, 2, 3, 4],
				gas_left: 49970,
			}]
		);
	}

	const CODE_CREATE: &str = r#"
(module
	;; ext_create(
	;;     code_ptr: u32,
	;;     code_len: u32,
	;;     gas: u64,
	;;     value_ptr: u32,
	;;     value_len: u32,
	;;     input_data_ptr: u32,
	;;     input_data_len: u32,
	;; ) -> u32
	(import "env" "ext_create" (func $ext_create (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $ext_create
				(i32.const 16)   ;; Pointer to `code_hash`
				(i32.const 32)   ;; Length of `code_hash`
				(i64.const 0)    ;; How much gas to devote for the execution. 0 = all.
				(i32.const 4)    ;; Pointer to the buffer with value to transfer
				(i32.const 8)    ;; Length of the buffer with value to transfer
				(i32.const 12)   ;; Pointer to input data buffer address
				(i32.const 4)    ;; Length of input data buffer
			)
		)
	)
	(func (export "deploy"))

	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 4) "\03\00\00\00\00\00\00\00")
	;; Input data to pass to the contract being created.
	(data (i32.const 12) "\01\02\03\04")
	;; Hash of code.
	(data (i32.const 16)
		"\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11"
		"\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11"
	)
)
"#;

	#[test]
	fn contract_create() {
		let mut mock_ext = MockExt::default();
		execute(
			CODE_CREATE,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&mut GasMeter::with_limit(50_000, 1),
		)
		.unwrap();

		assert_eq!(
			&mock_ext.creates,
			&[CreateEntry {
				code_hash: [0x11; 32].into(),
				endowment: 3,
				data: vec![1, 2, 3, 4],
				gas_left: 49946,
			}]
		);
	}

	const CODE_TRANSFER_LIMITED_GAS: &str = r#"
(module
	;; ext_call(
	;;    callee_ptr: u32,
	;;    callee_len: u32,
	;;    gas: u64,
	;;    value_ptr: u32,
	;;    value_len: u32,
	;;    input_data_ptr: u32,
	;;    input_data_len: u32
	;;) -> u32
	(import "env" "ext_call" (func $ext_call (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))
	(func (export "call")
		(drop
			(call $ext_call
				(i32.const 4)  ;; Pointer to "callee" address.
				(i32.const 8)  ;; Length of "callee" address.
				(i64.const 228)  ;; How much gas to devote for the execution.
				(i32.const 12)  ;; Pointer to the buffer with value to transfer
				(i32.const 8)   ;; Length of the buffer with value to transfer.
				(i32.const 20)   ;; Pointer to input data buffer address
				(i32.const 4)   ;; Length of input data buffer
			)
		)
	)
	(func (export "deploy"))

	;; Destination AccountId to transfer the funds.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 4) "\09\00\00\00\00\00\00\00")
	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 12) "\06\00\00\00\00\00\00\00")

	(data (i32.const 20) "\01\02\03\04")
)
"#;

	#[test]
	fn contract_call_limited_gas() {
		let mut mock_ext = MockExt::default();
		execute(
			&CODE_TRANSFER_LIMITED_GAS,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&mut GasMeter::with_limit(50_000, 1),
		)
		.unwrap();

		assert_eq!(
			&mock_ext.transfers,
			&[TransferEntry {
				to: 9,
				value: 6,
				data: vec![1, 2, 3, 4],
				gas_left: 228,
			}]
		);
	}

	const CODE_GET_STORAGE: &str = r#"
(module
	(import "env" "ext_get_storage" (func $ext_get_storage (param i32) (result i32)))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_copy" (func $ext_scratch_copy (param i32 i32 i32)))
	(import "env" "ext_return" (func $ext_return (param i32 i32)))
	(import "env" "memory" (memory 1 1))

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


		;; Load a storage value into the scratch buf.
		(call $assert
			(i32.eq
				(call $ext_get_storage
					(i32.const 4)		;; The pointer to the storage key to fetch
				)

				;; Return value 0 means that the value is found and there were
				;; no errors.
				(i32.const 0)
			)
		)

		;; Find out the size of the scratch buffer
		(set_local $buf_size
			(call $ext_scratch_size)
		)

		;; Copy scratch buffer into this contract memory.
		(call $ext_scratch_copy
			(i32.const 36)		;; The pointer where to store the scratch buffer contents,
								;; 36 = 4 + 32
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(get_local			;; Count of bytes to copy.
				$buf_size
			)
		)

		;; Return the contents of the buffer
		(call $ext_return
			(i32.const 36)
			(get_local $buf_size)
		)

		;; env:ext_return doesn't return, so this is effectively unreachable.
		(unreachable)
	)

	(func (export "deploy"))

	(data (i32.const 4)
		"\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11"
		"\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11"
	)
)
"#;

	#[test]
	fn get_storage_puts_data_into_scratch_buf() {
		let mut mock_ext = MockExt::default();
		mock_ext
			.storage
			.insert([0x11; 32], [0x22; 32].to_vec());

		let mut return_buf = Vec::new();
		execute(
			CODE_GET_STORAGE,
			&[],
			&mut return_buf,
			&mut mock_ext,
			&mut GasMeter::with_limit(50_000, 1),
		)
		.unwrap();

		assert_eq!(return_buf, [0x22; 32].to_vec());
	}

	/// calls `ext_caller`, loads the address from the scratch buffer and
	/// compares it with the constant 42.
	const CODE_CALLER: &str = r#"
(module
	(import "env" "ext_caller" (func $ext_caller))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_copy" (func $ext_scratch_copy (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; fill the scratch buffer with the caller.
		(call $ext_caller)

		;; assert $ext_scratch_size == 8
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)

		;; copy contents of the scratch buffer into the contract's memory.
		(call $ext_scratch_copy
			(i32.const 8)		;; Pointer in memory to the place where to copy.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 8)		;; Count of bytes to copy.
		)

		;; assert that contents of the buffer is equal to the i64 value of 42.
		(call $assert
			(i64.eq
				(i64.load
					(i32.const 8)
				)
				(i64.const 42)
			)
		)
	)

	(func (export "deploy"))
)
"#;

	#[test]
	fn caller() {
		let mut mock_ext = MockExt::default();
		execute(
			CODE_CALLER,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&mut GasMeter::with_limit(50_000, 1),
		)
		.unwrap();
	}

	/// calls `ext_address`, loads the address from the scratch buffer and
	/// compares it with the constant 69.
	const CODE_ADDRESS: &str = r#"
(module
	(import "env" "ext_address" (func $ext_address))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_copy" (func $ext_scratch_copy (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; fill the scratch buffer with the self address.
		(call $ext_address)

		;; assert $ext_scratch_size == 8
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)

		;; copy contents of the scratch buffer into the contract's memory.
		(call $ext_scratch_copy
			(i32.const 8)		;; Pointer in memory to the place where to copy.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 8)		;; Count of bytes to copy.
		)

		;; assert that contents of the buffer is equal to the i64 value of 69.
		(call $assert
			(i64.eq
				(i64.load
					(i32.const 8)
				)
				(i64.const 69)
			)
		)
	)

	(func (export "deploy"))
)
"#;

	#[test]
	fn address() {
		let mut mock_ext = MockExt::default();
		execute(
			CODE_ADDRESS,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&mut GasMeter::with_limit(50_000, 1),
		)
		.unwrap();
	}

	const CODE_BALANCE: &str = r#"
(module
	(import "env" "ext_balance" (func $ext_balance))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_copy" (func $ext_scratch_copy (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the balance in the scratch buffer
		(call $ext_balance)

		;; assert $ext_scratch_size == 8
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)

		;; copy contents of the scratch buffer into the contract's memory.
		(call $ext_scratch_copy
			(i32.const 8)		;; Pointer in memory to the place where to copy.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 8)		;; Count of bytes to copy.
		)

		;; assert that contents of the buffer is equal to the i64 value of 228.
		(call $assert
			(i64.eq
				(i64.load
					(i32.const 8)
				)
				(i64.const 228)
			)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn balance() {
		let mut mock_ext = MockExt::default();
		let mut gas_meter = GasMeter::with_limit(50_000, 1);
		execute(
			CODE_BALANCE,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&mut gas_meter,
		)
		.unwrap();
	}

	const CODE_GAS_PRICE: &str = r#"
(module
	(import "env" "ext_gas_price" (func $ext_gas_price))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_copy" (func $ext_scratch_copy (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the gas price in the scratch buffer
		(call $ext_gas_price)

		;; assert $ext_scratch_size == 8
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)

		;; copy contents of the scratch buffer into the contract's memory.
		(call $ext_scratch_copy
			(i32.const 8)		;; Pointer in memory to the place where to copy.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 8)		;; Count of bytes to copy.
		)

		;; assert that contents of the buffer is equal to the i64 value of 1312.
		(call $assert
			(i64.eq
				(i64.load
					(i32.const 8)
				)
				(i64.const 1312)
			)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn gas_price() {
		let mut mock_ext = MockExt::default();
		let mut gas_meter = GasMeter::with_limit(50_000, 1312);
		execute(
			CODE_GAS_PRICE,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&mut gas_meter,
		)
		.unwrap();
	}

	const CODE_GAS_LEFT: &str = r#"
(module
	(import "env" "ext_gas_left" (func $ext_gas_left))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_copy" (func $ext_scratch_copy (param i32 i32 i32)))
	(import "env" "ext_return" (func $ext_return (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the gas left in the scratch buffer
		(call $ext_gas_left)

		;; assert $ext_scratch_size == 8
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)

		;; copy contents of the scratch buffer into the contract's memory.
		(call $ext_scratch_copy
			(i32.const 8)		;; Pointer in memory to the place where to copy.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 8)		;; Count of bytes to copy.
		)

		(call $ext_return
			(i32.const 8)
			(i32.const 8)
		)

		(unreachable)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn gas_left() {
		let mut mock_ext = MockExt::default();
		let mut gas_meter = GasMeter::with_limit(50_000, 1312);
		execute(
			CODE_GAS_LEFT,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&mut gas_meter,
		)
		.unwrap();
	}

	const CODE_VALUE_TRANSFERRED: &str = r#"
(module
	(import "env" "ext_value_transferred" (func $ext_value_transferred))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_copy" (func $ext_scratch_copy (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the value transferred in the scratch buffer
		(call $ext_value_transferred)

		;; assert $ext_scratch_size == 8
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)

		;; copy contents of the scratch buffer into the contract's memory.
		(call $ext_scratch_copy
			(i32.const 8)		;; Pointer in memory to the place where to copy.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 8)		;; Count of bytes to copy.
		)

		;; assert that contents of the buffer is equal to the i64 value of 1337.
		(call $assert
			(i64.eq
				(i64.load
					(i32.const 8)
				)
				(i64.const 1337)
			)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn value_transferred() {
		let mut mock_ext = MockExt::default();
		let mut gas_meter = GasMeter::with_limit(50_000, 1);
		execute(
			CODE_VALUE_TRANSFERRED,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&mut gas_meter,
		)
		.unwrap();
	}

	const CODE_DISPATCH_CALL: &str = r#"
(module
	(import "env" "ext_dispatch_call" (func $ext_dispatch_call (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call")
		(call $ext_dispatch_call
			(i32.const 8) ;; Pointer to the start of encoded call buffer
			(i32.const 13) ;; Length of the buffer
		)
	)
	(func (export "deploy"))

	(data (i32.const 8) "\00\01\2A\00\00\00\00\00\00\00\E5\14\00")
)
"#;

	#[test]
	fn dispatch_call() {
		// This test can fail due to the encoding changes. In case it becomes too annoying
		// let's rewrite so as we use this module controlled call or we serialize it in runtime.

		let mut mock_ext = MockExt::default();
		execute(
			CODE_DISPATCH_CALL,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&mut GasMeter::with_limit(50_000, 1),
		)
		.unwrap();

		assert_eq!(
			&mock_ext.dispatches,
			&[DispatchEntry(
				Call::Balances(balances::Call::set_balance(42, 1337, 0)),
			)]
		);
	}

	const CODE_RETURN_FROM_START_FN: &str = r#"
(module
	(import "env" "ext_return" (func $ext_return (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(start $start)
	(func $start
		(call $ext_return
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
		let mut mock_ext = MockExt::default();
		let mut output_data = Vec::new();
		execute(
			CODE_RETURN_FROM_START_FN,
			&[],
			&mut output_data,
			&mut mock_ext,
			&mut GasMeter::with_limit(50_000, 1),
		)
		.unwrap();

		assert_eq!(output_data, vec![1, 2, 3, 4]);
	}

	const CODE_TIMESTAMP_NOW: &str = r#"
(module
	(import "env" "ext_now" (func $ext_now))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_copy" (func $ext_scratch_copy (param i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the block timestamp in the scratch buffer
		(call $ext_now)

		;; assert $ext_scratch_size == 8
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)

		;; copy contents of the scratch buffer into the contract's memory.
		(call $ext_scratch_copy
			(i32.const 8)		;; Pointer in memory to the place where to copy.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 8)		;; Count of bytes to copy.
		)

		;; assert that contents of the buffer is equal to the i64 value of 1111.
		(call $assert
			(i64.eq
				(i64.load
					(i32.const 8)
				)
				(i64.const 1111)
			)
		)
	)
	(func (export "deploy"))
)
"#;

	#[test]
	fn now() {
		let mut mock_ext = MockExt::default();
		let mut gas_meter = GasMeter::with_limit(50_000, 1);
		execute(
			CODE_TIMESTAMP_NOW,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&mut gas_meter,
		)
		.unwrap();
	}

	const CODE_RANDOM: &str = r#"
(module
	(import "env" "ext_random" (func $ext_random (param i32 i32)))
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_copy" (func $ext_scratch_copy (param i32 i32 i32)))
	(import "env" "ext_return" (func $ext_return (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "call")
		;; This stores the block random seed in the scratch buffer
		(call $ext_random
			(i32.const 40) ;; Pointer in memory to the start of the subject buffer
			(i32.const 32) ;; The subject buffer's length
		)

		;; assert $ext_scratch_size == 32
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 32)
			)
		)

		;; copy contents of the scratch buffer into the contract's memory.
		(call $ext_scratch_copy
			(i32.const 8)		;; Pointer in memory to the place where to copy.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 32)		;; Count of bytes to copy.
		)

		;; return the data from the contract
		(call $ext_return
			(i32.const 8)
			(i32.const 32)
		)
	)
	(func (export "deploy"))

	;; [8,40) is reserved for the result of PRNG.

	;; the subject used for the PRNG. [40,72)
	(data (i32.const 40)
		"\00\01\02\03\04\05\06\07\08\09\0A\0B\0C\0D\0E\0F"
		"\00\01\02\03\04\05\06\07\08\09\0A\0B\0C\0D\0E\0F"
	)
)
"#;

	#[test]
	fn random() {
		let mut mock_ext = MockExt::default();
		let mut gas_meter = GasMeter::with_limit(50_000, 1);

		let mut return_buf = Vec::new();
		execute(
			CODE_RANDOM,
			&[],
			&mut return_buf,
			&mut mock_ext,
			&mut gas_meter,
		)
		.unwrap();

		// The mock ext just returns the same data that was passed as the subject.
		assert_eq!(
			&return_buf,
			&hex!("000102030405060708090A0B0C0D0E0F000102030405060708090A0B0C0D0E0F")
		);
	}

	const CODE_DEPOSIT_EVENT: &str = r#"
(module
	(import "env" "ext_deposit_event" (func $ext_deposit_event (param i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call")
		(call $ext_deposit_event
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
		let mut gas_meter = GasMeter::with_limit(50_000, 1);
		execute(
			CODE_DEPOSIT_EVENT,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&mut gas_meter
		)
		.unwrap();

		assert_eq!(mock_ext.events, vec![
			(vec![H256::repeat_byte(0x33)],
			vec![0x00, 0x01, 0x2a, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0xe5, 0x14, 0x00])
		]);

		assert_eq!(gas_meter.gas_left(), 50_000
			- 6            // Explicit
			- 13 - 1 - 1   // Deposit event
			- (13 + 33)    // read memory
		);
	}

	const CODE_DEPOSIT_EVENT_MAX_TOPICS: &str = r#"
(module
	(import "env" "ext_deposit_event" (func $ext_deposit_event (param i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call")
		(call $ext_deposit_event
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
		let mut mock_ext = MockExt::default();
		let mut gas_meter = GasMeter::with_limit(50_000, 1);

		assert_eq!(
			execute(
				CODE_DEPOSIT_EVENT_MAX_TOPICS,
				&[],
				&mut Vec::new(),
				&mut mock_ext,
				&mut gas_meter
			),
			Err("during execution"),
		);
	}

	const CODE_DEPOSIT_EVENT_DUPLICATES: &str = r#"
(module
	(import "env" "ext_deposit_event" (func $ext_deposit_event (param i32 i32 i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func (export "call")
		(call $ext_deposit_event
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
		let mut mock_ext = MockExt::default();
		let mut gas_meter = GasMeter::with_limit(50_000, 1);

		assert_eq!(
			execute(
				CODE_DEPOSIT_EVENT_DUPLICATES,
				&[],
				&mut Vec::new(),
				&mut mock_ext,
				&mut gas_meter
			),
			Err("during execution"),
		);
	}
}
