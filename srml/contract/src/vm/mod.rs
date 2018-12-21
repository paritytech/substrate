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

//! This module provides a means for executing contracts
//! represented in wasm.

use exec::CreateReceipt;
use gas::GasMeter;
use rstd::prelude::*;
use {Trait, Schedule};
use {balances, sandbox, system};

type BalanceOf<T> = <T as balances::Trait>::Balance;
type AccountIdOf<T> = <T as system::Trait>::AccountId;

mod prepare;
#[macro_use]
mod env_def;
mod runtime;

use self::prepare::{prepare_contract, PreparedContract};
use self::runtime::{to_execution_result, Runtime};

/// An interface that provides an access to the external environment in which the
/// smart-contract is executed.
///
/// This interface is specialised to an account of the executing code, so all
/// operations are implicitly performed on that account.
pub trait Ext {
	type T: Trait;

	/// Returns the storage entry of the executing account by the given key.
	fn get_storage(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Sets the storage entry by the given key to the specified value.
	fn set_storage(&mut self, key: &[u8], value: Option<Vec<u8>>);

	/// Create a new account for a contract.
	///
	/// The newly created account will be associated with the `code`. `value` specifies the amount of value
	/// transfered from this to the newly created account.
	fn create(
		&mut self,
		code: &[u8],
		value: BalanceOf<Self::T>,
		gas_meter: &mut GasMeter<Self::T>,
		data: &[u8],
	) -> Result<CreateReceipt<Self::T>, ()>;

	/// Call (possibly transfering some amount of funds) into the specified account.
	fn call(
		&mut self,
		to: &AccountIdOf<Self::T>,
		value: BalanceOf<Self::T>,
		gas_meter: &mut GasMeter<Self::T>,
		data: &[u8],
		output_data: &mut Vec<u8>,
	) -> Result<(), ()>;

	/// Returns a reference to the account id of the caller.
	fn caller(&self) -> &AccountIdOf<Self::T>;
}

/// Error that can occur while preparing or executing wasm smart-contract.
#[derive(Debug, PartialEq, Eq)]
pub enum Error {
	/// Error happened while serializing the module.
	Serialization,

	/// Error happened while deserializing the module.
	Deserialization,

	/// Internal memory declaration has been found in the module.
	InternalMemoryDeclared,

	/// Gas instrumentation failed.
	///
	/// This most likely indicates the module isn't valid.
	GasInstrumentation,

	/// Stack instrumentation failed.
	///
	/// This  most likely indicates the module isn't valid.
	StackHeightInstrumentation,

	/// Error happened during invocation of the contract's entrypoint.
	///
	/// Most likely because of trap.
	Invoke,

	/// Error happened during instantiation.
	///
	/// This might indicate that `start` function trapped, or module isn't
	/// instantiable and/or unlinkable.
	Instantiate,

	/// Memory creation error.
	///
	/// This might happen when the memory import has invalid descriptor or
	/// requested too much resources.
	Memory,
}

/// Execute the given code as a contract.
pub fn execute<'a, E: Ext>(
	code: &[u8],
	input_data: &[u8],
	output_data: &mut Vec<u8>,
	ext: &'a mut E,
	schedule: &Schedule<<E::T as Trait>::Gas>,
	gas_meter: &mut GasMeter<E::T>,
) -> Result<(), Error> {
	let env = runtime::init_env();

	let PreparedContract {
		instrumented_code,
		memory,
	} = prepare_contract(code, &schedule, &env)?;

	let mut imports = sandbox::EnvironmentDefinitionBuilder::new();
	for (func_name, ext_func) in &env.funcs {
		imports.add_host_func("env", &func_name[..], ext_func.raw_fn_ptr());
	}
	imports.add_memory("env", "memory", memory.clone());

	let mut runtime = Runtime::new(ext, input_data, output_data, &schedule, memory, gas_meter);

	// Instantiate the instance from the instrumented module code.
	match sandbox::Instance::new(&instrumented_code, &imports, &mut runtime) {
		// No errors or traps were generated on instantiation! That
		// means we can now invoke the contract entrypoint.
		Ok(mut instance) => {
			let err = instance.invoke(b"call", &[], &mut runtime).err();
			to_execution_result(runtime, err)
		}
		// `start` function trapped. Treat it in the same manner as an execution error.
		Err(err @ sandbox::Error::Execution) => to_execution_result(runtime, Some(err)),
		// Other instantiation errors.
		// Return without executing anything.
		Err(_) => return Err(Error::Instantiate),
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use gas::GasMeter;
	use std::collections::HashMap;
	use tests::Test;
	use wabt;

	#[derive(Debug, PartialEq, Eq)]
	struct CreateEntry {
		code: Vec<u8>,
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
		storage: HashMap<Vec<u8>, Vec<u8>>,
		creates: Vec<CreateEntry>,
		transfers: Vec<TransferEntry>,
		next_account_id: u64,
	}
	impl Ext for MockExt {
		type T = Test;

		fn get_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
			self.storage.get(key).cloned()
		}
		fn set_storage(&mut self, key: &[u8], value: Option<Vec<u8>>) {
			*self.storage.entry(key.to_vec()).or_insert(Vec::new()) = value.unwrap_or(Vec::new());
		}
		fn create(
			&mut self,
			code: &[u8],
			endowment: u64,
			gas_meter: &mut GasMeter<Test>,
			data: &[u8],
		) -> Result<CreateReceipt<Test>, ()> {
			self.creates.push(CreateEntry {
				code: code.to_vec(),
				endowment,
				data: data.to_vec(),
				gas_left: gas_meter.gas_left(),
			});
			let address = self.next_account_id;
			self.next_account_id += 1;

			Ok(CreateReceipt { address })
		}
		fn call(
			&mut self,
			to: &u64,
			value: u64,
			gas_meter: &mut GasMeter<Test>,
			data: &[u8],
			_output_data: &mut Vec<u8>,
		) -> Result<(), ()> {
			self.transfers.push(TransferEntry {
				to: *to,
				value,
				data: data.to_vec(),
				gas_left: gas_meter.gas_left(),
			});
			// Assume for now that it was just a plain transfer.
			// TODO: Add tests for different call outcomes.
			Ok(())
		}
		fn caller(&self) -> &u64 {
			&42
		}
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
		let code_transfer = wabt::wat2wasm(CODE_TRANSFER).unwrap();

		let mut mock_ext = MockExt::default();
		execute(
			&code_transfer,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&Schedule::<u64>::default(),
			&mut GasMeter::with_limit(50_000, 1),
		).unwrap();

		assert_eq!(
			&mock_ext.transfers,
			&[TransferEntry {
				to: 9,
				value: 6,
				data: vec![
					1, 2, 3, 4,
				],
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
				(i32.const 12)   ;; Pointer to `code`
				(i32.const 8)    ;; Length of `code`
				(i64.const 0)    ;; How much gas to devote for the execution. 0 = all.
				(i32.const 4)    ;; Pointer to the buffer with value to transfer
				(i32.const 8)    ;; Length of the buffer with value to transfer
				(i32.const 20)   ;; Pointer to input data buffer address
				(i32.const 4)    ;; Length of input data buffer
			)
		)
	)
	;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
	(data (i32.const 4) "\03\00\00\00\00\00\00\00")
	;; Embedded wasm code.
	(data (i32.const 12) "\00\61\73\6d\01\00\00\00")
	;; Input data to pass to the contract being created.
	(data (i32.const 20) "\01\02\03\04")
)
"#;

	#[test]
	fn contract_create() {
		let code_create = wabt::wat2wasm(CODE_CREATE).unwrap();

		let mut mock_ext = MockExt::default();
		execute(
			&code_create,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&Schedule::default(),
			&mut GasMeter::with_limit(50_000, 1),
		).unwrap();

		assert_eq!(
			&mock_ext.creates,
			&[CreateEntry {
				code: vec![0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00],
				endowment: 3,
				data: vec![
					1, 2, 3, 4,
				],
				gas_left: 49970,
			}]
		);
	}

	const CODE_MEM: &str = r#"
(module
	;; Internal memory is not allowed.
	(memory 1 1)

	(func (export "call")
		nop
	)
)
"#;

	#[test]
	fn contract_internal_mem() {
		let code_mem = wabt::wat2wasm(CODE_MEM).unwrap();

		let mut mock_ext = MockExt::default();

		assert_matches!(
			execute(
				&code_mem,
				&[],
				&mut Vec::new(),
				&mut mock_ext,
				&Schedule::default(),
				&mut GasMeter::with_limit(100_000, 1)
			),
			Err(_)
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
		let code_transfer = wabt::wat2wasm(CODE_TRANSFER_LIMITED_GAS).unwrap();

		let mut mock_ext = MockExt::default();
		execute(
			&code_transfer,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&Schedule::default(),
			&mut GasMeter::with_limit(50_000, 1),
		).unwrap();

		assert_eq!(
			&mock_ext.transfers,
			&[TransferEntry {
				to: 9,
				value: 6,
				data: vec![
					1, 2, 3, 4,
				],
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

	(data (i32.const 4) "\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11\11")
)
"#;

	#[test]
	fn get_storage_puts_data_into_scratch_buf() {
		let code_get_storage = wabt::wat2wasm(CODE_GET_STORAGE).unwrap();

		let mut mock_ext = MockExt::default();
		mock_ext.storage.insert([0x11; 32].to_vec(), [0x22; 32].to_vec());

		let mut return_buf = Vec::new();
		execute(
			&code_get_storage,
			&[],
			&mut return_buf,
			&mut mock_ext,
			&Schedule::default(),
			&mut GasMeter::with_limit(50_000, 1),
		).unwrap();

		assert_eq!(
			return_buf,
			[0x22; 32].to_vec(),
		);
	}


	/// calls `ext_caller`, loads the address from the scratch buffer and
	/// compares it with the constant 42.
	const CODE_CALLER: &'static str =
r#"
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
)
"#;

	#[test]
	fn caller() {
		let code_caller = wabt::wat2wasm(CODE_CALLER).unwrap();

		let mut mock_ext = MockExt::default();
		execute(
			&code_caller,
			&[],
			&mut Vec::new(),
			&mut mock_ext,
			&Schedule::<u64>::default(),
			&mut GasMeter::with_limit(50_000, 1),
		).unwrap();
	}
}
