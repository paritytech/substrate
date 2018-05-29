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

extern crate parity_wasm;
extern crate pwasm_utils;

extern crate substrate_runtime_std as rstd;
extern crate substrate_runtime_sandbox as sandbox;
extern crate substrate_codec as codec;

#[cfg(test)]
#[macro_use]
extern crate assert_matches;

#[cfg(test)]
extern crate wabt;

use rstd::prelude::*;
use codec::Slicable;

use parity_wasm::elements::{self, External, MemoryType};
use pwasm_utils::rules;

/// An interface that provides an access to the external environment in which the
/// smart-contract is executed.
///
/// This interface is specialised to an account of the executing code, so all
/// operations are implicitly performed on that account.
pub trait Ext {
	/// The indentifier of an account.
	type AccountId: Slicable + Clone;
	/// The balance of an account.
	type Balance: Slicable;

	/// Returns the storage entry of the executing account by the given key.
	fn get_storage(&self, key: &[u8]) -> Option<Vec<u8>>;

	/// Sets the storage entry by the given key to the specified value.
	fn set_storage(&mut self, key: &[u8], value: Option<Vec<u8>>);

	// TODO: Return the address of the created contract.
	/// Create a new account for a contract.
	///
	/// The newly created account will be associated with the `code`. `value` specifies the amount of value
	/// transfered from this to the newly created account.
	fn create(&mut self, code: &[u8], value: Self::Balance);

	/// Transfer some funds to the specified account.
	fn transfer(&mut self, to: &Self::AccountId, value: Self::Balance);
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

struct Runtime<'a, T: Ext + 'a> {
	ext: &'a mut T,
	memory: sandbox::Memory,
	gas_used: u64,
	gas_limit: u64,
}
impl<'a, T: Ext + 'a> Runtime<'a, T> {
	fn memory(&self) -> &sandbox::Memory {
		&self.memory
	}
	fn ext(&self) -> &T {
		self.ext
	}
	fn ext_mut(&mut self) -> &mut T {
		self.ext
	}
	/// Account for used gas.
	///
	/// Returns `false` if there is not enough gas or addition of the specified
	/// amount of gas has lead to overflow. On success returns `true`.
	///
	/// Intuition about the return value sense is to answer the question 'are we allowed to continue?'
	fn charge_gas(&mut self, amount: u64) -> bool {
		match self.gas_used.checked_add(amount) {
			None => false,
			Some(val) if val > self.gas_limit => false,
			Some(val) => {
				self.gas_used = val;
				true
			}
		}
	}
}

/// Execute the given code as a contract.
pub fn execute<'a, T: Ext>(
	code: &[u8],
	ext: &'a mut T,
	gas_limit: u64,
) -> Result<(), Error> {
	// ext_gas(amount: u32)
	//
	// Account for used gas. Traps if gas used is greater than gas limit.
	//
	// - amount: How much gas is used.
	fn ext_gas<T: Ext>(e: &mut Runtime<T>, args: &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError> {
		let amount = args[0].as_i32().unwrap() as u32;
		if e.charge_gas(amount as u64) {
			Ok(sandbox::ReturnValue::Unit)
		} else {
			Err(sandbox::HostError)
		}
	}

	// ext_put_storage(location_ptr: u32, value_non_null: u32, value_ptr: u32);
	//
	// Change the value at the given location in storage or remove it.
	//
	// - location_ptr: pointer into the linear
	//   memory where the location of the requested value is placed.
	// - value_non_null: if set to 0, then the entry
	//   at the given location will be removed.
	// - value_ptr: pointer into the linear memory
	//   where the value to set is placed. If `value_non_null` is set to 0, then this parameter is ignored.
	fn ext_set_storage<T: Ext>(
		e: &mut Runtime<T>,
		args: &[sandbox::TypedValue],
	) -> Result<sandbox::ReturnValue, sandbox::HostError> {
		let location_ptr = args[0].as_i32().unwrap() as u32;
		let value_non_null = args[1].as_i32().unwrap() as u32;
		let value_ptr = args[2].as_i32().unwrap() as u32;

		let mut location = [0; 32];

		e.memory().get(location_ptr, &mut location)?;

		let value = if value_non_null != 0 {
			let mut value = [0; 32];
			e.memory().get(value_ptr, &mut value)?;
			Some(value.to_vec())
		} else {
			None
		};
		e.ext_mut().set_storage(
			&location,
			value,
		);

		Ok(sandbox::ReturnValue::Unit)
	}

	// ext_get_storage(location_ptr: u32, dest_ptr: u32);
	//
	// Retrieve the value at the given location from the strorage.
	// If there is no entry at the given location then all-zero-value
	// will be returned.
	//
	// - location_ptr: pointer into the linear
	//   memory where the location of the requested value is placed.
	// - dest_ptr: pointer where contents of the specified storage location
	//   should be placed.
	fn ext_get_storage<T: Ext>(e: &mut Runtime<T>, args: &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError> {
		let location_ptr = args[0].as_i32().unwrap() as u32;
		let dest_ptr = args[1].as_i32().unwrap() as u32;

		let mut location = [0; 32];
		e.memory().get(location_ptr, &mut location)?;

		if let Some(value) = e.ext().get_storage(&location) {
			e.memory().set(dest_ptr, &value)?;
		} else {
			e.memory().set(dest_ptr, &[0u8; 32])?;
		}

		Ok(sandbox::ReturnValue::Unit)
	}

	// ext_transfer(transfer_to: u32, transfer_to_len: u32, value_ptr: u32, value_len: u32)
	fn ext_transfer<T: Ext>(e: &mut Runtime<T>, args: &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError> {
		let transfer_to_ptr = args[0].as_i32().unwrap() as u32;
		let transfer_to_len = args[1].as_i32().unwrap() as u32;
		let value_ptr = args[2].as_i32().unwrap() as u32;
		let value_len = args[3].as_i32().unwrap() as u32;

		let mut transfer_to = Vec::new();
		transfer_to.resize(transfer_to_len as usize, 0);
		e.memory().get(transfer_to_ptr, &mut transfer_to)?;
		let transfer_to = T::AccountId::decode(&mut &transfer_to[..]).unwrap();

		let mut value_buf = Vec::new();
		value_buf.resize(value_len as usize, 0);
		e.memory().get(value_ptr, &mut value_buf)?;
		let value = T::Balance::decode(&mut &value_buf[..]).unwrap();

		e.ext_mut().transfer(&transfer_to, value);

		Ok(sandbox::ReturnValue::Unit)
	}

	// ext_create(code_ptr: u32, code_len: u32, value_ptr: u32, value_len: u32)
	fn ext_create<T: Ext>(e: &mut Runtime<T>, args: &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError> {
		let code_ptr = args[0].as_i32().unwrap() as u32;
		let code_len = args[1].as_i32().unwrap() as u32;
		let value_ptr = args[2].as_i32().unwrap() as u32;
		let value_len = args[3].as_i32().unwrap() as u32;

		let mut value_buf = Vec::new();
		value_buf.resize(value_len as usize, 0);
		e.memory().get(value_ptr, &mut value_buf)?;
		let value = T::Balance::decode(&mut &value_buf[..]).unwrap();

		let mut code = Vec::new();
		code.resize(code_len as usize, 0u8);
		e.memory().get(code_ptr, &mut code)?;

		e.ext_mut().create(&code, value);

		Ok(sandbox::ReturnValue::Unit)
	}

	let PreparedContract {
		instrumented_code,
		memory,
	} = prepare_contract(code)?;

	let mut imports = sandbox::EnvironmentDefinitionBuilder::new();
	imports.add_host_func("env", "gas", ext_gas::<T>);
	imports.add_host_func("env", "ext_set_storage", ext_set_storage::<T>);
	imports.add_host_func("env", "ext_get_storage", ext_get_storage::<T>);
	imports.add_host_func("env", "ext_transfer", ext_transfer::<T>);
	imports.add_host_func("env", "ext_create", ext_create::<T>);
	// TODO: ext_balance, ext_address, ext_callvalue, etc.
	imports.add_memory("env", "memory", memory.clone());

	let mut runtime = Runtime {
		ext,
		memory,
		gas_limit,
		gas_used: 0,
	};

	let mut instance =
		sandbox::Instance::new(&instrumented_code, &imports, &mut runtime)
			.map_err(|_| Error::Instantiate)?;
	instance
		.invoke(b"call", &[], &mut runtime)
		.map(|_| ())
		.map_err(|_| Error::Invoke)
}

#[derive(Clone)]
struct Config {
	/// Gas cost of a growing memory by single page.
	grow_mem_cost: u32,

	/// Gas cost of a regular operation.
	regular_op_cost: u32,

	/// How tall the stack is allowed to grow?
	///
	/// See https://wiki.parity.io/WebAssembly-StackHeight to find out
	/// how the stack frame cost is calculated.
	max_stack_height: u32,

	//// What is the maximal memory pages amount is allowed to have for
	/// a contract.
	max_memory_pages: u32,
}

impl Default for Config {
	fn default() -> Config {
		Config {
			grow_mem_cost: 1,
			regular_op_cost: 1,
			max_stack_height: 64 * 1024,
			max_memory_pages: 16,
		}
	}
}

struct ContractModule {
	// An `Option` is used here for loaning (`take()`-ing) the module.
	// Invariant: Can't be `None` (i.e. on enter and on exit from the function
	// the value *must* be `Some`).
	module: Option<elements::Module>,
	config: Config,
}

impl ContractModule {
	fn new(original_code: &[u8], config: Config) -> Result<ContractModule, Error> {
		let module =
			elements::deserialize_buffer(original_code).map_err(|_| Error::Deserialization)?;
		Ok(ContractModule {
			module: Some(module),
			config,
		})
	}

	/// Ensures that module doesn't declare internal memories.
	///
	/// In this runtime we only allow wasm module to import memory from the environment.
	/// Memory section contains declarations of internal linear memories, so if we find one
	/// we reject such a module.
	fn ensure_no_internal_memory(&self) -> Result<(), Error> {
		let module = self.module
			.as_ref()
			.expect("On entry to the function `module` can't be None; qed");
		if module
			.memory_section()
			.map_or(false, |ms| ms.entries().len() > 0)
		{
			return Err(Error::InternalMemoryDeclared);
		}
		Ok(())
	}

	fn inject_gas_metering(&mut self) -> Result<(), Error> {
		let gas_rules = rules::Set::new(self.config.regular_op_cost, Default::default())
			.with_grow_cost(self.config.grow_mem_cost)
			.with_forbidden_floats();

		let module = self.module
			.take()
			.expect("On entry to the function `module` can't be `None`; qed");

		let contract_module = pwasm_utils::inject_gas_counter(module, &gas_rules)
			.map_err(|_| Error::GasInstrumentation)?;

		self.module = Some(contract_module);
		Ok(())
	}

	fn inject_stack_height_metering(&mut self) -> Result<(), Error> {
		let module = self.module
			.take()
			.expect("On entry to the function `module` can't be `None`; qed");

		let contract_module =
			pwasm_utils::stack_height::inject_limiter(module, self.config.max_stack_height)
				.map_err(|_| Error::StackHeightInstrumentation)?;

		self.module = Some(contract_module);
		Ok(())
	}

	/// Find the memory import entry and return it's descriptor.
	fn find_mem_import(&self) -> Option<&MemoryType> {
		let import_section = self.module
			.as_ref()
			.expect("On entry to the function `module` can't be `None`; qed")
			.import_section()?;
		for import in import_section.entries() {
			if let ("env", "memory", &External::Memory(ref memory_type)) =
				(import.module(), import.field(), import.external())
			{
				return Some(memory_type);
			}
		}
		None
	}

	fn into_wasm_code(mut self) -> Result<Vec<u8>, Error> {
		elements::serialize(
			self.module
				.take()
				.expect("On entry to the function `module` can't be `None`; qed"),
		).map_err(|_| Error::Serialization)
	}
}

struct PreparedContract {
	instrumented_code: Vec<u8>,
	memory: sandbox::Memory,
}

fn prepare_contract(original_code: &[u8]) -> Result<PreparedContract, Error> {
	let config = Config::default();

	let mut contract_module = ContractModule::new(original_code, config.clone())?;
	contract_module.ensure_no_internal_memory()?;
	contract_module.inject_gas_metering()?;
	contract_module.inject_stack_height_metering()?;

	// Inspect the module to extract the initial and maximum page count.
	let memory = match contract_module.find_mem_import() {
		Some(memory_type) => {
			let limits = memory_type.limits();
			match (limits.initial(), limits.maximum()) {
				(initial, Some(maximum)) if initial > maximum => {
					// Requested initial number of pages should not exceed the requested maximum.
					return Err(Error::Memory);
				}
				(_, Some(maximum)) if maximum > config.max_memory_pages => {
					// Maximum number of pages should not exceed the configured maximum.
					return Err(Error::Memory);
				}
				(_, None) => {
					// Maximum number of pages should be always declared.
					// This isn't a hard requirement and can be treated as a maxiumum set
					// to configured maximum.
					return Err(Error::Memory)
				}
				(initial, maximum) => sandbox::Memory::new(
					initial,
					maximum,
				)
			}
		},

		// If none memory imported then just crate an empty placeholder.
		// Any access to it will lead to out of bounds trap.
		None => sandbox::Memory::new(0, Some(0)),
	}.map_err(|_| Error::Memory)?;

	Ok(PreparedContract {
		instrumented_code: contract_module.into_wasm_code()?,
		memory,
	})
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::fmt;
	use wabt;
	use std::collections::HashMap;

	#[derive(Debug, PartialEq, Eq)]
	struct CreateEntry {
		code: Vec<u8>,
		endownment: u64,
	}
	#[derive(Debug, PartialEq, Eq)]
	struct TransferEntry {
		to: u64,
		value: u64,
	}
	#[derive(Default)]
	struct MockExt {
		storage: HashMap<Vec<u8>, Vec<u8>>,
		creates: Vec<CreateEntry>,
		transfers: Vec<TransferEntry>,
	}
	impl Ext for MockExt {
		type AccountId = u64;
		type Balance = u64;

		fn get_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
			self.storage.get(key).cloned()
		}
		fn set_storage(&mut self, key: &[u8], value: Option<Vec<u8>>) {
			*self.storage.entry(key.to_vec()).or_insert(Vec::new()) = value.unwrap_or(Vec::new());
		}
		fn create(&mut self, code: &[u8], value: Self::Balance) {
			self.creates.push(
				CreateEntry {
					code: code.to_vec(),
					endownment: value,
				}
			);
		}
		fn transfer(&mut self, to: &Self::AccountId, value: Self::Balance) {
			self.transfers.push(
				TransferEntry {
					to: *to,
					value,
				}
			);
		}
	}

	impl fmt::Debug for PreparedContract {
		fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
			write!(f, "PreparedContract {{ .. }}")
		}
	}

	fn parse_and_prepare_wat(wat: &str) -> Result<PreparedContract, Error> {
		let wasm = wabt::Wat2Wasm::new()
			.validate(false)
			.convert(wat)
			.unwrap();
		prepare_contract(wasm.as_ref())
	}

	#[test]
	fn internal_memory_declaration() {
		let r = parse_and_prepare_wat(
			r#"(module (memory 1 1))"#,
		);
		assert_matches!(r, Err(Error::InternalMemoryDeclared));
	}

	#[test]
	fn memory() {
		// This test assumes that maximum page number is configured to a certain number.
		assert_eq!(Config::default().max_memory_pages, 16);

		let r = parse_and_prepare_wat(
			r#"(module (import "env" "memory" (memory 1 1)))"#,
		);
		assert_matches!(r, Ok(_));

		// No memory import
		let r = parse_and_prepare_wat(
			r#"(module)"#,
		);
		assert_matches!(r, Ok(_));

		// incorrect import name. That's kinda ok, since this will fail
		// at later stage when imports will be resolved.
		let r = parse_and_prepare_wat(
			r#"(module (import "vne" "memory" (memory 1 1)))"#,
		);
		assert_matches!(r, Ok(_));

		// initial exceed maximum
		let r = parse_and_prepare_wat(
			r#"(module (import "env" "memory" (memory 16 1)))"#,
		);
		assert_matches!(r, Err(Error::Memory));

		// no maximum
		let r = parse_and_prepare_wat(
			r#"(module (import "env" "memory" (memory 1)))"#,
		);
		assert_matches!(r, Err(Error::Memory));

		// requested maximum exceed configured maximum
		let r = parse_and_prepare_wat(
			r#"(module (import "env" "memory" (memory 1 17)))"#,
		);
		assert_matches!(r, Err(Error::Memory));
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
    (data (i32.const 4) "\02\00\00\00\00\00\00\00")

    ;; Amount of value to transfer.
	;; Represented by u64 (8 bytes long) in little endian.
    (data (i32.const 12) "\06\00\00\00\00\00\00\00")
)
"#;

	#[test]
	fn contract_transfer() {
		let code_transfer = wabt::wat2wasm(CODE_TRANSFER).unwrap();

		let mut mock_ext = MockExt::default();
		execute(&code_transfer, &mut mock_ext, 50_000).unwrap();

		assert_eq!(&mock_ext.transfers, &[TransferEntry {
			to: 2,
			value: 6,
		}]);
	}

	/// Returns code that uses `ext_create` runtime call.
	///
	/// Takes bytecode of the contract that needs to be deployed.
	fn code_create(child_bytecode: &[u8]) -> String {
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
    (data (i32.const 12) "{escaped_bytecode}")
)
"#,
			escaped_bytecode = escaped_bytestring(&child_bytecode),
			code_len = child_bytecode.len(),
		)
	}

	#[test]
	fn contract_create() {
		let code_transfer = wabt::wat2wasm(CODE_TRANSFER).unwrap();
		let code_create = wabt::wat2wasm(&code_create(&code_transfer)).unwrap();

		let mut mock_ext = MockExt::default();
		execute(&code_create, &mut mock_ext, 50_000).unwrap();

		assert_eq!(&mock_ext.creates, &[
			CreateEntry {
				code: code_transfer,
				endownment: 3,
			}
		]);
	}

	/// This code a value from the storage, increment it's first byte
	/// and then stores it back in the storage.
	const CODE_ADDER: &str =
r#"
(module
    ;; ext_set_storage(location_ptr: i32, value_non_null: bool, value_ptr: i32)
    (import "env" "ext_set_storage" (func $ext_set_storage (param i32 i32 i32)))
    ;; ext_get_storage(location_ptr: i32, value_ptr: i32)
    (import "env" "ext_get_storage" (func $ext_get_storage (param i32 i32)))
    (import "env" "memory" (memory 1 1))

    (func (export "call")
        (call $ext_get_storage
            (i32.const 4)  ;; Point to a location of the storage.
            (i32.const 36) ;; The result will be written at this address.
        )
        (i32.store
            (i32.const 36)
            (i32.add
                (i32.load
                    (i32.const 36)
                )
                (i32.const 1)
            )
        )

        (call $ext_set_storage
            (i32.const 4)  ;; Pointer to a location of the storage.
            (i32.const 1)  ;; Value is not null.
            (i32.const 36) ;; Pointer to a data we want to put in the storage.
        )
    )

    ;; Location of storage to load/store the data. 32 bytes.
    (data (i32.const 4) "\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01\01")
)
"#;

	#[test]
	fn contract_adder() {
		let code_adder = wabt::wat2wasm(CODE_ADDER).unwrap();

		let mut mock_ext = MockExt::default();

		// Execute the test twice.
		execute(&code_adder, &mut mock_ext, 50_000).unwrap();
		execute(&code_adder, &mut mock_ext, 50_000).unwrap();

		let storage_addr = [0x01u8; 32];
		assert_eq!(
			&mock_ext.storage.get(&storage_addr[..]).unwrap()[..],
			&[
				2, 0, 0, 0, 0, 0, 0, 0,
				0, 0, 0, 0, 0, 0, 0, 0,
				0, 0, 0, 0, 0, 0, 0, 0,
				0, 0, 0, 0, 0, 0, 0, 0,
			][..],
		);
	}

	// This code should make 100_000 iterations.
	const CODE_LOOP: &str =
r#"
(module
	(func (export "call")
		(local $i i32)

		loop $l
			;; $i = $i + 1
			(set_local $i
				(i32.add
					(get_local $i)
					(i32.const 1)
				)
			)

			;; if $i < 100_000u32: goto $l
			(br_if $l
				(i32.lt_u
					(get_local $i)
					(i32.const 100000)
				)
			)
		end
	)
)
"#;

	#[test]
	fn contract_out_of_gas() {
		let code_loop = wabt::wat2wasm(CODE_LOOP).unwrap();

		let mut mock_ext = MockExt::default();

		assert_matches!(
			execute(&code_loop, &mut mock_ext, 900_000),
			Err(_)
		);
		assert_matches!(
			execute(&code_loop, &mut mock_ext, 937_000),
			Ok(_)
		);
	}

	const CODE_MEM: &str =
r#"
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
			execute(&code_mem, &mut mock_ext, 100_000),
			Err(_)
		);
	}
}
