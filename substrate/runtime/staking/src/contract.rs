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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Smart-contract execution module.

// TODO: Extract to it's own crate?

use codec::Slicable;
use rstd::prelude::*;
use sandbox;
use {AccountDb, Module, OverlayAccountDb, Trait};

use parity_wasm::elements::{self, External, MemoryType};
use pwasm_utils;
use pwasm_utils::rules;

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

struct ExecutionExt<'a, 'b: 'a, T: Trait + 'b> {
	account_db: &'a mut OverlayAccountDb<'b, T>,
	account: T::AccountId,
	memory: sandbox::Memory,
	gas_used: u64,
	gas_limit: u64,
}
impl<'a, 'b: 'a, T: Trait> ExecutionExt<'a, 'b, T> {
	fn account(&self) -> &T::AccountId {
		&self.account
	}
	fn account_db(&self) -> &OverlayAccountDb<T> {
		self.account_db
	}
	fn account_db_mut(&mut self) -> &mut OverlayAccountDb<'b, T> {
		self.account_db
	}
	fn memory(&self) -> &sandbox::Memory {
		&self.memory
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

pub(crate) fn execute<'a, 'b: 'a, T: Trait>(
	code: &[u8],
	account: &T::AccountId,
	account_db: &'a mut OverlayAccountDb<'b, T>,
	gas_limit: u64,
) -> Result<(), Error> {
	// ext_gas(amount: u32)
	//
	// Account for used gas. Traps if gas used is greater than gas limit.
	//
	// - amount: How much gas is used.
	fn ext_gas<T: Trait>(e: &mut ExecutionExt<T>, args: &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError> {
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
	fn ext_set_storage<T: Trait>(e: &mut ExecutionExt<T>, args: &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError> {
		let location_ptr = args[0].as_i32().unwrap() as u32;
		let value_non_null = args[1].as_i32().unwrap() as u32;
		let value_ptr = args[2].as_i32().unwrap() as u32;

		let mut location = [0; 32];

		e.memory().get(location_ptr, &mut location)?;
		let account = e.account().clone();

		if value_non_null != 0 {
			let mut value = [0; 32];
			e.memory().get(value_ptr, &mut value)?;
			e.account_db_mut()
				.set_storage(&account, location.to_vec(), Some(value.to_vec()));
		} else {
			e.account_db_mut()
				.set_storage(&account, location.to_vec(), None);
		}

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
	fn ext_get_storage<T: Trait>(e: &mut ExecutionExt<T>, args: &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError> {
		let location_ptr = args[0].as_i32().unwrap() as u32;
		let dest_ptr = args[1].as_i32().unwrap() as u32;

		let mut location = [0; 32];
		e.memory().get(location_ptr, &mut location)?;

		let account = e.account().clone();
		if let Some(value) = e.account_db_mut().get_storage(&account, &location) {
			e.memory().set(dest_ptr, &value)?;
		} else {
			e.memory().set(dest_ptr, &[0u8; 32])?;
		}

		Ok(sandbox::ReturnValue::Unit)
	}

	// ext_transfer(transfer_to: u32, transfer_to_len: u32, value: u32)
	fn ext_transfer<T: Trait>(e: &mut ExecutionExt<T>, args: &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError> {
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

		let account = e.account().clone();
		if let Some(commit_state) =
			Module::<T>::effect_transfer(&account, &transfer_to, value, e.account_db())
				.map_err(|_| sandbox::Error::Execution)?
		{
			e.account_db_mut().merge(commit_state);
		}

		Ok(sandbox::ReturnValue::Unit)
	}

	// ext_create(code_ptr: u32, code_len: u32, value: u32)
	fn ext_create<T: Trait>(e: &mut ExecutionExt<T>, args: &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError> {
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

		let account = e.account().clone();
		if let Some(commit_state) =
			Module::<T>::effect_create(&account, &code, value, e.account_db())
				.map_err(|_| sandbox::Error::Execution)?
		{
			e.account_db_mut().merge(commit_state);
		}

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

	let mut exec_ext = ExecutionExt {
		account: account.clone(),
		account_db,
		memory,
		gas_limit,
		gas_used: 0,
	};

	let mut instance =
		sandbox::Instance::new(&instrumented_code, &imports, &mut exec_ext)
			.map_err(|_| Error::Instantiate)?;
	instance
		.invoke(b"call", &[], &mut exec_ext)
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
	use runtime_io::with_externalities;
	use mock::{Staking, Test, new_test_ext};
	use ::{CodeOf, ContractAddressFor, DirectAccountDb, FreeBalance, StorageMap};

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

		with_externalities(&mut new_test_ext(1, 3, 1, false), || {
			<FreeBalance<Test>>::insert(0, 111);
			<FreeBalance<Test>>::insert(1, 0);
			<FreeBalance<Test>>::insert(2, 30);

			<CodeOf<Test>>::insert(1, code_transfer.to_vec());

			Staking::transfer(&0, 1, 11);

			assert_eq!(Staking::balance(&0), 100);
			assert_eq!(Staking::balance(&1), 5);
			assert_eq!(Staking::balance(&2), 36);
		});
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

		with_externalities(&mut new_test_ext(1, 3, 1, false), || {
			<FreeBalance<Test>>::insert(0, 111);
			<FreeBalance<Test>>::insert(1, 0);

			<CodeOf<Test>>::insert(1, code_create.to_vec());

			// When invoked, the contract at address `1` must create a contract with 'transfer' code.
			Staking::transfer(&0, 1, 11);

			let derived_address =
				<Test as Trait>::DetermineContractAddress::contract_address_for(&code_transfer, &1);

			assert_eq!(Staking::balance(&0), 100);
			assert_eq!(Staking::balance(&1), 8);
			assert_eq!(Staking::balance(&derived_address), 3);
		});
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

		with_externalities(&mut new_test_ext(1, 3, 1, false), || {
			<FreeBalance<Test>>::insert(0, 111);
			<FreeBalance<Test>>::insert(1, 0);
			<CodeOf<Test>>::insert(1, code_adder);

			Staking::transfer(&0, 1, 1);
			Staking::transfer(&0, 1, 1);

			let storage_addr = [0x01u8; 32];
			let value =
				AccountDb::<Test>::get_storage(&DirectAccountDb, &1, &storage_addr).unwrap();

			assert_eq!(
				&value,
				&[
					2, 0, 0, 0, 0, 0, 0, 0,
					0, 0, 0, 0, 0, 0, 0, 0,
					0, 0, 0, 0, 0, 0, 0, 0,
					0, 0, 0, 0, 0, 0, 0, 0,
				]
			);
		});
	}

	// This code should make 100_000 iterations so it should
	// consume more than 100_000 units of gas.
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

		with_externalities(&mut new_test_ext(1, 3, 1, false), || {
			// Set initial balances.
			<FreeBalance<Test>>::insert(0, 111);
			<FreeBalance<Test>>::insert(1, 0);

			<CodeOf<Test>>::insert(1, code_loop.to_vec());

			// Transfer some balance from 0 to 1. This will trigger execution
			// of the smart-contract code at address 1.
			Staking::transfer(&0, 1, 11);

			// The balance should remain unchanged since we are expecting
			// out-of-gas error which will revert transfer.
			assert_eq!(Staking::balance(&0), 111);
		});
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

		with_externalities(&mut new_test_ext(1, 3, 1, false), || {
			// Set initial balances.
			<FreeBalance<Test>>::insert(0, 111);
			<FreeBalance<Test>>::insert(1, 0);

			<CodeOf<Test>>::insert(1, code_mem.to_vec());

			// Transfer some balance from 0 to 1.
			Staking::transfer(&0, 1, 11);

			// The balance should remain unchanged since we are expecting
			// validation error caused by internal memory declaration.
			assert_eq!(Staking::balance(&0), 111);
		});
	}
}
