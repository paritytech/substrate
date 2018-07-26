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
//! Contracts are able to create other contracts, transfer funds
//! to each other and operate on a simple key-value storage.

use codec::Decode;
use parity_wasm::elements::{self, External, MemoryType, Type, FunctionType};
use pwasm_utils;
use pwasm_utils::rules;
use rstd::prelude::*;
use rstd::collections::BTreeMap;
use sandbox;
use gas::{GasMeter, GasMeterResult};
use runtime_primitives::traits::{As, CheckedMul};
use {Trait};
use exec::{CallReceipt, CreateReceipt};
use system;
use staking;

type BalanceOf<T> = <T as staking::Trait>::Balance;
type AccountIdOf<T> = <T as system::Trait>::AccountId;

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

	// TODO: Return the address of the created contract.
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
	) -> Result<CallReceipt, ()>;
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

/// Enumerates all possible *special* trap conditions.
///
/// In this runtime traps used not only for signaling about errors but also
/// to just terminate quickly in some cases.
enum SpecialTrap {
	// TODO: Can we pass wrapped memory instance instead of copying?
	/// Signals that trap was generated in response to call `ext_return` host function.
	Return(Vec<u8>),
}

struct Runtime<'a, E: Ext + 'a> {
	ext: &'a mut E,
	config: &'a Config<E::T>,
	memory: sandbox::Memory,
	gas_meter: &'a mut GasMeter<E::T>,
	special_trap: Option<SpecialTrap>,
}
impl<'a, E: Ext + 'a> Runtime<'a, E> {
	fn memory(&self) -> &sandbox::Memory {
		&self.memory
	}
	/// Save a data buffer as a result of the execution.
	///
	/// This function also charges gas for the returning.
	///
	/// Returns `Err` if there is not enough gas.
	fn store_return_data(&mut self, data: Vec<u8>) -> Result<(), ()> {
		let data_len = <<<E as Ext>::T as Trait>::Gas as As<u64>>::sa(data.len() as u64);
		let price = (self.config.return_data_per_byte_cost)
			.checked_mul(&data_len)
			.ok_or_else(|| ())?;

		match self.gas_meter.charge(price) {
			GasMeterResult::Proceed => {
				self.special_trap = Some(SpecialTrap::Return(data));
				Ok(())
			}
			GasMeterResult::OutOfGas => Err(()),
		}
	}
}

fn to_execution_result<E: Ext>(
	runtime: Runtime<E>,
	run_err: Option<sandbox::Error>,
) -> Result<ExecutionResult, Error> {
	// Check the exact type of the error. It could be plain trap or
	// special runtime trap the we must recognize.
	let return_data = match (run_err, runtime.special_trap) {
		// No traps were generated. Proceed normally.
		(None, None) => Vec::new(),
		// Special case. The trap was the result of the execution `return` host function.
		(Some(sandbox::Error::Execution), Some(SpecialTrap::Return(rd))) => rd,
		// Any other kind of a trap should result in a failure.
		(Some(_), _) => return Err(Error::Invoke),
		// Any other case (such as special trap flag without actual trap) signifies
		// a logic error.
		_ => unreachable!(),
	};

	Ok(ExecutionResult {
		return_data,
	})
}

/// The result of execution of a smart-contract.
#[derive(PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct ExecutionResult {
	/// The result produced by the execution of the contract.
	///
	/// The contract can designate some buffer at the execution time via a special function.
	/// If contract called this function with non-empty buffer it will be copied here.
	///
	/// Note that gas is already charged for returning the data.
	pub return_data: Vec<u8>,
}

// ext_gas(amount: u32)
//
// Account for used gas. Traps if gas used is greater than gas limit.
//
// - amount: How much gas is used.
fn ext_gas<E: Ext>(
	e: &mut Runtime<E>,
	args: &[sandbox::TypedValue],
) -> Result<sandbox::ReturnValue, sandbox::HostError> {
	let amount = args[0].as_i32().unwrap() as u32;
	let amount = <<<E as Ext>::T as Trait>::Gas as As<u32>>::sa(amount);

	match e.gas_meter.charge(amount) {
		GasMeterResult::Proceed => Ok(sandbox::ReturnValue::Unit),
		GasMeterResult::OutOfGas => Err(sandbox::HostError),
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
fn ext_set_storage<E: Ext>(
	e: &mut Runtime<E>,
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
	e.ext.set_storage(&location, value);

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
fn ext_get_storage<E: Ext>(
	e: &mut Runtime<E>,
	args: &[sandbox::TypedValue],
) -> Result<sandbox::ReturnValue, sandbox::HostError> {
	let location_ptr = args[0].as_i32().unwrap() as u32;
	let dest_ptr = args[1].as_i32().unwrap() as u32;

	let mut location = [0; 32];
	e.memory().get(location_ptr, &mut location)?;

	if let Some(value) = e.ext.get_storage(&location) {
		e.memory().set(dest_ptr, &value)?;
	} else {
		e.memory().set(dest_ptr, &[0u8; 32])?;
	}

	Ok(sandbox::ReturnValue::Unit)
}

// ext_transfer(transfer_to: u32, transfer_to_len: u32, value_ptr: u32, value_len: u32)
fn ext_transfer<E: Ext>(
	e: &mut Runtime<E>,
	args: &[sandbox::TypedValue],
) -> Result<sandbox::ReturnValue, sandbox::HostError> {
	let transfer_to_ptr = args[0].as_i32().unwrap() as u32;
	let transfer_to_len = args[1].as_i32().unwrap() as u32;
	let value_ptr = args[2].as_i32().unwrap() as u32;
	let value_len = args[3].as_i32().unwrap() as u32;

	let mut transfer_to = Vec::new();
	transfer_to.resize(transfer_to_len as usize, 0);
	e.memory().get(transfer_to_ptr, &mut transfer_to)?;
	let transfer_to = <<E as Ext>::T as system::Trait>::AccountId::decode(&mut &transfer_to[..]).unwrap();

	let mut value_buf = Vec::new();
	value_buf.resize(value_len as usize, 0);
	e.memory().get(value_ptr, &mut value_buf)?;
	let value = BalanceOf::<<E as Ext>::T>::decode(&mut &value_buf[..]).unwrap();

	// TODO: Read input data from memory.
	let input_data = Vec::new();

	// TODO: Let user to choose how much gas to allocate for the execution.
	let nested_gas_limit = e.gas_meter.gas_left();
	let ext = &mut e.ext;
	let call_outcome = e.gas_meter.with_nested(nested_gas_limit, |nested_meter| {
		match nested_meter {
			Some(nested_meter) => ext.call(&transfer_to, value, nested_meter, &input_data),
			// there is not enough gas to allocate for the nested call.
			None => Err(()),
		}
	});

	match call_outcome {
		// TODO: Find a way how to pass return_data back to the this sandbox.
		Ok(CallReceipt { .. }) => Ok(sandbox::ReturnValue::Unit),
		// TODO: Return a status code value that can be handled by the caller instead of a trap.
		Err(_) => Err(sandbox::HostError),
	}
}

// ext_create(code_ptr: u32, code_len: u32, value_ptr: u32, value_len: u32)
fn ext_create<E: Ext>(
	e: &mut Runtime<E>,
	args: &[sandbox::TypedValue],
) -> Result<sandbox::ReturnValue, sandbox::HostError> {
	let code_ptr = args[0].as_i32().unwrap() as u32;
	let code_len = args[1].as_i32().unwrap() as u32;
	let value_ptr = args[2].as_i32().unwrap() as u32;
	let value_len = args[3].as_i32().unwrap() as u32;

	let mut value_buf = Vec::new();
	value_buf.resize(value_len as usize, 0);
	e.memory().get(value_ptr, &mut value_buf)?;
	let value = BalanceOf::<<E as Ext>::T>::decode(&mut &value_buf[..]).unwrap();

	let mut code = Vec::new();
	code.resize(code_len as usize, 0u8);
	e.memory().get(code_ptr, &mut code)?;

	// TODO: Read input data from the sandbox.
	let input_data = Vec::new();

	// TODO: Let user to choose how much gas to allocate for the execution.
	let nested_gas_limit = e.gas_meter.gas_left();
	let ext = &mut e.ext;
	let create_outcome = e.gas_meter.with_nested(nested_gas_limit, |nested_meter| {
		match nested_meter {
			Some(nested_meter) => ext.create(&code, value, nested_meter, &input_data),
			// there is not enough gas to allocate for the nested call.
			None => Err(()),
		}
	});

	match create_outcome {
		// TODO: Copy an address of the created contract in the sandbox.
		Ok(CreateReceipt { .. }) => Ok(sandbox::ReturnValue::Unit),
		// TODO: Return a status code value that can be handled by the caller instead of a trap.
		Err(_) => Err(sandbox::HostError),
	}
}

// ext_return(data_ptr: u32, data_len: u32) -> !
fn ext_return<E: Ext>(
	e: &mut Runtime<E>,
	args: &[sandbox::TypedValue],
) -> Result<sandbox::ReturnValue, sandbox::HostError> {
	let data_ptr = args[0].as_i32().unwrap() as u32;
	let data_len = args[1].as_i32().unwrap() as u32;

	let mut data_buf = Vec::new();
	data_buf.resize(data_len as usize, 0);
	e.memory().get(data_ptr, &mut data_buf)?;

	e.store_return_data(data_buf)
		.map_err(|_| sandbox::HostError)?;

	// The trap mechanism is used to immediately terminate the execution.
	// This trap should be handled appropriately before returning the result
	// to the user of this crate.
	Err(sandbox::HostError)
}

// trait Param {
// 	fn new(&sandbox::TypedValue) -> Self;
// }

// trait Params {
// 	fn new(&[sandbox::TypedValue]) -> Self;
// }

// impl Params for () {
// 	fn new(_args: &[sandbox::TypedValue]) -> Self { () }
// }

// impl<A1: Param, A2: Param> Params for (A1, A2) {
// 	fn new(args: &[sandbox::TypedValue]) -> Self {
// 		assert!(args.len() == 2);
// 		let a1 = A1::new(&args[0]);
// 		let a2 = A2::new(&args[1]);
// 		(a1, a2)
// 	}
// }

// impl<A1: Param, A2: Param, A3: Param> Params for (A1, A2, A3) {
// 	fn new(args: &[sandbox::TypedValue]) -> Self {
// 		assert!(args.len() == 3);
// 		let a1 = A1::new(&args[0]);
// 		let a2 = A2::new(&args[1]);
// 		let a3 = A3::new(&args[2]);
// 		(a1, a2, a3)
// 	}
// }

// trait ExternalFunction<E: Ext> {
// 	type Result;

// 	/// Something that can be created from &[TypedValue]
// 	/// + something that can be compared to a parity-wasm's signature
// 	type Params: Params;

// 	/// Logic that will be executed upon a call.
// 	fn call(e: &mut Runtime<E>, params: Self::Params) -> Result<Self::Result, sandbox::HostError>;
// 	fn signature() -> FunctionType;
// }

// fn ext_wrapper<E: Ext, F: ExternalFunction<E>>(
// 	e: &mut Runtime<E>,
// 	args: &[sandbox::TypedValue],
// ) -> Result<sandbox::ReturnValue, sandbox::HostError> {
// 	let args = F::Params::new(args);
// 	let result = F::call(e, args);
// 	panic!()
// }

struct ExtFunc<E: Ext> {
	f: fn(&mut Runtime<E>, &[sandbox::TypedValue]) -> Result<sandbox::ReturnValue, sandbox::HostError>,
	func_type: FunctionType,
}

impl<E: Ext> ExtFunc<E> {
	fn type_matches(&self, func_type: &FunctionType) -> bool {
		panic!()
	}
}

struct ExtFunctions<E: Ext> {
	funcs: BTreeMap<String, ExtFunc<E>>,
}

/// Execute the given code as a contract.
pub fn execute<'a, E: Ext>(
	code: &[u8],
	ext: &'a mut E,
	gas_meter: &mut GasMeter<E::T>,
) -> Result<ExecutionResult, Error> {
	// TODO: Receive data as an argument

	let config = Config::default();

	let PreparedContract {
		instrumented_code,
		memory,
	} = prepare_contract(code, &config)?;

	let mut imports = sandbox::EnvironmentDefinitionBuilder::new();
	imports.add_host_func("env", "gas", ext_gas::<E>);
	imports.add_host_func("env", "ext_set_storage", ext_set_storage::<E>);
	imports.add_host_func("env", "ext_get_storage", ext_get_storage::<E>);
	// TODO: Rename it to ext_call.
	imports.add_host_func("env", "ext_transfer", ext_transfer::<E>);
	imports.add_host_func("env", "ext_create", ext_create::<E>);
	imports.add_host_func("env", "ext_return", ext_return::<E>);
	// TODO: ext_balance, ext_address, ext_callvalue, etc.
	imports.add_memory("env", "memory", memory.clone());

	let mut runtime = Runtime {
		ext,
		config: &config,
		memory,
		gas_meter,
		special_trap: None,
	};

	let mut instance = sandbox::Instance::new(&instrumented_code, &imports, &mut runtime)
		.map_err(|_| Error::Instantiate)?;

	let run_result = instance.invoke(b"call", &[], &mut runtime);

	to_execution_result(runtime, run_result.err())
}

// TODO: Extract it to the root of the crate
#[derive(Clone)]
struct Config<T: Trait> {
	/// Gas cost of a growing memory by single page.
	grow_mem_cost: T::Gas,

	/// Gas cost of a regular operation.
	regular_op_cost: T::Gas,

	/// Gas cost per one byte returned.
	return_data_per_byte_cost: T::Gas,

	/// How tall the stack is allowed to grow?
	///
	/// See https://wiki.parity.io/WebAssembly-StackHeight to find out
	/// how the stack frame cost is calculated.
	max_stack_height: u32,

	//// What is the maximal memory pages amount is allowed to have for
	/// a contract.
	max_memory_pages: u32,
}

impl<T: Trait> Default for Config<T> {
	fn default() -> Config<T> {
		Config {
			grow_mem_cost: T::Gas::sa(1),
			regular_op_cost: T::Gas::sa(1),
			return_data_per_byte_cost: T::Gas::sa(1),
			max_stack_height: 64 * 1024,
			max_memory_pages: 16,
		}
	}
}

struct ContractModule<'a, T: Trait + 'a> {
	// An `Option` is used here for loaning (`take()`-ing) the module.
	// Invariant: Can't be `None` (i.e. on enter and on exit from the function
	// the value *must* be `Some`).
	module: Option<elements::Module>,
	config: &'a Config<T>,
}

impl<'a, T: Trait> ContractModule<'a, T> {
	fn new(original_code: &[u8], config: &'a Config<T>) -> Result<ContractModule<'a, T>, Error> {
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
		let module = self
			.module
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
		let gas_rules = rules::Set::new(self.config.regular_op_cost.as_(), Default::default())
			.with_grow_cost(self.config.grow_mem_cost.as_())
			.with_forbidden_floats();

		let module = self
			.module
			.take()
			.expect("On entry to the function `module` can't be `None`; qed");

		let contract_module = pwasm_utils::inject_gas_counter(module, &gas_rules)
			.map_err(|_| Error::GasInstrumentation)?;

		self.module = Some(contract_module);
		Ok(())
	}

	fn inject_stack_height_metering(&mut self) -> Result<(), Error> {
		let module = self
			.module
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
		let import_section = self
			.module
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

	fn check_signatures(&self) -> Result<(), Error> {
		// TODO: Merge it with `find_mem_import`?
		let module = self
			.module
			.as_ref()
			.expect("On entry to the function `module` can't be `None`; qed");

		let types = module.type_section().map(|ts| ts.types()).unwrap_or(&[]);
		let import_entries = module.import_section().map(|is| is.entries()).unwrap_or(&[]);

		for import in import_entries {
			if let ("env", "memory", &External::Function(ref type_index)) =
				(import.module(), import.field(), import.external())
			{
				let Type::Function(ref func_ty) = types
					.get(*type_index as usize)
					.ok_or_else(|| Error::Deserialization)?;


			}
		}
		Ok(())
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

fn prepare_contract<T: Trait>(original_code: &[u8], config: &Config<T>) -> Result<PreparedContract, Error> {
	let mut contract_module = ContractModule::new(original_code, config)?;
	contract_module.ensure_no_internal_memory()?;
	contract_module.inject_gas_metering()?;
	contract_module.inject_stack_height_metering()?;

	// Inspect the module to extract the initial and maximum page count.
	let memory = if let Some(memory_type) = contract_module.find_mem_import() {
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
				return Err(Error::Memory);
			}
			(initial, maximum) => sandbox::Memory::new(initial, maximum),
		}
	} else {
		// If none memory imported then just crate an empty placeholder.
		// Any access to it will lead to out of bounds trap.
		sandbox::Memory::new(0, Some(0))
	};
	let memory = memory.map_err(|_| Error::Memory)?;

	Ok(PreparedContract {
		instrumented_code: contract_module.into_wasm_code()?,
		memory,
	})
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::collections::HashMap;
	use std::fmt;
	use wabt;
	use gas::GasMeter;
	use ::tests::Test;

	#[derive(Debug, PartialEq, Eq)]
	struct CreateEntry {
		code: Vec<u8>,
		endowment: u64,
		data: Vec<u8>,
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
			_gas_meter: &mut GasMeter<Test>,
			data: &[u8],
		) -> Result<CreateReceipt<Test>, ()> {
			self.creates.push(CreateEntry {
				code: code.to_vec(),
				endowment,
				data: data.to_vec(),
			});
			let address = self.next_account_id;
			self.next_account_id += 1;

			Ok(CreateReceipt {
				address,
			})
		}
		fn call(
			&mut self,
			to: &u64,
			value: u64,
			_gas_meter: &mut GasMeter<Test>,
			_data: &[u8],
		) -> Result<CallReceipt, ()> {
			self.transfers.push(TransferEntry { to: *to, value });
			// Assume for now that it was just a plain transfer.
			// TODO: Add tests for different call outcomes.
			Ok(CallReceipt {
				return_data: Vec::new(),
			})
		}
	}

	impl fmt::Debug for PreparedContract {
		fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
			write!(f, "PreparedContract {{ .. }}")
		}
	}

	fn parse_and_prepare_wat(wat: &str) -> Result<PreparedContract, Error> {
		let wasm = wabt::Wat2Wasm::new().validate(false).convert(wat).unwrap();
		let config = Config::<Test>::default();
		prepare_contract(wasm.as_ref(), &config)
	}

	#[test]
	fn internal_memory_declaration() {
		let r = parse_and_prepare_wat(r#"(module (memory 1 1))"#);
		assert_matches!(r, Err(Error::InternalMemoryDeclared));
	}

	#[test]
	fn memory() {
		// This test assumes that maximum page number is configured to a certain number.
		assert_eq!(Config::<Test>::default().max_memory_pages, 16);

		let r = parse_and_prepare_wat(r#"(module (import "env" "memory" (memory 1 1)))"#);
		assert_matches!(r, Ok(_));

		// No memory import
		let r = parse_and_prepare_wat(r#"(module)"#);
		assert_matches!(r, Ok(_));

		// incorrect import name. That's kinda ok, since this will fail
		// at later stage when imports will be resolved.
		let r = parse_and_prepare_wat(r#"(module (import "vne" "memory" (memory 1 1)))"#);
		assert_matches!(r, Ok(_));

		// initial exceed maximum
		let r = parse_and_prepare_wat(r#"(module (import "env" "memory" (memory 16 1)))"#);
		assert_matches!(r, Err(Error::Memory));

		// no maximum
		let r = parse_and_prepare_wat(r#"(module (import "env" "memory" (memory 1)))"#);
		assert_matches!(r, Err(Error::Memory));

		// requested maximum exceed configured maximum
		let r = parse_and_prepare_wat(r#"(module (import "env" "memory" (memory 1 17)))"#);
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
		execute(&code_transfer, &mut mock_ext, &mut GasMeter::with_limit(50_000, 1)).unwrap();

		assert_eq!(&mock_ext.transfers, &[TransferEntry { to: 2, value: 6 }]);
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
			execute(&code_mem, &mut mock_ext, &mut GasMeter::with_limit(100_000, 1)),
			Err(_)
		);
	}
}
