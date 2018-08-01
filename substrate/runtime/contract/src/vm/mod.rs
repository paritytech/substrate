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

use exec::{CallReceipt, CreateReceipt};
use gas::{GasMeter, GasMeterResult};
use rstd::prelude::*;
use runtime_primitives::traits::{As, CheckedMul};
use sandbox;
use staking;
use system;
use Trait;

type BalanceOf<T> = <T as staking::Trait>::Balance;
type AccountIdOf<T> = <T as system::Trait>::AccountId;

mod prepare;

#[macro_use]
mod env_def;

use self::prepare::{prepare_contract, PreparedContract};

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

pub(crate) struct Runtime<'a, E: Ext + 'a> {
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

	Ok(ExecutionResult { return_data })
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

/// Execute the given code as a contract.
pub fn execute<'a, E: Ext>(
	code: &[u8],
	ext: &'a mut E,
	gas_meter: &mut GasMeter<E::T>,
) -> Result<ExecutionResult, Error> {
	// TODO: Receive data as an argument

	let config = Config::default();
	let env = env_def::init_env();

	let PreparedContract {
		instrumented_code,
		memory,
	} = prepare_contract(code, &config, &env)?;

	let mut imports = sandbox::EnvironmentDefinitionBuilder::new();
	for (func_name, ext_func) in &env.funcs {
		imports.add_host_func("env", &func_name[..], ext_func.raw_fn_ptr());
	}
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
	}
	#[derive(Debug, PartialEq, Eq)]
	struct TransferEntry {
		to: u64,
		value: u64,
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

			Ok(CreateReceipt { address })
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
		execute(
			&code_transfer,
			&mut mock_ext,
			&mut GasMeter::with_limit(50_000, 1),
		).unwrap();

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
			execute(
				&code_mem,
				&mut mock_ext,
				&mut GasMeter::with_limit(100_000, 1)
			),
			Err(_)
		);
	}
}
