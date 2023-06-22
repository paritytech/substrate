// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! This module takes care of loading, checking and preprocessing of a
//! wasm module before execution. It also extracts some essential information
//! from a module.

use crate::{
	chain_extension::ChainExtension,
	ensure,
	storage::meter::Diff,
	wasm::{runtime::AllowDeprecatedInterface, CodeInfo, Determinism, Environment, WasmBlob},
	AccountIdOf, CodeVec, Config, Error, Schedule, LOG_TARGET,
};
use codec::MaxEncodedLen;
use sp_runtime::DispatchError;
use sp_std::prelude::*;
use wasmi::{
	core::ValueType, Config as WasmiConfig, Engine, ExternType, FuelConsumptionMode, Module,
	StackLimits,
};

/// Imported memory must be located inside this module. The reason for hardcoding is that current
/// compiler toolchains might not support specifying other modules than "env" for memory imports.
pub const IMPORT_MODULE_MEMORY: &str = "env";
const BYTES_PER_PAGE: usize = 64 * 1024;

/// Determines whether a module should be instantiated during preparation.
pub enum TryInstantiate {
	/// Do the instantiation to make sure that the module is valid.
	///
	/// This should be used if a module is only uploaded but not executed. We need
	/// to make sure that it can be actually instantiated.
	Instantiate,
	/// Skip the instantiation during preparation.
	///
	/// This makes sense when the preparation takes place as part of an instantiation. Then
	/// this instantiation would fail the whole transaction and an extra check is not
	/// necessary.
	Skip,
}

/// The inner deserialized module is valid and contains only allowed WebAssembly features.
/// This is checked by loading it into wasmi interpreter `engine`.
pub struct LoadedModule {
	pub module: Module,
	pub engine: Engine,
}

impl LoadedModule {
	/// Creates a new instance of `LoadedModule`.
	///
	/// The inner Wasm module is checked not the have restricted WebAssembly proposals.
	/// Returns `Err` if the `code` cannot be deserialized or if it contains an invalid module.
	pub fn new<T>(
		code: &[u8],
		determinism: Determinism,
		stack_limits: Option<StackLimits>,
	) -> Result<Self, &'static str> {
		// Do not enable any features here. Any additional feature needs to be carefully
		// checked for potential security issues. For example, enabling multi value could lead
		// to a DoS vector: It breaks our assumption that branch instructions are of constant time.
		// Depending on the implementation they can linearly depend on the amount of values returned
		// from a block.
		//
		// NOTE: wasmi does not support unstable WebAssembly features. The module is implicitly
		// checked for not having those ones when creating `wasmi::Module` below.
		let mut config = WasmiConfig::default();
		config
			.wasm_multi_value(false)
			.wasm_mutable_global(false)
			.wasm_sign_extension(false)
			.wasm_bulk_memory(false)
			.wasm_reference_types(false)
			.wasm_tail_call(false)
			.wasm_extended_const(false)
			.wasm_saturating_float_to_int(false)
			// This is not our only defense: All instructions explicitly need to have weights
			// assigned or the deployment will fail. We have none assigned for float instructions.
			.floats(matches!(determinism, Determinism::Relaxed))
			.consume_fuel(true)
			.fuel_consumption_mode(FuelConsumptionMode::Eager);

		if let Some(stack_limits) = stack_limits {
			config.set_stack_limits(stack_limits);
		}

		let engine = Engine::new(&config);
		let module =
			Module::new(&engine, code.clone()).map_err(|_| "Validation of new code failed!")?;

		// Return a `LoadedModule` instance with
		// __valid__ module.
		Ok(LoadedModule { module, engine })
	}

	/// Check that the module has required exported functions. For now
	/// these are just entrypoints:
	///
	/// - 'call'
	/// - 'deploy'
	///
	/// Any other exports are not allowed.
	fn scan_exports(&self) -> Result<(), &'static str> {
		let mut deploy_found = false;
		let mut call_found = false;
		let module = &self.module;
		let exports = module.exports();

		for export in exports {
			match export.ty() {
				ExternType::Func(ft) => {
					match export.name() {
						"call" => call_found = true,
						"deploy" => deploy_found = true,
						_ =>
							return Err(
								"unknown function export: expecting only deploy and call functions",
							),
					}
					// Check the signature.
					// Both "call" and "deploy" has a () -> () function type.
					// We still support () -> (i32) for backwards compatibility.
					if !(ft.params().is_empty() &&
						(ft.results().is_empty() || ft.results() == [ValueType::I32]))
					{
						return Err("entry point has wrong signature")
					}
				},
				ExternType::Memory(_) => return Err("memory export is forbidden"),
				ExternType::Global(_) => return Err("global export is forbidden"),
				ExternType::Table(_) => return Err("table export is forbidden"),
			}
		}

		if !deploy_found {
			return Err("deploy function isn't exported")
		}
		if !call_found {
			return Err("call function isn't exported")
		}

		Ok(())
	}

	/// Scan an import section if any.
	///
	/// This makes sure that the import section looks as we expect it from a contract.
	/// Makes sure the limits of the memory type declared by the contract comply with the Schedule.
	/// Returns the checked memory limits back to caller.
	///
	/// `import_fn_banlist`: list of function names that are disallowed to be imported.
	///
	/// This method fails if:
	///
	/// - banned function found among imports,
	/// - tables or globals found among imports,
	/// - call_chain_extension host function is imported, while chain extensions are disabled,
	/// - no valid memory import found in the module,
	///
	/// NOTE that only single memory instance is allowed for contract modules, which is enforced by
	/// this check combined with multi_memory proposal disabling in the engine.
	pub fn scan_imports<T: Config>(
		&self,
		import_fn_banlist: &[&[u8]],
		schedule: &Schedule<T>,
	) -> Result<(u32, u32), &'static str> {
		let module = &self.module;
		let imports = module.imports();
		let mut memory_limits = None;

		for import in imports {
			match *import.ty() {
				ExternType::Table(_) => return Err("Cannot import tables"),
				ExternType::Global(_) => return Err("Cannot import globals"),
				ExternType::Func(_) => {
					let _ = import.ty().func().ok_or("expected a function")?;
					if !<T as Config>::ChainExtension::enabled() &&
						import.module().as_bytes()[0..4] == b"seal"[0..4] &&
						import.name().as_bytes() == b"seal_call_chain_extension" ||
						import.name().as_bytes() == b"call_chain_extension"
					{
						return Err("module uses chain extensions but chain extensions are disabled")
					}
					if import_fn_banlist.iter().any(|f| import.name().as_bytes() == *f) {
						return Err("module imports a banned function")
					}
				},
				ExternType::Memory(mt) => {
					if import.module().as_bytes() != IMPORT_MODULE_MEMORY.as_bytes() {
						return Err("Invalid module for imported memory")
					}
					if import.name().as_bytes() != b"memory" {
						return Err("Memory import must have the field name 'memory'")
					}
					if memory_limits.is_some() {
						return Err("Multiple memory imports defined")
					}
					// Parse memory limits defaulting it to (0,0).
					// Any access to it will then lead to out of bounds trap.
					let (initial, maximum) = (
						mt.initial_pages().to_bytes().unwrap_or(0).saturating_div(BYTES_PER_PAGE)
							as u32,
						mt.maximum_pages().map_or(schedule.limits.memory_pages, |p| {
							p.to_bytes().unwrap_or(0).saturating_div(BYTES_PER_PAGE) as u32
						}),
					);
					if initial > maximum {
						return Err(
						"Requested initial number of memory pages should not exceed the requested maximum",
					)
					}
					if maximum > schedule.limits.memory_pages {
						return Err("Maximum number of memory pages should not exceed the maximum configured in the Schedule.")
					}

					memory_limits = Some((initial, maximum));
					continue
				},
			}
		}

		memory_limits.ok_or("No memory import found in the module")
	}
}

/// Check that given `code` satisfies constraints required for the contract Wasm module.
/// This includes two groups of checks:
///
/// 1. General engine-side validation makes sure the module is consistent and does not contain
///    forbidden WebAssembly features.
/// 2. Additional checks which are specific to smart contracts eligible for this pallet.
///
/// On success it returns back the code.
fn validate<E, T>(
	code: &[u8],
	schedule: &Schedule<T>,
	determinism: Determinism,
	try_instantiate: TryInstantiate,
) -> Result<Vec<u8>, (DispatchError, &'static str)>
where
	E: Environment<()>,
	T: Config,
{
	let code = (|| {
		// We check that the module is generally valid,
		// and does not have restricted WebAssembly features, here.
		let contract_module = LoadedModule::new::<T>(code, determinism, None)?;
		// Checks that module satisfies constraints required for contracts.
		contract_module.scan_exports()?;
		contract_module.scan_imports::<T>(&[], schedule)?;
		Ok(code.to_vec())
	})()
	.map_err(|msg: &str| {
		log::debug!(target: LOG_TARGET, "New code rejected: {}", msg);
		(Error::<T>::CodeRejected.into(), msg)
	})?;

	// This will make sure that the module can be actually run within wasmi:
	//
	// - It doesn't use any unknown imports.
	// - It doesn't explode the wasmi bytecode generation.
	if matches!(try_instantiate, TryInstantiate::Instantiate) {
		// We don't actually ever run any code so we can get away with a minimal stack which
		// reduces the amount of memory that needs to be zeroed.
		let stack_limits = StackLimits::new(1, 1, 0).expect("initial <= max; qed");
		WasmBlob::<T>::instantiate::<E, _>(
			&code,
			(),
			schedule,
			stack_limits,
			AllowDeprecatedInterface::No,
		)
		.map_err(|err| {
			log::debug!(target: LOG_TARGET, "{}", err);
			(Error::<T>::CodeRejected.into(), "New code rejected on wasmi instantiation!")
		})?;
	}

	Ok(code)
}

/// Validates the given binary `code` is a valid Wasm module satisfying following constraints:
///
/// - The module doesn't export any memory.
/// - The module imports memory, which limits lay within the limits permitted by the `schedule`.
/// - All imported functions from the external environment match defined by `env` module.
///
/// Also constructs contract `code_info` by calculating the storage deposit.
pub fn prepare<E, T>(
	code: CodeVec<T>,
	schedule: &Schedule<T>,
	owner: AccountIdOf<T>,
	determinism: Determinism,
	try_instantiate: TryInstantiate,
) -> Result<WasmBlob<T>, (DispatchError, &'static str)>
where
	E: Environment<()>,
	T: Config,
{
	let checked_code = validate::<E, T>(code.as_ref(), schedule, determinism, try_instantiate)?;
	let err = |_| (<Error<T>>::CodeTooLarge.into(), "Validation enlarged the code size!");
	let checked_code: CodeVec<T> = checked_code.try_into().map_err(err)?;
	ensure!(
		code == checked_code,
		(<Error<T>>::CodeRejected.into(), "Validation altered the code!")
	);

	// Calculate deposit for storing contract code and `code_info` in two different storage items.
	let bytes_added = code.len().saturating_add(<CodeInfo<T>>::max_encoded_len()) as u32;
	let deposit = Diff { bytes_added, items_added: 2, ..Default::default() }
		.update_contract::<T>(None)
		.charge_or_zero();
	let code_info = CodeInfo { owner, deposit, determinism, refcount: 0 };

	Ok(WasmBlob { code, code_info })
}

/// Alternate (possibly unsafe) preparation functions used only for benchmarking and testing.
///
/// For benchmarking we need to construct special contracts that might not pass our
/// sanity checks. We hide functions allowing this behind a feature that is only set during
/// benchmarking or testing to prevent usage in production code.
#[cfg(any(test, feature = "runtime-benchmarks"))]
pub mod benchmarking {
	use super::*;

	/// Prepare function that does not perform export section checks on the passed in code.
	pub fn prepare<T: Config>(
		code: Vec<u8>,
		schedule: &Schedule<T>,
		owner: AccountIdOf<T>,
	) -> Result<WasmBlob<T>, DispatchError> {
		let determinism = Determinism::Enforced;
		let contract_module = LoadedModule::new(&code, determinism, None)?;
		let _ = contract_module.scan_imports::<T>(&[], schedule)?;
		let code = code.try_into().map_err(|_| <Error<T>>::CodeTooLarge)?;
		let code_info = CodeInfo {
			owner,
			// this is a helper function for benchmarking which skips deposit collection
			deposit: Default::default(),
			refcount: 0,
			determinism,
		};
		Ok(WasmBlob { code, code_info })
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::{
		exec::Ext,
		schedule::Limits,
		tests::{Test, ALICE},
	};
	use pallet_contracts_proc_macro::define_env;
	use std::fmt;

	impl fmt::Debug for WasmBlob<Test> {
		fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
			write!(f, "ContractCode {{ .. }}")
		}
	}

	/// Using unreachable statements triggers unreachable warnings in the generated code
	#[allow(unreachable_code)]
	mod env {
		use super::*;
		use crate::wasm::runtime::{AllowDeprecatedInterface, AllowUnstableInterface, TrapReason};

		// Define test environment for tests. We need ImportSatisfyCheck
		// implementation from it. So actual implementations doesn't matter.
		#[define_env]
		pub mod test_env {
			fn panic(_ctx: _, _memory: _) -> Result<(), TrapReason> {
				Ok(())
			}

			// gas is an implementation defined function and a contract can't import it.
			fn gas(_ctx: _, _memory: _, _amount: u64) -> Result<(), TrapReason> {
				Ok(())
			}

			fn nop(_ctx: _, _memory: _, _unused: u64) -> Result<(), TrapReason> {
				Ok(())
			}

			// new version of nop with other data type for argument
			#[version(1)]
			fn nop(_ctx: _, _memory: _, _unused: i32) -> Result<(), TrapReason> {
				Ok(())
			}
		}
	}

	macro_rules! prepare_test {
		($name:ident, $wat:expr, $($expected:tt)*) => {
			#[test]
			fn $name() {
				let wasm = wat::parse_str($wat).unwrap().try_into().unwrap();
				let schedule = Schedule {
					limits: Limits {
					    globals: 3,
					    locals: 3,
						parameters: 3,
						memory_pages: 16,
						table_size: 3,
						br_table_size: 3,
						.. Default::default()
					},
					.. Default::default()
				};
				let r = prepare::<env::Env, Test>(
					wasm,
					&schedule,
					ALICE,
					Determinism::Enforced,
					TryInstantiate::Instantiate,
				);
				assert_matches::assert_matches!(r.map_err(|(_, msg)| msg), $($expected)*);
			}
		};
	}

	prepare_test!(
		no_floats,
		r#"
		(module
			(func (export "call")
				(drop
					(f32.add
						(f32.const 0)
						(f32.const 1)
					)
				)
			)
			(func (export "deploy"))
		)"#,
		Err("Validation of new code failed!")
	);

	mod functions {
		use super::*;

		prepare_test!(
			param_number_valid,
			r#"
			(module
				(func (export "call"))
				(func (export "deploy"))
				(func (param i32 i32 i32))
			)
			"#,
			Ok(_)
		);

		prepare_test!(
			param_number_invalid,
			r#"
			(module
				(func (export "call"))
				(func (export "deploy"))
				(func (param i32 i32 i32 i32))
				(func (param i32))
			)
			"#,
			Err("Use of a function type with too many parameters.")
		);
	}

	mod globals {
		use super::*;

		prepare_test!(
			global_number_valid,
			r#"
			(module
				(global i64 (i64.const 0))
				(global i64 (i64.const 0))
				(global i64 (i64.const 0))
				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Ok(_)
		);

		prepare_test!(
			global_number_too_high,
			r#"
			(module
				(global i64 (i64.const 0))
				(global i64 (i64.const 0))
				(global i64 (i64.const 0))
				(global i64 (i64.const 0))
				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("module declares too many globals")
		);
	}

	mod locals {
		use super::*;

		prepare_test!(
			local_number_valid,
			r#"
			(module
				(func
					(local i32)
					(local i32)
					(local i32)
				)
				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Ok(_)
		);

		prepare_test!(
			local_number_too_high,
			r#"
			(module
				(func
					(local i32)
					(local i32)
					(local i32)
					(local i32)
				)
				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("single function declares too many locals")
		);
	}

	mod memories {
		use super::*;

		prepare_test!(
			memory_with_one_page,
			r#"
			(module
				(import "env" "memory" (memory 1 1))

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Ok(_)
		);

		prepare_test!(
			internal_memory_declaration,
			r#"
			(module
				(memory 1 1)

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("module declares internal memory")
		);

		prepare_test!(
			no_memory_import,
			r#"
			(module
				;; no memory imported

				(func (export "call"))
				(func (export "deploy"))
			)"#,
			Ok(_)
		);

		prepare_test!(
			initial_exceeds_maximum,
			r#"
			(module
				(import "env" "memory" (memory 16 1))

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("Validation of new code failed!")
		);

		prepare_test!(
			requested_maximum_valid,
			r#"
			(module
				(import "env" "memory" (memory 1 16))

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Ok(_)
		);

		prepare_test!(
			requested_maximum_exceeds_configured_maximum,
			r#"
			(module
				(import "env" "memory" (memory 1 17))

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("New code rejected on wasmi instantiation!")
		);

		prepare_test!(
			field_name_not_memory,
			r#"
			(module
				(import "env" "forgetit" (memory 1 1))

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("New code rejected on wasmi instantiation!")
		);

		prepare_test!(
			multiple_memory_imports,
			r#"
			(module
				(import "env" "memory" (memory 1 1))
				(import "env" "memory" (memory 1 1))

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("Validation of new code failed!")
		);

		prepare_test!(
			table_import,
			r#"
			(module
				(import "seal0" "table" (table 1 anyfunc))

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("New code rejected on wasmi instantiation!")
		);

		prepare_test!(
			global_import,
			r#"
			(module
				(global $g (import "seal0" "global") i32)
				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("New code rejected on wasmi instantiation!")
		);
	}

	mod tables {
		use super::*;

		prepare_test!(
			no_tables,
			r#"
			(module
				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Ok(_)
		);

		prepare_test!(
			table_valid_size,
			r#"
			(module
				(table 3 funcref)

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Ok(_)
		);

		prepare_test!(
			table_too_big,
			r#"
			(module
				(table 4 funcref)

				(func (export "call"))
				(func (export "deploy"))
			)"#,
			Err("table exceeds maximum size allowed")
		);

		prepare_test!(
			br_table_valid_size,
			r#"
			(module
				(func (export "call"))
				(func (export "deploy"))
				(func
					i32.const 0
					br_table 0 0 0 0
				)
			)
			"#,
			Ok(_)
		);

		prepare_test!(
			br_table_too_big,
			r#"
			(module
				(func (export "call"))
				(func (export "deploy"))
				(func
					i32.const 0
					br_table 0 0 0 0 0
				)
			)"#,
			Err("BrTable's immediate value is too big.")
		);
	}

	mod imports {
		use super::*;

		prepare_test!(
			can_import_legit_function,
			r#"
			(module
				(import "seal0" "nop" (func (param i64)))

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Ok(_)
		);

		// memory is in "env" and not in "seal0"
		prepare_test!(
			memory_not_in_seal0,
			r#"
			(module
				(import "seal0" "memory" (memory 1 1))

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("New code rejected on wasmi instantiation!")
		);

		// memory is in "env" and not in some arbitrary module
		prepare_test!(
			memory_not_in_arbitrary_module,
			r#"
			(module
				(import "any_module" "memory" (memory 1 1))

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("New code rejected on wasmi instantiation!")
		);

		prepare_test!(
			function_in_other_module_works,
			r#"
			(module
				(import "seal1" "nop" (func (param i32)))

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Ok(_)
		);

		prepare_test!(
			unknown_func_name,
			r#"
			(module
				(import "seal0" "unknown_func" (func))

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("New code rejected on wasmi instantiation!")
		);
	}

	mod entrypoints {
		use super::*;

		prepare_test!(
			it_works,
			r#"
			(module
				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Ok(_)
		);

		prepare_test!(
			omit_deploy,
			r#"
			(module
				(func (export "call"))
			)
			"#,
			Err("deploy function isn't exported")
		);

		prepare_test!(
			omit_call,
			r#"
			(module
				(func (export "deploy"))
			)
			"#,
			Err("call function isn't exported")
		);

		// Try to use imported function as an entry point.
		prepare_test!(
			try_sneak_export_as_entrypoint,
			r#"
			(module
				(import "seal0" "panic" (func))

				(func (export "deploy"))

				(export "call" (func 0))
			)
			"#,
			Err("entry point points to an imported function")
		);

		// Try to use imported function as an entry point.
		prepare_test!(
			try_sneak_export_as_global,
			r#"
			(module
				(func (export "deploy"))
				(global (export "call") i32 (i32.const 0))
			)
			"#,
			Err("expected a function")
		);

		prepare_test!(
			wrong_signature,
			r#"
			(module
				(func (export "deploy"))
				(func (export "call") (param i32))
			)
			"#,
			Err("entry point has wrong signature")
		);

		prepare_test!(
			unknown_exports,
			r#"
			(module
				(func (export "call"))
				(func (export "deploy"))
				(func (export "whatevs"))
			)
			"#,
			Err("unknown export: expecting only deploy and call functions")
		);

		prepare_test!(
			global_float,
			r#"
			(module
				(global $x f32 (f32.const 0))
				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("Validation of new code failed!")
		);

		prepare_test!(
			local_float,
			r#"
			(module
				(func $foo (local f32))
				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("Validation of new code failed!")
		);

		prepare_test!(
			param_float,
			r#"
			(module
				(func $foo (param f32))
				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("Validation of new code failed!")
		);

		prepare_test!(
			result_float,
			r#"
			(module
				(func $foo (result f32) (f32.const 0))
				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("Validation of new code failed!")
		);
	}
}
