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
	storage::meter::Diff,
	wasm::{runtime::AllowDeprecatedInterface, CodeInfo, Determinism, Environment, WasmBlob},
	AccountIdOf, CodeVec, Config, Error, Schedule, LOG_TARGET,
};
use codec::MaxEncodedLen;
use sp_runtime::{traits::Hash, DispatchError};
#[cfg(any(test, feature = "runtime-benchmarks"))]
use sp_std::prelude::Vec;
use wasm_instrument::parity_wasm::elements::{
	self, External, Internal, MemoryType, Type, ValueType,
};
use wasmi::StackLimits;
use wasmparser::{Validator, WasmFeatures};

/// Imported memory must be located inside this module. The reason for hardcoding is that current
/// compiler toolchains might not support specifying other modules than "env" for memory imports.
pub const IMPORT_MODULE_MEMORY: &str = "env";

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

/// The inner deserialized module is valid (this is guaranteed by `new` method).
pub struct ContractModule(elements::Module);

impl ContractModule {
	/// Creates a new instance of `ContractModule`.
	///
	/// Returns `Err` if the `code` couldn't be decoded or
	/// if it contains an invalid module.
	pub fn new(code: &[u8]) -> Result<Self, &'static str> {
		let module = elements::deserialize_buffer(code).map_err(|_| "Can't decode Wasm code")?;

		// Return a `ContractModule` instance with
		// __valid__ module.
		Ok(ContractModule(module))
	}

	/// Ensures that module doesn't declare internal memories.
	///
	/// In this runtime we only allow wasm module to import memory from the environment.
	/// Memory section contains declarations of internal linear memories, so if we find one
	/// we reject such a module.
	fn ensure_no_internal_memory(&self) -> Result<(), &'static str> {
		if self.0.memory_section().map_or(false, |ms| ms.entries().len() > 0) {
			return Err("module declares internal memory")
		}
		Ok(())
	}

	/// Ensures that tables declared in the module are not too big.
	fn ensure_table_size_limit(&self, limit: u32) -> Result<(), &'static str> {
		if let Some(table_section) = self.0.table_section() {
			// In Wasm MVP spec, there may be at most one table declared. Double check this
			// explicitly just in case the Wasm version changes.
			if table_section.entries().len() > 1 {
				return Err("multiple tables declared")
			}
			if let Some(table_type) = table_section.entries().first() {
				// Check the table's initial size as there is no instruction or environment function
				// capable of growing the table.
				if table_type.limits().initial() > limit {
					return Err("table exceeds maximum size allowed")
				}
			}
		}
		Ok(())
	}

	/// Ensure that any `br_table` instruction adheres to its immediate value limit.
	fn ensure_br_table_size_limit(&self, limit: u32) -> Result<(), &'static str> {
		let code_section = if let Some(type_section) = self.0.code_section() {
			type_section
		} else {
			return Ok(())
		};
		for instr in code_section.bodies().iter().flat_map(|body| body.code().elements()) {
			use self::elements::Instruction::BrTable;
			if let BrTable(table) = instr {
				if table.table.len() > limit as usize {
					return Err("BrTable's immediate value is too big.")
				}
			}
		}
		Ok(())
	}

	fn ensure_global_variable_limit(&self, limit: u32) -> Result<(), &'static str> {
		if let Some(global_section) = self.0.global_section() {
			if global_section.entries().len() > limit as usize {
				return Err("module declares too many globals")
			}
		}
		Ok(())
	}

	fn ensure_local_variable_limit(&self, limit: u32) -> Result<(), &'static str> {
		if let Some(code_section) = self.0.code_section() {
			for func_body in code_section.bodies() {
				let locals_count: u32 =
					func_body.locals().iter().map(|val_type| val_type.count()).sum();
				if locals_count > limit {
					return Err("single function declares too many locals")
				}
			}
		}
		Ok(())
	}

	/// Ensure that no function exists that has more parameters than allowed.
	fn ensure_parameter_limit(&self, limit: u32) -> Result<(), &'static str> {
		let type_section = if let Some(type_section) = self.0.type_section() {
			type_section
		} else {
			return Ok(())
		};

		for Type::Function(func) in type_section.types() {
			if func.params().len() > limit as usize {
				return Err("Use of a function type with too many parameters.")
			}
		}

		Ok(())
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

		let module = &self.0;

		let types = module.type_section().map(|ts| ts.types()).unwrap_or(&[]);
		let export_entries = module.export_section().map(|is| is.entries()).unwrap_or(&[]);
		let func_entries = module.function_section().map(|fs| fs.entries()).unwrap_or(&[]);

		// Function index space consists of imported function following by
		// declared functions. Calculate the total number of imported functions so
		// we can use it to convert indexes from function space to declared function space.
		let fn_space_offset = module
			.import_section()
			.map(|is| is.entries())
			.unwrap_or(&[])
			.iter()
			.filter(|entry| matches!(*entry.external(), External::Function(_)))
			.count();

		for export in export_entries {
			match export.field() {
				"call" => call_found = true,
				"deploy" => deploy_found = true,
				_ => return Err("unknown export: expecting only deploy and call functions"),
			}

			// Then check the export kind. "call" and "deploy" are
			// functions.
			let fn_idx = match export.internal() {
				Internal::Function(ref fn_idx) => *fn_idx,
				_ => return Err("expected a function"),
			};

			// convert index from function index space to declared index space.
			let fn_idx = match fn_idx.checked_sub(fn_space_offset as u32) {
				Some(fn_idx) => fn_idx,
				None => {
					// Underflow here means fn_idx points to imported function which we don't allow!
					return Err("entry point points to an imported function")
				},
			};

			// Then check the signature.
			// Both "call" and "deploy" has a () -> () function type.
			// We still support () -> (i32) for backwards compatibility.
			let func_ty_idx = func_entries
				.get(fn_idx as usize)
				.ok_or("export refers to non-existent function")?
				.type_ref();
			let Type::Function(ref func_ty) =
				types.get(func_ty_idx as usize).ok_or("function has a non-existent type")?;
			if !(func_ty.params().is_empty() &&
				(func_ty.results().is_empty() || func_ty.results() == [ValueType::I32]))
			{
				return Err("entry point has wrong signature")
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
	/// This makes sure that the import section looks as we expect it from a contract
	/// and enforces and returns the memory type declared by the contract if any.
	pub fn scan_imports<T: Config>(&self) -> Result<Option<&MemoryType>, &'static str> {
		let module = &self.0;
		let import_entries = module.import_section().map(|is| is.entries()).unwrap_or(&[]);
		let mut imported_mem_type = None;

		for import in import_entries {
			match *import.external() {
				External::Table(_) => return Err("Cannot import tables"),
				External::Global(_) => return Err("Cannot import globals"),
				External::Function(_) => {
					if !<T as Config>::ChainExtension::enabled() &&
						import.field().as_bytes() == b"seal_call_chain_extension"
					{
						return Err("module uses chain extensions but chain extensions are disabled")
					}
				},
				External::Memory(ref memory_type) => {
					if import.module() != IMPORT_MODULE_MEMORY {
						return Err("Invalid module for imported memory")
					}
					if import.field() != "memory" {
						return Err("Memory import must have the field name 'memory'")
					}
					if imported_mem_type.is_some() {
						return Err("Multiple memory imports defined")
					}
					imported_mem_type = Some(memory_type);
					continue
				},
			}
		}

		Ok(imported_mem_type)
	}
}
#[cfg(any(test, feature = "runtime-benchmarks"))]
fn get_memory_limits<T: Config>(
	module: Option<&MemoryType>,
	schedule: &Schedule<T>,
) -> Result<(u32, u32), &'static str> {
	if let Some(memory_type) = module {
		// Inspect the module to extract the initial and maximum page count.
		let limits = memory_type.limits();
		match (limits.initial(), limits.maximum()) {
			(initial, Some(maximum)) if initial > maximum =>
				Err("Requested initial number of memory pages should not exceed the requested maximum"),
			(_, Some(maximum)) if maximum > schedule.limits.memory_pages =>
				Err("Maximum number of memory pages should not exceed the maximum configured in the Schedule."),
			(initial, Some(maximum)) => Ok((initial, maximum)),
			(initial, None) => {
				Ok((initial, schedule.limits.memory_pages))
			},
		}
	} else {
		// None memory imported in the Wasm module,
		// any access to it will lead to out of bounds trap.
		Ok((0, 0))
	}
}

/// Check that given `code` satisfies constraints required for the contract Wasm module.
///
/// On success it returns back the code.
fn validate<E, T>(
	code: &[u8],
	schedule: &Schedule<T>,
	determinism: Determinism,
	try_instantiate: TryInstantiate,
) -> Result<(), (DispatchError, &'static str)>
where
	E: Environment<()>,
	T: Config,
{
	// Do not enable any features here. Any additional feature needs to be carefully
	// checked for potential security issues. For example, enabling multi value could lead
	// to a DoS vector: It breaks our assumption that branch instructions are of constant time.
	// Depending on the implementation they can linearly depend on the amount of values returned
	// from a block.
	Validator::new_with_features(WasmFeatures {
		relaxed_simd: false,
		threads: false,
		tail_call: false,
		multi_memory: false,
		exceptions: false,
		memory64: false,
		extended_const: false,
		component_model: false,
		// This is not our only defense: All instructions explicitly need to have weights assigned
		// or the deployment will fail. We have none assigned for float instructions.
		floats: matches!(determinism, Determinism::Relaxed),
		mutable_global: false,
		saturating_float_to_int: false,
		sign_extension: false,
		bulk_memory: false,
		multi_value: false,
		reference_types: false,
		simd: false,
		memory_control: false,
	})
	.validate_all(code)
	.map_err(|err| {
		log::debug!(target: LOG_TARGET, "{}", err);
		(Error::<T>::CodeRejected.into(), "Validation of new code failed!")
	})?;

	(|| {
		let contract_module = ContractModule::new(code)?;
		contract_module.scan_exports()?;
		contract_module.scan_imports::<T>()?;
		contract_module.ensure_no_internal_memory()?;
		contract_module.ensure_table_size_limit(schedule.limits.table_size)?;
		contract_module.ensure_global_variable_limit(schedule.limits.globals)?;
		contract_module.ensure_local_variable_limit(schedule.limits.locals)?;
		contract_module.ensure_parameter_limit(schedule.limits.parameters)?;
		contract_module.ensure_br_table_size_limit(schedule.limits.br_table_size)?;
		// Extract memory limits from the module.
		// This also checks that module's memory import satisfies the schedule.
		Ok(())
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
	Ok(())
}

/// Validates the given binary `code` is a valid Wasm module satisfying following constraints:
///
/// - The module doesn't define an internal memory instance.
/// - Imported memory (if any) doesn't reserve more memory than permitted by the `schedule`.
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
	validate::<E, T>(code.as_ref(), schedule, determinism, try_instantiate)?;

	// Calculate deposit for storing contract code and `code_info` in two different storage items.
	let bytes_added = code.len().saturating_add(<CodeInfo<T>>::max_encoded_len()) as u32;
	let deposit = Diff { bytes_added, items_added: 2, ..Default::default() }
		.update_contract::<T>(None)
		.charge_or_zero();

	let code_info = CodeInfo { owner, deposit, determinism, refcount: 0 };
	let code_hash = T::Hashing::hash(&code);

	Ok(WasmBlob { code, code_info, code_hash })
}

/// Alternate (possibly unsafe) preparation functions used only for benchmarking and testing.
///
/// For benchmarking we need to construct special contracts that might not pass our
/// sanity checks. We hide functions allowing this behind a feature that is only set during
/// benchmarking or testing to prevent usage in production code.
#[cfg(any(test, feature = "runtime-benchmarks"))]
pub mod benchmarking {
	use super::*;

	/// Prepare function that does not perform most checks on the passed in code.
	pub fn prepare<T: Config>(
		code: Vec<u8>,
		schedule: &Schedule<T>,
		owner: AccountIdOf<T>,
	) -> Result<WasmBlob<T>, DispatchError> {
		let contract_module = ContractModule::new(&code)?;
		let _ = get_memory_limits(contract_module.scan_imports::<T>()?, schedule)?;
		let code_hash = T::Hashing::hash(&code);
		let code = code.try_into().map_err(|_| <Error<T>>::CodeTooLarge)?;
		let code_info = CodeInfo {
			owner,
			// this is a helper function for benchmarking which skips deposit collection
			deposit: Default::default(),
			refcount: 0,
			determinism: Determinism::Enforced,
		};

		Ok(WasmBlob { code, code_info, code_hash })
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
			Err("Memory import must have the field name 'memory'")
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
			Err("Cannot import tables")
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
			Err("Cannot import globals")
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
			Err("Invalid module for imported memory")
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
			Err("Invalid module for imported memory")
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
			wrong_signature,
			r#"
			(module
				(import "seal0" "input" (func (param i64)))

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("New code rejected on wasmi instantiation!")
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
