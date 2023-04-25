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
	wasm::{
		runtime::AllowDeprecatedInterface, Determinism, Environment, OwnerInfo, PrefabWasmModule,
	},
	AccountIdOf, CodeVec, Config, Error, Schedule, LOG_TARGET,
};
use codec::{Encode, MaxEncodedLen};
use sp_runtime::{traits::Hash, DispatchError};
use sp_std::prelude::*;
use wasm_instrument::{
	gas_metering,
	parity_wasm::elements::{self, External, Internal, MemoryType, Type, ValueType},
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

/// The reason why a contract is instrumented.
enum InstrumentReason {
	/// A new code is uploaded.
	New,
	/// Existing code is re-instrumented.
	Reinstrument,
}

struct ContractModule<'a, T: Config> {
	/// A deserialized module. The module is valid (this is Guaranteed by `new` method).
	module: elements::Module,
	schedule: &'a Schedule<T>,
}

impl<'a, T: Config> ContractModule<'a, T> {
	/// Creates a new instance of `ContractModule`.
	///
	/// Returns `Err` if the `original_code` couldn't be decoded or
	/// if it contains an invalid module.
	fn new(original_code: &[u8], schedule: &'a Schedule<T>) -> Result<Self, &'static str> {
		let module =
			elements::deserialize_buffer(original_code).map_err(|_| "Can't decode wasm code")?;

		// Return a `ContractModule` instance with
		// __valid__ module.
		Ok(ContractModule { module, schedule })
	}

	/// Ensures that module doesn't declare internal memories.
	///
	/// In this runtime we only allow wasm module to import memory from the environment.
	/// Memory section contains declarations of internal linear memories, so if we find one
	/// we reject such a module.
	fn ensure_no_internal_memory(&self) -> Result<(), &'static str> {
		if self.module.memory_section().map_or(false, |ms| ms.entries().len() > 0) {
			return Err("module declares internal memory")
		}
		Ok(())
	}

	/// Ensures that tables declared in the module are not too big.
	fn ensure_table_size_limit(&self, limit: u32) -> Result<(), &'static str> {
		if let Some(table_section) = self.module.table_section() {
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
		let code_section = if let Some(type_section) = self.module.code_section() {
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
		if let Some(global_section) = self.module.global_section() {
			if global_section.entries().len() > limit as usize {
				return Err("module declares too many globals")
			}
		}
		Ok(())
	}

	fn ensure_local_variable_limit(&self, limit: u32) -> Result<(), &'static str> {
		if let Some(code_section) = self.module.code_section() {
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
		let type_section = if let Some(type_section) = self.module.type_section() {
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

	fn inject_gas_metering(self, determinism: Determinism) -> Result<Self, &'static str> {
		let gas_rules = self.schedule.rules(determinism);
		let backend = gas_metering::host_function::Injector::new("seal0", "gas");
		let contract_module = gas_metering::inject(self.module, backend, &gas_rules)
			.map_err(|_| "gas instrumentation failed")?;
		Ok(ContractModule { module: contract_module, schedule: self.schedule })
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
	///
	/// `import_fn_banlist`: list of function names that are disallowed to be imported
	fn scan_imports(
		&self,
		import_fn_banlist: &[&[u8]],
	) -> Result<Option<&MemoryType>, &'static str> {
		let module = &self.module;
		let import_entries = module.import_section().map(|is| is.entries()).unwrap_or(&[]);
		let mut imported_mem_type = None;

		for import in import_entries {
			match *import.external() {
				External::Table(_) => return Err("Cannot import tables"),
				External::Global(_) => return Err("Cannot import globals"),
				External::Function(_) => {
					if !T::ChainExtension::enabled() &&
						import.field().as_bytes() == b"seal_call_chain_extension"
					{
						return Err("module uses chain extensions but chain extensions are disabled")
					}

					if import_fn_banlist.iter().any(|f| import.field().as_bytes() == *f) {
						return Err("module imports a banned function")
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

	fn into_wasm_code(self) -> Result<Vec<u8>, &'static str> {
		elements::serialize(self.module).map_err(|_| "error serializing instrumented module")
	}
}

fn get_memory_limits<T: Config>(
	module: Option<&MemoryType>,
	schedule: &Schedule<T>,
) -> Result<(u32, u32), &'static str> {
	if let Some(memory_type) = module {
		// Inspect the module to extract the initial and maximum page count.
		let limits = memory_type.limits();
		match (limits.initial(), limits.maximum()) {
			(initial, Some(maximum)) if initial > maximum =>
				Err("Requested initial number of pages should not exceed the requested maximum"),
			(_, Some(maximum)) if maximum > schedule.limits.memory_pages =>
				Err("Maximum number of pages should not exceed the configured maximum."),
			(initial, Some(maximum)) => Ok((initial, maximum)),
			(_, None) => {
				// Maximum number of pages should be always declared.
				// This isn't a hard requirement and can be treated as a maximum set
				// to configured maximum.
				Err("Maximum number of pages should be always declared.")
			},
		}
	} else {
		// If none memory imported then just create an empty placeholder.
		// Any access to it will lead to out of bounds trap.
		Ok((0, 0))
	}
}

/// Check and instrument the given `original_code`.
///
/// On success it returns the instrumented versions together with its `(initial, maximum)`
/// error requirement. The memory requirement was also validated against the `schedule`.
fn instrument<E, T>(
	original_code: &[u8],
	schedule: &Schedule<T>,
	determinism: Determinism,
	try_instantiate: TryInstantiate,
	reason: InstrumentReason,
) -> Result<(Vec<u8>, (u32, u32)), (DispatchError, &'static str)>
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
	.validate_all(original_code)
	.map_err(|err| {
		log::debug!(target: LOG_TARGET, "{}", err);
		(Error::<T>::CodeRejected.into(), "validation of new code failed")
	})?;

	let (code, (initial, maximum)) = (|| {
		let contract_module = ContractModule::new(original_code, schedule)?;
		contract_module.scan_exports()?;
		contract_module.ensure_no_internal_memory()?;
		contract_module.ensure_table_size_limit(schedule.limits.table_size)?;
		contract_module.ensure_global_variable_limit(schedule.limits.globals)?;
		contract_module.ensure_local_variable_limit(schedule.limits.locals)?;
		contract_module.ensure_parameter_limit(schedule.limits.parameters)?;
		contract_module.ensure_br_table_size_limit(schedule.limits.br_table_size)?;

		// We disallow importing `gas` function here since it is treated as implementation detail.
		let disallowed_imports = [b"gas".as_ref()];
		let memory_limits =
			get_memory_limits(contract_module.scan_imports(&disallowed_imports)?, schedule)?;

		let code = contract_module.inject_gas_metering(determinism)?.into_wasm_code()?;

		Ok((code, memory_limits))
	})()
	.map_err(|msg: &str| {
		log::debug!(target: LOG_TARGET, "new code rejected: {}", msg);
		(Error::<T>::CodeRejected.into(), msg)
	})?;

	// This will make sure that the module can be actually run within wasmi:
	//
	// - Doesn't use any unknown imports.
	// - Doesn't explode the wasmi bytecode generation.
	if matches!(try_instantiate, TryInstantiate::Instantiate) {
		// We don't actually ever run any code so we can get away with a minimal stack which
		// reduces the amount of memory that needs to be zeroed.
		let stack_limits = StackLimits::new(1, 1, 0).expect("initial <= max; qed");
		PrefabWasmModule::<T>::instantiate::<E, _>(
			&code,
			(),
			(initial, maximum),
			stack_limits,
			match reason {
				InstrumentReason::New => AllowDeprecatedInterface::No,
				InstrumentReason::Reinstrument => AllowDeprecatedInterface::Yes,
			},
		)
		.map_err(|err| {
			log::debug!(target: LOG_TARGET, "{}", err);
			(Error::<T>::CodeRejected.into(), "new code rejected after instrumentation")
		})?;
	}

	Ok((code, (initial, maximum)))
}

/// Loads the given module given in `original_code`, performs some checks on it and
/// does some preprocessing.
///
/// The checks are:
///
/// - the provided code is a valid wasm module
/// - the module doesn't define an internal memory instance
/// - imported memory (if any) doesn't reserve more memory than permitted by the `schedule`
/// - all imported functions from the external environment matches defined by `env` module
///
/// The preprocessing includes injecting code for gas metering and metering the height of stack.
pub fn prepare<E, T>(
	original_code: CodeVec<T>,
	schedule: &Schedule<T>,
	owner: AccountIdOf<T>,
	determinism: Determinism,
	try_instantiate: TryInstantiate,
) -> Result<PrefabWasmModule<T>, (DispatchError, &'static str)>
where
	E: Environment<()>,
	T: Config,
{
	let (code, (initial, maximum)) = instrument::<E, T>(
		original_code.as_ref(),
		schedule,
		determinism,
		try_instantiate,
		InstrumentReason::New,
	)?;

	let original_code_len = original_code.len();

	let mut module = PrefabWasmModule {
		instruction_weights_version: schedule.instruction_weights.version,
		initial,
		maximum,
		code: code.try_into().map_err(|_| (<Error<T>>::CodeTooLarge.into(), ""))?,
		code_hash: T::Hashing::hash(&original_code),
		original_code: Some(original_code),
		owner_info: None,
		determinism,
	};

	// We need to add the sizes of the `#[codec(skip)]` fields which are stored in different
	// storage items. This is also why we have `3` items added and not only one.
	let bytes_added = module
		.encoded_size()
		.saturating_add(original_code_len)
		.saturating_add(<OwnerInfo<T>>::max_encoded_len()) as u32;
	let deposit = Diff { bytes_added, items_added: 3, ..Default::default() }
		.update_contract::<T>(None)
		.charge_or_zero();

	module.owner_info = Some(OwnerInfo { owner, deposit, refcount: 0 });

	Ok(module)
}

/// Same as [`prepare`] but without constructing a new module.
///
/// Used to update the code of an existing module to the newest [`Schedule`] version.
/// Stictly speaking is not necessary to check the existing code before reinstrumenting because
/// it can't change in the meantime. However, since we recently switched the validation library
/// we want to re-validate to weed out any bugs that were lurking in the old version.
pub fn reinstrument<E, T>(
	original_code: &[u8],
	schedule: &Schedule<T>,
	determinism: Determinism,
) -> Result<Vec<u8>, DispatchError>
where
	E: Environment<()>,
	T: Config,
{
	instrument::<E, T>(
		original_code,
		schedule,
		determinism,
		// This function was triggered by an interaction with an existing contract code
		// that will try to instantiate anyways. Failing here would not help
		// as the contract is already on chain.
		TryInstantiate::Skip,
		InstrumentReason::Reinstrument,
	)
	.map_err(|(err, msg)| {
		log::error!(target: LOG_TARGET, "CodeRejected during reinstrument: {}", msg);
		err
	})
	.map(|(code, _)| code)
}

/// Alternate (possibly unsafe) preparation functions used only for benchmarking and testing.
///
/// For benchmarking we need to construct special contracts that might not pass our
/// sanity checks or need to skip instrumentation for correct results. We hide functions
/// allowing this behind a feature that is only set during benchmarking or testing to
/// prevent usage in production code.
#[cfg(any(test, feature = "runtime-benchmarks"))]
pub mod benchmarking {
	use super::*;

	/// Prepare function that neither checks nor instruments the passed in code.
	pub fn prepare<T: Config>(
		original_code: Vec<u8>,
		schedule: &Schedule<T>,
		owner: AccountIdOf<T>,
	) -> Result<PrefabWasmModule<T>, &'static str> {
		let contract_module = ContractModule::new(&original_code, schedule)?;
		let memory_limits = get_memory_limits(contract_module.scan_imports(&[])?, schedule)?;
		Ok(PrefabWasmModule {
			instruction_weights_version: schedule.instruction_weights.version,
			initial: memory_limits.0,
			maximum: memory_limits.1,
			code_hash: T::Hashing::hash(&original_code),
			original_code: Some(original_code.try_into().map_err(|_| "Original code too large")?),
			code: contract_module
				.into_wasm_code()?
				.try_into()
				.map_err(|_| "Instrumented code too large")?,
			owner_info: Some(OwnerInfo {
				owner,
				// this is a helper function for benchmarking which skips deposit collection
				deposit: Default::default(),
				refcount: 0,
			}),
			determinism: Determinism::Enforced,
		})
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

	impl fmt::Debug for PrefabWasmModule<Test> {
		fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
			write!(f, "PreparedContract {{ .. }}")
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
		Err("validation of new code failed")
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
			Err("validation of new code failed")
		);

		prepare_test!(
			no_maximum,
			r#"
			(module
				(import "env" "memory" (memory 1))

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("Maximum number of pages should be always declared.")
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
			Err("Maximum number of pages should not exceed the configured maximum.")
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
			Err("validation of new code failed")
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

		// even though gas is defined the contract can't import it since
		// it is an implementation defined.
		prepare_test!(
			can_not_import_gas_function,
			r#"
			(module
				(import "seal0" "gas" (func (param i32)))

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("module imports a banned function")
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

		// wrong signature
		prepare_test!(
			wrong_signature,
			r#"
			(module
				(import "seal0" "gas" (func (param i64)))

				(func (export "call"))
				(func (export "deploy"))
			)
			"#,
			Err("module imports a banned function")
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
			Err("new code rejected after instrumentation")
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
			Err("validation of new code failed")
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
			Err("validation of new code failed")
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
			Err("validation of new code failed")
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
			Err("validation of new code failed")
		);
	}
}
