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

//! Module that takes care of loading, checking and preprocessing of a
//! wasm module before execution.

use super::env_def::HostFunctionSet;
use super::{Config, Error, Ext};
use parity_wasm::elements::{self, External, MemoryType, Type};
use pwasm_utils;
use pwasm_utils::rules;
use runtime_primitives::traits::As;
use sandbox;
use Trait;

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

	/// Scan an import section if any.
	///
	/// This accomplishes two tasks:
	///
	/// - checks any imported function against defined host functions set, incl.
	///   their signatures.
	/// - if there is a memory import, returns it's descriptor
	fn scan_imports<E: Ext>(&self, env: &HostFunctionSet<E>) -> Result<Option<&MemoryType>, Error> {
		let module = self
			.module
			.as_ref()
			.expect("On entry to the function `module` can't be `None`; qed");

		let types = module.type_section().map(|ts| ts.types()).unwrap_or(&[]);
		let import_entries = module
			.import_section()
			.map(|is| is.entries())
			.unwrap_or(&[]);

		let mut imported_mem_type = None;

		for import in import_entries {
			if import.module() != "env" {
				// This import tries to import something from non-"env" module,
				// but all imports are located in "env" at the moment.
				return Err(Error::Instantiate);
			}

			let type_idx = match import.external() {
				&External::Function(ref type_idx) => type_idx,
				&External::Memory(ref memory_type) => {
					imported_mem_type = Some(memory_type);
					continue;
				}
				_ => continue,
			};

			let Type::Function(ref func_ty) = types
				.get(*type_idx as usize)
				.ok_or_else(|| Error::Instantiate)?;

			let ext_func = env
				.funcs
				.get(import.field())
				.ok_or_else(|| Error::Instantiate)?;
			if !ext_func.func_type_matches(func_ty) {
				return Err(Error::Instantiate);
			}
		}
		Ok(imported_mem_type)
	}

	fn into_wasm_code(mut self) -> Result<Vec<u8>, Error> {
		elements::serialize(
			self.module
				.take()
				.expect("On entry to the function `module` can't be `None`; qed"),
		).map_err(|_| Error::Serialization)
	}
}

pub(super) struct PreparedContract {
	pub instrumented_code: Vec<u8>,
	pub memory: sandbox::Memory,
}

/// Loads the given module given in `original_code`, performs some checks on it and
/// does some preprocessing.
///
/// The checks are:
///
/// - module doesn't define an internal memory instance,
/// - imported memory (if any) doesn't reserve more memory than permitted by the `config`,
/// - all imported functions from the external environment matches defined by `env` module,
///
/// The preprocessing includes injecting code for gas metering and metering the height of stack.
pub(super) fn prepare_contract<E: Ext>(
	original_code: &[u8],
	config: &Config<E::T>,
	env: &HostFunctionSet<E>,
) -> Result<PreparedContract, Error> {
	let mut contract_module = ContractModule::new(original_code, config)?;
	contract_module.ensure_no_internal_memory()?;
	contract_module.inject_gas_metering()?;
	contract_module.inject_stack_height_metering()?;

	let memory = if let Some(memory_type) = contract_module.scan_imports(env)? {
		// Inspect the module to extract the initial and maximum page count.
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
	use std::fmt;
	use tests::Test;
	use vm::tests::MockExt;
	use wabt;

	impl fmt::Debug for PreparedContract {
		fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
			write!(f, "PreparedContract {{ .. }}")
		}
	}

	fn parse_and_prepare_wat(wat: &str) -> Result<PreparedContract, Error> {
		let wasm = wabt::Wat2Wasm::new().validate(false).convert(wat).unwrap();
		let config = Config::<Test>::default();
		let env = ::vm::env_def::init_env();
		prepare_contract::<MockExt>(wasm.as_ref(), &config, &env)
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

	#[test]
	fn imports() {
		// nothing can be imported from non-"env" module for now.
		let r = parse_and_prepare_wat(r#"(module (import "another_module" "memory" (memory 1 1)))"#);
		assert_matches!(r, Err(Error::Instantiate));

		let r = parse_and_prepare_wat(r#"(module (import "env" "gas" (func (param i32))))"#);
		assert_matches!(r, Ok(_));

		// wrong signature
		let r = parse_and_prepare_wat(r#"(module (import "env" "gas" (func (param i64))))"#);
		assert_matches!(r, Err(Error::Instantiate));

		// unknown function name
		let r = parse_and_prepare_wat(r#"(module (import "env" "unknown_func" (func)))"#);
		assert_matches!(r, Err(Error::Instantiate));
	}
}
