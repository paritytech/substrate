// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! WASM re-execution of a parachain candidate.
//! In the context of relay-chain candidate evaluation, there are some additional
//! steps to ensure that the provided input parameters are correct.
//! Assuming the parameters are correct, this module provides a wrapper around
//! a WASM VM for re-execution of a parachain candidate.

use codec::{Decode, Encode};

use wasmi::{self, Module, ModuleInstance,  MemoryInstance, MemoryDescriptor, MemoryRef, ModuleImportResolver};
use wasmi::{memory_units, RuntimeValue};
use wasmi::Error as WasmError;
use wasmi::memory_units::{Bytes, Pages, RoundUpTo};

use super::{ValidationParams, ValidationResult};

use std::cell::RefCell;

error_chain! {
	types { Error, ErrorKind, ResultExt; }
	foreign_links {
		Wasm(WasmError);
	}
	errors {
		/// Call data too big. WASM32 only has a 32-bit address space.
		ParamsTooLarge(len: usize) {
			description("Validation parameters took up too much space to execute in WASM"),
			display("Validation parameters took up {} bytes, max allowed by WASM is {}", len, i32::max_value()),
		}
		/// Bad return data or type.
		BadReturn {
			description("Validation function returned invalid data."),
			display("Validation function returned invalid data."),
		}
	}
}

struct Resolver {
	max_memory: u32, // in pages.
	memory: RefCell<Option<MemoryRef>>,
}

impl ModuleImportResolver for Resolver {
	fn resolve_memory(
		&self,
		field_name: &str,
		descriptor: &MemoryDescriptor,
	) -> Result<MemoryRef, WasmError> {
		if field_name == "memory" {
			let effective_max = descriptor.maximum().unwrap_or(self.max_memory);
			if descriptor.initial() > self.max_memory || effective_max > self.max_memory {
				Err(WasmError::Instantiation("Module requested too much memory".to_owned()))
			} else {
				let mem = MemoryInstance::alloc(
					memory_units::Pages(descriptor.initial() as usize),
					descriptor.maximum().map(|x| memory_units::Pages(x as usize)),
				)?;
				*self.memory.borrow_mut() = Some(mem.clone());
				Ok(mem)
			}
		} else {
			Err(WasmError::Instantiation("Memory imported under unknown name".to_owned()))
		}
	}
}

/// Validate a candidate under the given validation code.
///
/// This will fail if the validation code is not a proper parachain validation module.
pub fn validate_candidate(validation_code: &[u8], params: ValidationParams) -> Result<ValidationResult, Error> {
	use wasmi::LINEAR_MEMORY_PAGE_SIZE;

	// maximum memory in bytes
	const MAX_MEM: u32 = 1024 * 1024 * 1024; // 1 GiB

	// instantiate the module.
	let (module, memory) = {
		let module = Module::from_buffer(validation_code)?;

		let module_resolver = Resolver {
			max_memory: MAX_MEM / LINEAR_MEMORY_PAGE_SIZE.0 as u32,
			memory: RefCell::new(None),
		};

		let module = ModuleInstance::new(
			&module,
			&wasmi::ImportsBuilder::new().with_resolver("env", &module_resolver),
		)?.run_start(&mut wasmi::NopExternals).map_err(WasmError::Trap)?;

		let memory = module_resolver.memory.borrow()
			.as_ref()
			.ok_or_else(|| WasmError::Instantiation("No imported memory instance".to_owned()))?
			.clone();

		(module, memory)
	};

	// allocate call data in memory.
	let (offset, len) = {
		let encoded_call_data = params.encode();

		// hard limit from WASM.
		if encoded_call_data.len() > i32::max_value() as usize {
			bail!(ErrorKind::ParamsTooLarge(encoded_call_data.len()));
		}

		// allocate sufficient amount of wasm pages to fit encoded call data.
		let call_data_pages: Pages = Bytes(encoded_call_data.len()).round_up_to();
		let allocated_mem_start: Bytes = memory.grow(call_data_pages)?.into();

		memory.set(allocated_mem_start.0 as u32, &encoded_call_data)
			.expect(
				"enough memory allocated just before this; \
				copying never fails if memory is large enough; qed"
			);

		(allocated_mem_start.0, encoded_call_data.len())
	};

	let output = module.invoke_export(
		"validate",
		&[RuntimeValue::I32(offset as i32), RuntimeValue::I32(len as i32)],
		&mut wasmi::NopExternals,
	)?;

	match output {
		Some(RuntimeValue::I32(len_offset)) => {
			let len_offset = len_offset as u32;

			let mut len_bytes = [0u8; 4];
			memory.get_into(len_offset, &mut len_bytes)?;

			let len = u32::decode(&mut &len_bytes[..])
				.ok_or_else(|| ErrorKind::BadReturn)?;

			let return_offset = if len > len_offset {
				bail!(ErrorKind::BadReturn);
			} else {
				len_offset - len
			};

			// TODO: optimize when `wasmi` lets you inspect memory with a closure.
			let raw_return = memory.get(return_offset, len as usize)?;
			ValidationResult::decode(&mut &raw_return[..])
				.ok_or_else(|| ErrorKind::BadReturn)
				.map_err(Into::into)
		}
		_ => bail!(ErrorKind::BadReturn),
	}
}
