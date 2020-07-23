// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use super::InstanceWrapper;
use sc_executor_common::{
	error::{Error, Result},
};
use sp_wasm_interface::Value;
use cranelift_codegen::ir;
use cranelift_wasm::GlobalIndex;
use wasmtime_runtime::{ExportGlobal, Export};

/// A snapshot of a global variables values. This snapshot can be used later for restoring the
/// values to the preserved state.
///
/// Technically, a snapshot stores only values of mutable global variables. This is because
/// immutable global variables always have the same values.
pub struct GlobalsSnapshot {
	handle: wasmtime_runtime::InstanceHandle,
	preserved_mut_globals: Vec<(*mut wasmtime_runtime::VMGlobalDefinition, Value)>,
}

impl GlobalsSnapshot {
	/// Take a snapshot of global variables for a given instance.
	pub fn take(instance_wrapper: &InstanceWrapper) -> Result<Self> {
		// EVIL:
		// Usage of an undocumented function.
		let handle = instance_wrapper.instance.handle().clone().handle;

		let mut preserved_mut_globals = vec![];

		for global_idx in instance_wrapper.imported_globals_count..instance_wrapper.globals_count {
			let (def, global) = match handle.lookup_by_declaration(
				&wasmtime_environ::EntityIndex::Global(GlobalIndex::from_u32(global_idx)),
			) {
				Export::Global(ExportGlobal { definition, global, .. }) => (definition, global),
				_ => unreachable!("only globals can be returned for a global request"),
			};

			// skip immutable globals.
			if !global.mutability {
				continue;
			}

			let value = unsafe {
				// Safety of this function solely depends on the correctness of the reference and
				// the type information of the global.
				read_global(def, global.ty)?
			};
			preserved_mut_globals.push((def, value));
		}

		Ok(Self {
			preserved_mut_globals,
			handle,
		})
	}

	/// Apply the snapshot to the given instance.
	///
	/// This instance must be the same that was used for creation of this snapshot.
	pub fn apply(&self, instance_wrapper: &InstanceWrapper) -> Result<()> {
		if instance_wrapper.instance.handle().handle != self.handle {
			return Err(Error::from("unexpected instance handle".to_string()));
		}

		for (def, value) in &self.preserved_mut_globals {
			unsafe {
				// The following writes are safe if the precondition that this is the same instance
				// this snapshot was created with:
				//
				// 1. These pointers must be still not-NULL and allocated.
				// 2. The set of global variables is fixed for the lifetime of the same instance.
				// 3. We obviously assume that the wasmtime references are correct in the first place.
				// 4. We write the data with the same type it was read in the first place.
				write_global(*def, *value)?;
			}
		}
		Ok(())
	}
}

unsafe fn read_global(
	def: *const wasmtime_runtime::VMGlobalDefinition,
	ty: ir::Type,
) -> Result<Value> {
	let def = def
		.as_ref()
		.ok_or_else(|| Error::from("wasmtime global reference is null during read".to_string()))?;
	let val = match ty {
		ir::types::I32 => Value::I32(*def.as_i32()),
		ir::types::I64 => Value::I64(*def.as_i64()),
		ir::types::F32 => Value::F32(*def.as_u32()),
		ir::types::F64 => Value::F64(*def.as_u64()),
		_ => {
			return Err(Error::from(format!(
				"unsupported global variable type: {}",
				ty
			)))
		}
	};
	Ok(val)
}

unsafe fn write_global(def: *mut wasmtime_runtime::VMGlobalDefinition, value: Value) -> Result<()> {
	let def = def
		.as_mut()
		.ok_or_else(|| Error::from("wasmtime global reference is null during write".to_string()))?;
	match value {
		Value::I32(v) => *def.as_i32_mut() = v,
		Value::I64(v) => *def.as_i64_mut() = v,
		Value::F32(v) => *def.as_u32_mut() = v,
		Value::F64(v) => *def.as_u64_mut() = v,
	}
	Ok(())
}
