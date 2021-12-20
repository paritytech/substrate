// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use crate::{
	host::HostContext,
	runtime::{Store, StoreData},
};
use sc_executor_common::error::WasmError;
use sp_wasm_interface::{FunctionContext, HostFunctions};
use std::{collections::HashMap, convert::TryInto};
use wasmtime::{Extern, ExternType, Func, FuncType, ImportType, Memory, MemoryType, Module, Trap};

pub struct Imports {
	/// Contains the index into `externs` where the memory import is stored if any. `None` if there
	/// is none.
	pub memory_import_index: Option<usize>,
	pub externs: Vec<Extern>,
}

/// Goes over all imports of a module and prepares a vector of `Extern`s that can be used for
/// instantiation of the module. Returns an error if there are imports that cannot be satisfied.
pub(crate) fn resolve_imports<H>(
	store: &mut Store,
	module: &Module,
	heap_pages: u64,
	allow_missing_func_imports: bool,
) -> Result<Imports, WasmError>
where
	H: HostFunctions,
{
	let mut externs = vec![];
	let mut memory_import_index = None;
	let mut pending_func_imports = HashMap::new();
	for (index, import_ty) in module.imports().enumerate() {
		let name = import_name(&import_ty)?;

		if import_ty.module() != "env" {
			return Err(WasmError::Other(format!(
				"host doesn't provide any imports from non-env module: {}:{}",
				import_ty.module(),
				name,
			)))
		}

		if name == "memory" {
			memory_import_index = Some(index);
			externs.push((index, resolve_memory_import(store, &import_ty, heap_pages)?));
			continue
		}

		match import_ty.ty() {
			ExternType::Func(func_ty) => {
				pending_func_imports.insert(name.to_owned(), (index, import_ty, func_ty));
			},
			_ =>
				return Err(WasmError::Other(format!(
					"host doesn't provide any non function imports besides 'memory': {}:{}",
					import_ty.module(),
					name,
				))),
		};
	}

	let mut registry = Registry { store, externs, pending_func_imports };

	H::register_static(&mut registry)?;
	let mut externs = registry.externs;

	if !registry.pending_func_imports.is_empty() {
		if allow_missing_func_imports {
			for (_, (index, import_ty, func_ty)) in registry.pending_func_imports {
				externs.push((
					index,
					MissingHostFuncHandler::new(&import_ty)?.into_extern(store, &func_ty),
				));
			}
		} else {
			let mut names = Vec::new();
			for (name, (_, import_ty, _)) in registry.pending_func_imports {
				names.push(format!("'{}:{}'", import_ty.module(), name));
			}
			let names = names.join(", ");
			return Err(WasmError::Other(format!(
				"runtime requires function imports which are not present on the host: {}",
				names
			)))
		}
	}

	externs.sort_unstable_by_key(|&(index, _)| index);
	let externs = externs.into_iter().map(|(_, ext)| ext).collect();

	Ok(Imports { memory_import_index, externs })
}

struct Registry<'a, 'b> {
	store: &'a mut Store,
	externs: Vec<(usize, Extern)>,
	pending_func_imports: HashMap<String, (usize, ImportType<'b>, FuncType)>,
}

impl<'a, 'b> sp_wasm_interface::HostFunctionRegistry for Registry<'a, 'b> {
	type State = StoreData;
	type Error = WasmError;
	type FunctionContext = HostContext<'a>;

	fn with_function_context<R>(
		caller: wasmtime::Caller<Self::State>,
		callback: impl FnOnce(&mut dyn FunctionContext) -> R,
	) -> R {
		callback(&mut HostContext { caller })
	}

	fn register_static<Params, Results>(
		&mut self,
		fn_name: &str,
		func: impl wasmtime::IntoFunc<Self::State, Params, Results>,
	) -> Result<(), Self::Error> {
		if let Some((index, _, _)) = self.pending_func_imports.remove(fn_name) {
			let func = Func::wrap(&mut *self.store, func);
			self.externs.push((index, Extern::Func(func)));
		}

		Ok(())
	}
}

/// When the module linking proposal is supported the import's name can be `None`.
/// Because we are not using this proposal we could safely unwrap the name.
/// However, we opt for an error in order to avoid panics at all costs.
fn import_name<'a, 'b: 'a>(import: &'a ImportType<'b>) -> Result<&'a str, WasmError> {
	let name = import.name().ok_or_else(|| {
		WasmError::Other("The module linking proposal is not supported.".to_owned())
	})?;
	Ok(name)
}

fn resolve_memory_import(
	store: &mut Store,
	import_ty: &ImportType,
	heap_pages: u64,
) -> Result<Extern, WasmError> {
	let requested_memory_ty = match import_ty.ty() {
		ExternType::Memory(memory_ty) => memory_ty,
		_ =>
			return Err(WasmError::Other(format!(
				"this import must be of memory type: {}:{}",
				import_ty.module(),
				import_name(&import_ty)?,
			))),
	};

	// Increment the min (a.k.a initial) number of pages by `heap_pages` and check if it exceeds the
	// maximum specified by the import.
	let initial = requested_memory_ty.minimum().saturating_add(heap_pages);
	if let Some(max) = requested_memory_ty.maximum() {
		if initial > max {
			return Err(WasmError::Other(format!(
				"incremented number of pages by heap_pages (total={}) is more than maximum requested\
				by the runtime wasm module {}",
				initial,
				max,
			)))
		}
	}

	// Note that the return value of `maximum` and `minimum`, while a u64,
	// will always fit into a u32 for 32-bit memories.
	// 64-bit memories are part of the memory64 proposal for WebAssembly which is not standardized
	// yet.
	let minimum: u32 = initial.try_into().map_err(|_| {
		WasmError::Other(format!(
			"minimum number of memory pages ({}) doesn't fit into u32",
			initial
		))
	})?;
	let maximum: Option<u32> = match requested_memory_ty.maximum() {
		Some(max) => Some(max.try_into().map_err(|_| {
			WasmError::Other(format!(
				"maximum number of memory pages ({}) doesn't fit into u32",
				max
			))
		})?),
		None => None,
	};

	let memory_ty = MemoryType::new(minimum, maximum);
	let memory = Memory::new(store, memory_ty).map_err(|e| {
		WasmError::Other(format!(
			"failed to create a memory during resolving of memory import: {}",
			e,
		))
	})?;
	Ok(Extern::Memory(memory))
}

/// A `Callable` handler for missing functions.
struct MissingHostFuncHandler {
	module: String,
	name: String,
}

impl MissingHostFuncHandler {
	fn new(import_ty: &ImportType) -> Result<Self, WasmError> {
		Ok(Self {
			module: import_ty.module().to_string(),
			name: import_name(import_ty)?.to_string(),
		})
	}

	fn into_extern(self, store: &mut Store, func_ty: &FuncType) -> Extern {
		let Self { module, name } = self;
		let func = Func::new(store, func_ty.clone(), move |_, _, _| {
			Err(Trap::new(format!("call to a missing function {}:{}", module, name)))
		});
		Extern::Func(func)
	}
}
