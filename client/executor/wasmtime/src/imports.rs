// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use crate::{host::HostContext, runtime::StoreData};
use sc_executor_common::error::WasmError;
use sp_wasm_interface::{FunctionContext, HostFunctions};
use std::collections::HashMap;
use wasmtime::{ExternType, FuncType, ImportType, Linker, Module, Trap};

/// Goes over all imports of a module and prepares the given linker for instantiation of the module.
/// Returns an error if there are imports that cannot be satisfied.
pub(crate) fn prepare_imports<H>(
	linker: &mut Linker<StoreData>,
	module: &Module,
	allow_missing_func_imports: bool,
) -> Result<(), WasmError>
where
	H: HostFunctions,
{
	let mut pending_func_imports = HashMap::new();
	for import_ty in module.imports() {
		let name = import_name(&import_ty)?;

		if import_ty.module() != "env" {
			return Err(WasmError::Other(format!(
				"host doesn't provide any imports from non-env module: {}:{}",
				import_ty.module(),
				name,
			)))
		}

		match import_ty.ty() {
			ExternType::Func(func_ty) => {
				pending_func_imports.insert(name.to_owned(), (import_ty, func_ty));
			},
			_ =>
				return Err(WasmError::Other(format!(
					"host doesn't provide any non function imports: {}:{}",
					import_ty.module(),
					name,
				))),
		};
	}

	let mut registry = Registry { linker, pending_func_imports };
	H::register_static(&mut registry)?;

	if !registry.pending_func_imports.is_empty() {
		if allow_missing_func_imports {
			for (name, (import_ty, func_ty)) in registry.pending_func_imports {
				let error = format!("call to a missing function {}:{}", import_ty.module(), name);
				log::debug!("Missing import: '{}' {:?}", name, func_ty);
				linker
					.func_new("env", &name, func_ty.clone(), move |_, _, _| {
						Err(Trap::new(error.clone()))
					})
					.expect("adding a missing import stub can only fail when the item already exists, and it is missing here; qed");
			}
		} else {
			let mut names = Vec::new();
			for (name, (import_ty, _)) in registry.pending_func_imports {
				names.push(format!("'{}:{}'", import_ty.module(), name));
			}
			let names = names.join(", ");
			return Err(WasmError::Other(format!(
				"runtime requires function imports which are not present on the host: {}",
				names
			)))
		}
	}

	Ok(())
}

struct Registry<'a, 'b> {
	linker: &'a mut Linker<StoreData>,
	pending_func_imports: HashMap<String, (ImportType<'b>, FuncType)>,
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
		if self.pending_func_imports.remove(fn_name).is_some() {
			self.linker.func_wrap("env", fn_name, func).map_err(|error| {
				WasmError::Other(format!(
					"failed to register host function '{}' with the WASM linker: {}",
					fn_name, error
				))
			})?;
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
