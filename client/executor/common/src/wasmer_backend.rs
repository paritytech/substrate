// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Wasmer specific impls for sandbox

pub fn invoke_wasmer(
	&self,

	// function to call that is exported from the module
	export_name: &str,

	// arguments passed to the function
	args: &[RuntimeValue],

	// arbitraty context data of the call
	state: u32,

	sandbox_context: &mut dyn SandboxContext,
) -> std::result::Result<Option<wasmi::RuntimeValue>, wasmi::Error> {
	let function = wasmer_instance
		.exports
		.get_function(export_name)
		.map_err(|error| wasmi::Error::Function(error.to_string()))?;

	let args: Vec<wasmer::Val> = args
		.iter()
		.map(|v| match *v {
			RuntimeValue::I32(val) => wasmer::Val::I32(val),
			RuntimeValue::I64(val) => wasmer::Val::I64(val),
			RuntimeValue::F32(val) => wasmer::Val::F32(val.into()),
			RuntimeValue::F64(val) => wasmer::Val::F64(val.into()),
		})
		.collect();

	let wasmer_result = SandboxContextStore::using(sandbox_context, || {
		function.call(&args).map_err(|error| wasmi::Error::Function(error.to_string()))
	})?;

	if wasmer_result.len() > 1 {
		return Err(wasmi::Error::Function(
			"multiple return types are not supported yet".into(),
		))
	}

	wasmer_result
		.first()
		.map(|wasm_value| {
			let wasmer_value = match *wasm_value {
				wasmer::Val::I32(val) => RuntimeValue::I32(val),
				wasmer::Val::I64(val) => RuntimeValue::I64(val),
				wasmer::Val::F32(val) => RuntimeValue::F32(val.into()),
				wasmer::Val::F64(val) => RuntimeValue::F64(val.into()),
				_ =>
					return Err(wasmi::Error::Function(format!(
						"Unsupported return value: {:?}",
						wasm_value,
					))),
			};

			Ok(wasmer_value)
		})
		.transpose()
}

