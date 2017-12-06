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

//! Rust implementation of Polkadot contracts.

use parity_wasm;

use primitives::contract::{CallData, OutData};
//use serializer::{from_slice as de, to_vec as ser};
use state_machine::{Externalities, CodeExecutor};

use error::{Error, ErrorKind, Result};

/// Dummy rust executor for contracts.
///
/// Instead of actually executing the provided code it just
/// dispatches the calls to pre-defined hardcoded implementations in rust.
#[derive(Debug, Default)]
pub struct WasmExecutor {
}

impl CodeExecutor for WasmExecutor {
	type Error = Error;

	fn call<E: Externalities>(
		&self,
		ext: &mut E,
		method: &str,
		data: &CallData,
	) -> Result<OutData> {

		// TODO: avoid copying code by requiring code to remain immutable through execution,
		// splitting it off from potentially mutable externalities.
		let code = match ext.code() {
			Ok(e) => e.to_owned(),
			Err(e) => Err(ErrorKind::Externalities(Box::new(e)))?,
		};

		use parity_wasm::ModuleInstanceInterface;
		use parity_wasm::RuntimeValue::{I64};
		let program = parity_wasm::ProgramInstance::new();
		let module = parity_wasm::deserialize_buffer(code).expect("Failed to load module");
		let module = program.add_module("main", module, None).expect("Failed to initialize module");
		module.execute_export(method, vec![I64(data.0.len() as i64)].into())
			.map(|o| OutData(vec![1; if let Some(I64(l)) = o { l as usize } else { 0 }]))
			.map_err(|_| ErrorKind::Runtime.into())
	}
}

#[cfg(test)]
mod tests {

	use parity_wasm;
	use super::*;

	#[derive(Debug, Default)]
	struct TestExternalities;
	impl Externalities<WasmExecutor> for TestExternalities {
		fn set_storage(&mut self, _object: i64, _key: Vec<u8>, _value: Vec<u8>) {
			unimplemented!()
		}
	}

	impl StaticExternalities<WasmExecutor> for TestExternalities {
		type Error = Error;

		fn storage(&self, _object: i64, _key: Vec<u8>) -> Result<&[u8]> {
			unimplemented!()
		}
	}

	#[test]
	fn should_run_wasm() {
		use parity_wasm::ModuleInstanceInterface;
		use parity_wasm::RuntimeValue::{I64};

		let program = parity_wasm::ProgramInstance::new();
		let test_module = include_bytes!("../../target/wasm32-unknown-unknown/release/runtime.compact.wasm");
		let module = parity_wasm::deserialize_buffer(test_module.to_vec()).expect("Failed to load module");
		let module = program.add_module("test", module, None).expect("Failed to initialize module");
		let argument: i64 = 42;
		assert_eq!(Some(I64(argument * 2)), module.execute_export("test", vec![I64(argument)].into()).unwrap());
	}


	#[test]
	fn should_provide_externalities() {
		use parity_wasm::ModuleInstanceInterface;
		use parity_wasm::RuntimeValue::{I64};

		let program = parity_wasm::ProgramInstance::new();
		let test_module = include_bytes!("../../target/wasm32-unknown-unknown/release/runtime.compact.wasm");
		let module = parity_wasm::deserialize_buffer(test_module.to_vec()).expect("Failed to load module");
		let module = program.add_module("test", module, None).expect("Failed to initialize module");
		let argument: i64 = 42;
		assert_eq!(Some(I64(argument * 2)), module.execute_export("test", vec![I64(argument)].into()).unwrap());
	}
}
