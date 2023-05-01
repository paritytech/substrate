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

/// ! For instruction benchmarking we do not instantiate a full contract but merely the
/// ! sandbox to execute the Wasm code. This is because we do not need the full
/// ! environment that provides the seal interface as imported functions.
use super::{code::WasmModule, Config};
use crate::wasm::{
	AllowDeprecatedInterface, AllowUnstableInterface, Determinism, Environment, WasmBlob,
};
use sp_core::Get;
use wasmi::{errors::LinkerError, Func, Linker, StackLimits, Store};

/// Minimal execution environment without any imported functions.
pub struct Sandbox {
	entry_point: Func,
	store: Store<()>,
}

impl Sandbox {
	/// Invoke the `call` function of a contract code and panic on any execution error.
	pub fn invoke(&mut self) {
		self.entry_point.call(&mut self.store, &[], &mut []).unwrap();
	}
}

impl<T: Config> From<&WasmModule<T>> for Sandbox {
	/// Creates an instance from the supplied module.
	/// Sets the execution engine fuel level to `u64::MAX`.
	fn from(module: &WasmModule<T>) -> Self {
		let (mut store, _memory, instance) = WasmBlob::<T>::instantiate_wasm::<EmptyEnv, _>(
			&module.code,
			(),
			&<T>::Schedule::get(),
			Determinism::Relaxed,
			StackLimits::default(),
			// We are testing with an empty environment anyways
			AllowDeprecatedInterface::No,
		)
		.expect("Failed to create benchmarking Sandbox instance");

		// Set fuel for wasmi execution.
		store
			.add_fuel(u64::MAX)
			.expect("We've set up engine to fuel consuming mode; qed");

		let entry_point = instance.get_export(&store, "call").unwrap().into_func().unwrap();
		Self { entry_point, store }
	}
}

struct EmptyEnv;

impl Environment<()> for EmptyEnv {
	fn define(
		_: &mut Store<()>,
		_: &mut Linker<()>,
		_: AllowUnstableInterface,
		_: AllowDeprecatedInterface,
	) -> Result<(), LinkerError> {
		Ok(())
	}
}
