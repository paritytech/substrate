// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

/// ! For instruction benchmarking we do no instantiate a full contract but merely the
/// ! sandbox to execute the wasm code. This is because we do not need the full
/// ! environment that provides the seal interface as imported functions.
use super::{code::WasmModule, Config};
use sp_core::crypto::UncheckedFrom;
use sp_sandbox::{
	default_executor::{EnvironmentDefinitionBuilder, Instance, Memory},
	SandboxEnvironmentBuilder, SandboxInstance,
};

/// Minimal execution environment without any exported functions.
pub struct Sandbox {
	instance: Instance<()>,
	_memory: Option<Memory>,
}

impl Sandbox {
	/// Invoke the `call` function of a contract code and panic on any execution error.
	pub fn invoke(&mut self) {
		self.instance.invoke("call", &[], &mut ()).unwrap();
	}
}

impl<T: Config> From<&WasmModule<T>> for Sandbox
where
	T: Config,
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	/// Creates an instance from the supplied module and supplies as much memory
	/// to the instance as the module declares as imported.
	fn from(module: &WasmModule<T>) -> Self {
		let mut env_builder = EnvironmentDefinitionBuilder::new();
		let memory = module.add_memory(&mut env_builder);
		let instance = Instance::new(&module.code, &env_builder, &mut ())
			.expect("Failed to create benchmarking Sandbox instance");
		Self { instance, _memory: memory }
	}
}
