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
use crate::wasm::{Environment, PrefabWasmModule};
use sp_core::crypto::UncheckedFrom;
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

impl<T: Config> From<&WasmModule<T>> for Sandbox
where
	T: Config,
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
{
	/// Creates an instance from the supplied module and supplies as much memory
	/// to the instance as the module declares as imported.
	fn from(module: &WasmModule<T>) -> Self {
		let memory = module
			.memory
			.as_ref()
			.map(|mem| (mem.min_pages, mem.max_pages))
			.unwrap_or((0, 0));
		let (store, _memory, instance) = PrefabWasmModule::<T>::instantiate::<EmptyEnv, _>(
			&module.code,
			(),
			memory,
			StackLimits::default(),
		)
		.expect("Failed to create benchmarking Sandbox instance");
		let entry_point = instance.get_export(&store, "call").unwrap().into_func().unwrap();
		Self { entry_point, store }
	}
}

struct EmptyEnv;

impl Environment<()> for EmptyEnv {
	fn define(_store: &mut Store<()>, _linker: &mut Linker<()>) -> Result<(), LinkerError> {
		Ok(())
	}
}
