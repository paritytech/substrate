// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

//! A `CodeExecutor` specialization which uses natively compiled runtime when the wasm to be
//! executed is equivalent to the natively compiled code.

pub use sc_executor::NativeExecutor;

// Declare an instance of the native executor named `Executor`. Include the wasm binary as the
// equivalent wasm code.
pub struct Executor;

impl sc_executor::NativeExecutionDispatch for Executor {
	type ExtendHostFunctions = frame_benchmarking::benchmarking::HostFunctions;

	fn dispatch(method: &str, data: &[u8]) -> Option<Vec<u8>> {
		node_runtime::api::dispatch(method, data)
	}

	fn native_version() -> sc_executor::NativeVersion {
		node_runtime::native_version()
	}
}
