// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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
//! executed is equivalent to the natively compiled code for the older runtimes

use sc_executor::{NativeExecutor, FallbackDispatch, FallbackDispatchHolder, native_executor_instance};

pub fn initialize_older_runtimes() -> Vec<Box<dyn FallbackDispatch>> {
    vec![
        Box::new(FallbackDispatchRc1::new()),
        Box::new(FallbackDispatchRc2::new())
    ]
}

native_executor_instance!(
	pub ExecutorRc1,
	node_runtime_rc1::api::dispatch,
	node_runtime_rc1::native_version,
	frame_benchmarking::benchmarking::HostFunctions,
);

pub type FallbackDispatchRc1 = FallbackDispatchHolder<ExecutorRc1>;

native_executor_instance!(
	pub ExecutorRc2,
	node_runtime_rc2::api::dispatch,
	node_runtime_rc2::native_version,
	frame_benchmarking::benchmarking::HostFunctions,
);
pub type FallbackDispatchRc2 = FallbackDispatchHolder<ExecutorRc2>;

