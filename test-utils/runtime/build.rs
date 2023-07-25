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

const BUILD_NO_GENESIS_BUILDER_SUPPORT_ENV: &str = "BUILD_NO_GENESIS_BUILDER_SUPPORT";

fn main() {
	#[cfg(feature = "std")]
	{
		substrate_wasm_builder::WasmBuilder::new()
			.with_current_project()
			.export_heap_base()
			// Note that we set the stack-size to 1MB explicitly even though it is set
			// to this value by default. This is because some of our tests
			// (`restoration_of_globals`) depend on the stack-size.
			.append_to_rust_flags("-Clink-arg=-zstack-size=1048576")
			.import_memory()
			.build();
	}

	#[cfg(feature = "std")]
	if std::env::var(BUILD_NO_GENESIS_BUILDER_SUPPORT_ENV).is_ok() {
		substrate_wasm_builder::WasmBuilder::new()
			.with_current_project()
			.export_heap_base()
			.append_to_rust_flags("-Clink-arg=-zstack-size=1048576")
			.set_file_name("wasm_binary_no_genesis_builder")
			.import_memory()
			.enable_feature("disable-genesis-builder")
			.build();
	}
	println!("cargo:rerun-if-env-changed={}", BUILD_NO_GENESIS_BUILDER_SUPPORT_ENV);

	#[cfg(feature = "std")]
	{
		substrate_wasm_builder::WasmBuilder::new()
			.with_current_project()
			.export_heap_base()
			.import_memory()
			.set_file_name("wasm_binary_logging_disabled.rs")
			.enable_feature("disable-logging")
			.build();
	}
}
