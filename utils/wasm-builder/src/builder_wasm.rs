// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

use std::{
	env,
	path::{Path, PathBuf},
};

/// First step of the [`WasmBuilder`] to select the project to build.
pub struct WasmBuilderSelectProject {
	/// This parameter just exists to make it impossible to construct
	/// this type outside of this crate.
	_ignore: (),
}

impl WasmBuilderSelectProject {
	/// Use the current project as project for building the WASM binary.
	///
	/// # Panics
	///
	/// Panics if the `CARGO_MANIFEST_DIR` variable is not set. This variable
	/// is always set by `Cargo` in `build.rs` files.
	pub fn with_current_project(self) -> WasmBuilder {
		WasmBuilder { rust_flags: Vec::new(), file_name: None, features_to_enable: Vec::new() }
	}

	/// Use the given `path` as project for building the WASM binary.
	///
	/// Returns an error if the given `path` does not points to a `Cargo.toml`.
	pub fn with_project(self, path: impl Into<PathBuf>) -> Result<WasmBuilder, &'static str> {
		let path = path.into();

		if path.ends_with("Cargo.toml") && path.exists() {
			Ok(WasmBuilder {
				rust_flags: Vec::new(),
				file_name: None,
				features_to_enable: Vec::new(),
			})
		} else {
			Err("Project path must point to the `Cargo.toml` of the project")
		}
	}
}

/// The builder for building a wasm binary.
///
/// The builder itself is separated into multiple structs to make the setup type safe.
///
/// Building a wasm binary:
///
/// 1. Call [`WasmBuilder::new`] to create a new builder.
/// 2. Select the project to build using the methods of [`WasmBuilderSelectProject`].
/// 3. Set additional `RUST_FLAGS` or a different name for the file containing the WASM code
///    using methods of [`WasmBuilder`].
/// 4. Build the WASM binary using [`Self::build`].
pub struct WasmBuilder {
	/// Flags that should be appended to `RUST_FLAGS` env variable.
	rust_flags: Vec<String>,
	/// The name of the file that is being generated in `OUT_DIR`.
	///
	/// Defaults to `wasm_binary.rs`.
	file_name: Option<String>,
	/// Features that should be enabled when building the wasm binary.
	features_to_enable: Vec<String>,
}

impl WasmBuilder {
	/// Create a new instance of the builder.
	pub fn new() -> WasmBuilderSelectProject {
		WasmBuilderSelectProject { _ignore: () }
	}

	/// Enable exporting `__heap_base` as global variable in the WASM binary.
	///
	/// This adds `-Clink-arg=--export=__heap_base` to `RUST_FLAGS`.
	pub fn export_heap_base(mut self) -> Self {
		self.rust_flags.push("-Clink-arg=--export=__heap_base".into());
		self
	}

	/// Set the name of the file that will be generated in `OUT_DIR`.
	///
	/// This file needs to be included to get access to the build WASM binary.
	///
	/// If this function is not called, `file_name` defaults to `wasm_binary.rs`
	pub fn set_file_name(mut self, file_name: impl Into<String>) -> Self {
		self.file_name = Some(file_name.into());
		self
	}

	/// Instruct the linker to import the memory into the WASM binary.
	///
	/// This adds `-C link-arg=--import-memory` to `RUST_FLAGS`.
	pub fn import_memory(mut self) -> Self {
		self.rust_flags.push("-C link-arg=--import-memory".into());
		self
	}

	/// Append the given `flag` to `RUST_FLAGS`.
	///
	/// `flag` is appended as is, so it needs to be a valid flag.
	pub fn append_to_rust_flags(mut self, flag: impl Into<String>) -> Self {
		self.rust_flags.push(flag.into());
		self
	}

	/// Enable the given feature when building the wasm binary.
	///
	/// `feature` needs to be a valid feature that is defined in the project `Cargo.toml`.
	pub fn enable_feature(mut self, feature: impl Into<String>) -> Self {
		self.features_to_enable.push(feature.into());
		self
	}

	/// Build the WASM binary.
	pub fn build(self) {
		let out_dir = PathBuf::from(env::var("OUT_DIR").expect("`OUT_DIR` is set by cargo!"));
		let file_path =
			out_dir.join(self.file_name.clone().unwrap_or_else(|| "wasm_binary.rs".into()));

		provide_dummy_wasm_binary_if_not_exist(&file_path);
	}
}

/// Provide a dummy WASM binary if there doesn't exist one.
fn provide_dummy_wasm_binary_if_not_exist(file_path: &Path) {
	if !file_path.exists() {
		crate::write_file_if_changed(
			file_path,
			"pub const WASM_BINARY: Option<&[u8]> = None;\
			 pub const WASM_BINARY_BLOATY: Option<&[u8]> = None;",
		);
	}
}
