// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! # WASM builder runner
//!
//! Since cargo contains many bugs when it comes to correct dependency and feature
//! resolution, we need this little tool. See <https://github.com/rust-lang/cargo/issues/5730> for
//! more information.
//!
//! It will create a project that will call `substrate-wasm-builder` to prevent any dependencies
//! from `substrate-wasm-builder` influencing the main project's dependencies.
//!
//! For more information see <https://crates.io/substrate-wasm-builder>

use std::{
	env, process::{Command, self}, fs, path::{PathBuf, Path}, hash::{Hash, Hasher},
	collections::hash_map::DefaultHasher,
};

/// Environment variable that tells us to skip building the WASM binary.
const SKIP_BUILD_ENV: &str = "SKIP_WASM_BUILD";

/// Environment variable that tells us to create a dummy WASM binary.
///
/// This is useful for `cargo check` to speed-up the compilation.
///
/// # Caution
///
/// Enabling this option will just provide `&[]` as WASM binary.
const DUMMY_WASM_BINARY_ENV: &str = "BUILD_DUMMY_WASM_BINARY";

/// Environment variable that makes sure the WASM build is triggered.
const TRIGGER_WASM_BUILD_ENV: &str = "TRIGGER_WASM_BUILD";

/// Replace all backslashes with slashes.
fn replace_back_slashes<T: ToString>(path: T) -> String {
	path.to_string().replace("\\", "/")
}

/// Returns the manifest dir from the `CARGO_MANIFEST_DIR` env.
fn get_manifest_dir() -> PathBuf {
	env::var("CARGO_MANIFEST_DIR")
		.expect("`CARGO_MANIFEST_DIR` is always set for `build.rs` files; qed")
		.into()
}

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
	pub fn with_current_project(self) -> WasmBuilderSelectSource {
		WasmBuilderSelectSource(get_manifest_dir().join("Cargo.toml"))
	}

	/// Use the given `path` as project for building the WASM binary.
	///
	/// Returns an error if the given `path` does not points to a `Cargo.toml`.
	pub fn with_project(
		self,
		path: impl Into<PathBuf>,
	) -> Result<WasmBuilderSelectSource, &'static str> {
		let path = path.into();

		if path.ends_with("Cargo.toml") {
			Ok(WasmBuilderSelectSource(path))
		} else {
			Err("Project path must point to the `Cargo.toml` of the project")
		}
	}
}

/// Second step of the [`WasmBuilder`] to set the source of the `wasm-builder`.
pub struct WasmBuilderSelectSource(PathBuf);

impl WasmBuilderSelectSource {
	/// Use the given `path` as source for `wasm-builder`.
	///
	/// The `path` must be relative and point to the directory that contains the `Cargo.toml` for
	/// `wasm-builder`.
	pub fn with_wasm_builder_from_path(self, path: &'static str) -> WasmBuilder {
		WasmBuilder {
			source: WasmBuilderSource::Path(path),
			rust_flags: Vec::new(),
			file_name: None,
			project_cargo_toml: self.0,
		}
	}

	/// Use the given `repo` and `rev` as source for `wasm-builder`.
	pub fn with_wasm_builder_from_git(self, repo: &'static str, rev: &'static str) -> WasmBuilder {
		WasmBuilder {
			source: WasmBuilderSource::Git { repo, rev },
			rust_flags: Vec::new(),
			file_name: None,
			project_cargo_toml: self.0,
		}
	}

	/// Use the given `version` to fetch `wasm-builder` source from crates.io.
	pub fn with_wasm_builder_from_crates(self, version: &'static str) -> WasmBuilder {
		WasmBuilder {
			source: WasmBuilderSource::Crates(version),
			rust_flags: Vec::new(),
			file_name: None,
			project_cargo_toml: self.0,
		}
	}

	/// Use the given `version` to fetch `wasm-builder` source from crates.io or use
	/// the given `path` as source.
	///
	/// The `path` must be relative and point to the directory that contains the `Cargo.toml` for
	/// `wasm-builder`.
	pub fn with_wasm_builder_from_crates_or_path(
		self,
		version: &'static str,
		path: &'static str,
	) -> WasmBuilder {
		WasmBuilder {
			source: WasmBuilderSource::CratesOrPath { version, path },
			rust_flags: Vec::new(),
			file_name: None,
			project_cargo_toml: self.0,
		}
	}

	/// Use the given `source` as source for `wasm-builder`.
	pub fn with_wasm_builder_source(self, source: WasmBuilderSource) -> WasmBuilder {
		WasmBuilder {
			source,
			rust_flags: Vec::new(),
			file_name: None,
			project_cargo_toml: self.0,
		}
	}
}

/// The builder for building a wasm binary.
///
/// The builder itself is seperated into multiple structs to make the setup type safe.
///
/// Building a wasm binary:
///
/// 1. Call [`WasmBuilder::new`] to create a new builder.
/// 2. Select the project to build using the methods of [`WasmBuilderSelectProject`].
/// 3. Select the source of the `wasm-builder` crate using the methods of
///    [`WasmBuilderSelectSource`].
/// 4. Set additional `RUST_FLAGS` or a different name for the file containing the WASM code
///    using methods of [`WasmBuilder`].
/// 5. Build the WASM binary using [`Self::build`].
pub struct WasmBuilder {
	/// Where should we pull the `wasm-builder` crate from.
	source: WasmBuilderSource,
	/// Flags that should be appended to `RUST_FLAGS` env variable.
	rust_flags: Vec<String>,
	/// The name of the file that is being generated in `OUT_DIR`.
	///
	/// Defaults to `wasm_binary.rs`.
	file_name: Option<String>,
	/// The path to the `Cargo.toml` of the project that should be build
	/// for wasm.
	project_cargo_toml: PathBuf,
}

impl WasmBuilder {
	/// Create a new instance of the builder.
	pub fn new() -> WasmBuilderSelectProject {
		WasmBuilderSelectProject {
			_ignore: (),
		}
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

	/// Build the WASM binary.
	pub fn build(self) {
		if check_skip_build() {
			// If we skip the build, we still want to make sure to be called when an env variable
			// changes
			generate_rerun_if_changed_instructions();
			return;
		}

		let out_dir = PathBuf::from(env::var("OUT_DIR").expect("`OUT_DIR` is set by cargo!"));
		let file_path = out_dir.join(self.file_name.unwrap_or_else(|| "wasm_binary.rs".into()));

		// Hash the path to the project cargo toml.
		let mut hasher = DefaultHasher::new();
		self.project_cargo_toml.hash(&mut hasher);

		let project_name = env::var("CARGO_PKG_NAME").expect("`CARGO_PKG_NAME` is set by cargo!");
		// Make sure the `wasm-builder-runner` path is unique by concatenating the name of the
		// project that is compiling the WASM binary with the hash of the path to the project that
		// should be compiled as WASM binary.
		let project_folder = get_workspace_root()
			.join(format!("{}{}", project_name, hasher.finish()));

		if check_provide_dummy_wasm_binary() {
			provide_dummy_wasm_binary(&file_path);
		} else {
			create_project(
				&project_folder,
				&file_path,
				self.source,
				&self.project_cargo_toml,
				&self.rust_flags.into_iter().map(|f| format!("{} ", f)).collect::<String>(),
			);
			run_project(&project_folder);
		}

		// As last step we need to generate our `rerun-if-changed` stuff. If a build fails, we don't
		// want to spam the output!
		generate_rerun_if_changed_instructions();
	}
}

/// The `wasm-builder` dependency source.
pub enum WasmBuilderSource {
	/// The relative path to the source code from the current manifest dir.
	Path(&'static str),
	/// The git repository that contains the source code.
	Git {
		repo: &'static str,
		rev: &'static str,
	},
	/// Use the given version released on crates.io.
	Crates(&'static str),
	/// Use the given version released on crates.io or from the given path.
	CratesOrPath {
		version: &'static str,
		path: &'static str,
	}
}

impl WasmBuilderSource {
	/// Convert to a valid cargo source declaration.
	///
	/// `absolute_path` - The manifest dir.
	fn to_cargo_source(&self, manifest_dir: &Path) -> String {
		match self {
			WasmBuilderSource::Path(path) => {
				replace_back_slashes(format!("path = \"{}\"", manifest_dir.join(path).display()))
			}
			WasmBuilderSource::Git { repo, rev } => {
				format!("git = \"{}\", rev=\"{}\"", repo, rev)
			}
			WasmBuilderSource::Crates(version) => {
				format!("version = \"{}\"", version)
			}
			WasmBuilderSource::CratesOrPath { version, path } => {
				replace_back_slashes(
					format!(
						"path = \"{}\", version = \"{}\"",
						manifest_dir.join(path).display(),
						version
					)
				)
			}
		}
	}
}

/// Build the currently built project as WASM binary and extend `RUSTFLAGS` with the given rustflags.
///
/// For more information, see [`build_current_project`].
#[deprecated(
	since = "1.0.5",
	note = "Please switch to [`WasmBuilder`]",
)]
pub fn build_current_project_with_rustflags(
	file_name: &str,
	wasm_builder_source: WasmBuilderSource,
	default_rust_flags: &str,
) {
	WasmBuilder::new()
		.with_current_project()
		.with_wasm_builder_source(wasm_builder_source)
		.append_to_rust_flags(default_rust_flags)
		.set_file_name(file_name)
		.build()
}

/// Build the currently built project as WASM binary.
///
/// The current project is determined using the `CARGO_MANIFEST_DIR` environment variable.
///
/// `file_name` - The name of the file being generated in the `OUT_DIR`. The file contains the
///               constant `WASM_BINARY` which contains the build wasm binary.
/// `wasm_builder_path` - Path to the wasm-builder project, relative to `CARGO_MANIFEST_DIR`.
#[deprecated(
	since = "1.0.5",
	note = "Please switch to [`WasmBuilder`]",
)]
pub fn build_current_project(file_name: &str, wasm_builder_source: WasmBuilderSource) {
	#[allow(deprecated)]
	build_current_project_with_rustflags(file_name, wasm_builder_source, "");
}

/// Returns the root path of the wasm-builder workspace.
///
/// The wasm-builder workspace contains all wasm-builder's projects.
fn get_workspace_root() -> PathBuf {
	let out_dir_env = env::var("OUT_DIR").expect("`OUT_DIR` is set by cargo!");
	let mut out_dir = PathBuf::from(&out_dir_env);

	loop {
		match out_dir.parent() {
			Some(parent) if out_dir.ends_with("build") => return parent.join("wbuild-runner"),
			_ => if !out_dir.pop() {
				break;
			}
		}
	}

	panic!("Could not find target dir in: {}", out_dir_env)
}

fn create_project(
	project_folder: &Path,
	file_path: &Path,
	wasm_builder_source: WasmBuilderSource,
	cargo_toml_path: &Path,
	default_rustflags: &str,
) {
	fs::create_dir_all(project_folder.join("src"))
		.expect("WASM build runner dir create can not fail; qed");

	fs::write(
		project_folder.join("Cargo.toml"),
		format!(
			r#"
				[package]
				name = "wasm-build-runner-impl"
				version = "1.0.0"
				edition = "2018"

				[dependencies]
				substrate-wasm-builder = {{ {wasm_builder_source} }}

				[workspace]
			"#,
			wasm_builder_source = wasm_builder_source.to_cargo_source(&get_manifest_dir()),
		)
	).expect("WASM build runner `Cargo.toml` writing can not fail; qed");

	fs::write(
		project_folder.join("src/main.rs"),
		format!(
			r#"
				use substrate_wasm_builder::build_project_with_default_rustflags;

				fn main() {{
					build_project_with_default_rustflags(
						"{file_path}",
						"{cargo_toml_path}",
						"{default_rustflags}",
					)
				}}
			"#,
			file_path = replace_back_slashes(file_path.display()),
			cargo_toml_path = replace_back_slashes(cargo_toml_path.display()),
			default_rustflags = default_rustflags,
		)
	).expect("WASM build runner `main.rs` writing can not fail; qed");
}

fn run_project(project_folder: &Path) {
	let cargo = env::var("CARGO").expect("`CARGO` env variable is always set when executing `build.rs`.");
	let mut cmd = Command::new(cargo);
	cmd.arg("run").arg(format!("--manifest-path={}", project_folder.join("Cargo.toml").display()));

	if env::var("DEBUG") != Ok(String::from("true")) {
		cmd.arg("--release");
	}

	// Make sure we always run the `wasm-builder` project for the `HOST` architecture.
	let host_triple = env::var("HOST").expect("`HOST` is always set when executing `build.rs`.");
	cmd.arg(&format!("--target={}", host_triple));

	// Unset the `CARGO_TARGET_DIR` to prevent a cargo deadlock (cargo locks a target dir exclusive).
	// The runner project is created in `CARGO_TARGET_DIR` and executing it will create a sub target
	// directory inside of `CARGO_TARGET_DIR`.
	cmd.env_remove("CARGO_TARGET_DIR");

	if !cmd.status().map(|s| s.success()).unwrap_or(false) {
		// Don't spam the output with backtraces when a build failed!
		process::exit(1);
	}
}

/// Generate the name of the skip build environment variable for the current crate.
fn generate_crate_skip_build_env_name() -> String {
	format!(
		"SKIP_{}_WASM_BUILD",
		env::var("CARGO_PKG_NAME").expect("Package name is set").to_uppercase().replace('-', "_"),
	)
}

/// Checks if the build of the WASM binary should be skipped.
fn check_skip_build() -> bool {
	env::var(SKIP_BUILD_ENV).is_ok() || env::var(generate_crate_skip_build_env_name()).is_ok()
}

/// Check if we should provide a dummy WASM binary.
fn check_provide_dummy_wasm_binary() -> bool {
	env::var(DUMMY_WASM_BINARY_ENV).is_ok()
}

/// Provide the dummy WASM binary
fn provide_dummy_wasm_binary(file_path: &Path) {
	fs::write(
		file_path,
		"pub const WASM_BINARY: Option<&[u8]> = None; pub const WASM_BINARY_BLOATY: Option<&[u8]> = None;",
	).expect("Writing dummy WASM binary should not fail");
}

/// Generate the `rerun-if-changed` instructions for cargo to make sure that the WASM binary is
/// rebuilt when needed.
fn generate_rerun_if_changed_instructions() {
	// Make sure that the `build.rs` is called again if one of the following env variables changes.
	println!("cargo:rerun-if-env-changed={}", SKIP_BUILD_ENV);
	println!("cargo:rerun-if-env-changed={}", DUMMY_WASM_BINARY_ENV);
	println!("cargo:rerun-if-env-changed={}", TRIGGER_WASM_BUILD_ENV);
	println!("cargo:rerun-if-env-changed={}", generate_crate_skip_build_env_name());
}
