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

//! # Wasm builder is a utility for building a project as a Wasm binary
//!
//! The Wasm builder is a tool that integrates the process of building the WASM binary of your project into the main
//! `cargo` build process.
//!
//! ## Project setup
//!
//! A project that should be compiled as a Wasm binary needs to:
//!
//! 1. Add a `build.rs` file.
//! 2. Add `substrate-wasm-builder` as dependency into `build-dependencies`.
//!
//! The `build.rs` file needs to contain the following code:
//!
//! ```ignore
//! use wasm_builder_runner::{build_current_project, WasmBuilderSource};
//!
//! fn main() {
//! 	build_current_project(
//! 		// The name of the file being generated in out-dir.
//! 		"wasm_binary.rs",
//! 		// How to include wasm-builder, in this case from crates.io.
//! 		WasmBuilderSource::Crates("1.0.0"),
//! 	);
//! }
//! ```
//!
//! As the final step, you need to add the following to your project:
//!
//! ```ignore
//! include!(concat!(env!("OUT_DIR"), "/wasm_binary.rs"));
//! ```
//!
//! This will include the generated Wasm binary as two constants `WASM_BINARY` and `WASM_BINARY_BLOATY`.
//! The former is a compact Wasm binary and the latter is not compacted.
//!
//! ### Feature
//!
//! Wasm builder supports to enable cargo features while building the Wasm binary. By default it will
//! enable all features in the wasm build that are enabled for the native build except the
//! `default` and `std` features. Besides that, wasm builder supports the special `runtime-wasm`
//! feature. This `runtime-wasm` feature will be enabled by the wasm builder when it compiles the
//! Wasm binary. If this feature is not present, it will not be enabled.
//!
//! ## Environment variables
//!
//! By using environment variables, you can configure which Wasm binaries are built and how:
//!
//! - `SKIP_WASM_BUILD` - Skips building any wasm binary. This is useful when only native should be recompiled.
//! - `BUILD_DUMMY_WASM_BINARY` - Builds dummy wasm binaries. These dummy binaries are empty and useful
//!                              for `cargo check` runs.
//! - `WASM_BUILD_TYPE` - Sets the build type for building wasm binaries. Supported values are `release` or `debug`.
//!                       By default the build type is equal to the build type used by the main build.
//! - `FORCE_WASM_BUILD` - Can be set to force a wasm build. On subsequent calls the value of the variable
//!                        needs to change. As wasm builder instructs `cargo` to watch for file changes
//!                        this environment variable should only be required in certain circumstances.
//! - `WASM_BUILD_RUSTFLAGS` - Extend `RUSTFLAGS` given to `cargo build` while building the wasm binary.
//! - `WASM_BUILD_NO_COLOR` - Disable color output of the wasm build.
//! - `WASM_TARGET_DIRECTORY` - Will copy any build wasm binary to the given directory. The path needs
//!                            to be absolute.
//! - `WASM_BUILD_TOOLCHAIN` - The toolchain that should be used to build the wasm binaries. The
//!                            format needs to be the same as used by cargo, e.g. `nightly-2020-02-20`.
//!
//! Each project can be skipped individually by using the environment variable `SKIP_PROJECT_NAME_WASM_BUILD`.
//! Where `PROJECT_NAME` needs to be replaced by the name of the cargo project, e.g. `node-runtime` will
//! be `NODE_RUNTIME`.
//!
//! ## Prerequisites:
//!
//! Wasm builder requires the following prerequisites for building the Wasm binary:
//!
//! - rust nightly + `wasm32-unknown-unknown` toolchain
//!
//! If a specific rust nightly is installed with `rustup`, it is important that the wasm target is installed
//! as well. For example if installing the rust nightly from 20.02.2020 using `rustup install nightly-2020-02-20`,
//! the wasm target needs to be installed as well `rustup target add wasm32-unknown-unknown --toolchain nightly-2020-02-20`.

use std::{env, fs, path::PathBuf, process::{Command, self}, io::BufRead};

mod prerequisites;
mod wasm_project;

/// Environment variable that tells us to skip building the wasm binary.
const SKIP_BUILD_ENV: &str = "SKIP_WASM_BUILD";

/// Environment variable to force a certain build type when building the wasm binary.
/// Expects "debug" or "release" as value.
///
/// By default the WASM binary uses the same build type as the main cargo build.
const WASM_BUILD_TYPE_ENV: &str = "WASM_BUILD_TYPE";

/// Environment variable to extend the `RUSTFLAGS` variable given to the wasm build.
const WASM_BUILD_RUSTFLAGS_ENV: &str = "WASM_BUILD_RUSTFLAGS";

/// Environment variable to set the target directory to copy the final wasm binary.
///
/// The directory needs to be an absolute path.
const WASM_TARGET_DIRECTORY: &str = "WASM_TARGET_DIRECTORY";

/// Environment variable to disable color output of the wasm build.
const WASM_BUILD_NO_COLOR: &str = "WASM_BUILD_NO_COLOR";

/// Environment variable to set the toolchain used to compile the wasm binary.
const WASM_BUILD_TOOLCHAIN: &str = "WASM_BUILD_TOOLCHAIN";

/// Build the currently built project as wasm binary.
///
/// The current project is determined by using the `CARGO_MANIFEST_DIR` environment variable.
///
/// `file_name` - The name + path of the file being generated. The file contains the
///               constant `WASM_BINARY`, which contains the built WASM binary.
/// `cargo_manifest` - The path to the `Cargo.toml` of the project that should be built.
pub fn build_project(file_name: &str, cargo_manifest: &str) {
	build_project_with_default_rustflags(file_name, cargo_manifest, "");
}

/// Build the currently built project as wasm binary.
///
/// The current project is determined by using the `CARGO_MANIFEST_DIR` environment variable.
///
/// `file_name` - The name + path of the file being generated. The file contains the
///               constant `WASM_BINARY`, which contains the built WASM binary.
/// `cargo_manifest` - The path to the `Cargo.toml` of the project that should be built.
/// `default_rustflags` - Default `RUSTFLAGS` that will always be set for the build.
pub fn build_project_with_default_rustflags(
	file_name: &str,
	cargo_manifest: &str,
	default_rustflags: &str,
) {
	if check_skip_build() {
		return;
	}

	let cargo_manifest = PathBuf::from(cargo_manifest);

	if !cargo_manifest.exists() {
		panic!("'{}' does not exist!", cargo_manifest.display());
	}

	if !cargo_manifest.ends_with("Cargo.toml") {
		panic!("'{}' no valid path to a `Cargo.toml`!", cargo_manifest.display());
	}

	if let Some(err_msg) = prerequisites::check() {
		eprintln!("{}", err_msg);
		process::exit(1);
	}

	let (wasm_binary, bloaty) = wasm_project::create_and_compile(
		&cargo_manifest,
		default_rustflags,
	);

	let (wasm_binary, wasm_binary_bloaty) = if let Some(wasm_binary) = wasm_binary {
		(
			wasm_binary.wasm_binary_path_escaped(),
			bloaty.wasm_binary_bloaty_path_escaped(),
		)
	} else {
		(
			bloaty.wasm_binary_bloaty_path_escaped(),
			bloaty.wasm_binary_bloaty_path_escaped(),
		)
	};

	write_file_if_changed(
			file_name.into(),
			format!(
				r#"
					pub const WASM_BINARY: Option<&[u8]> = Some(include_bytes!("{wasm_binary}"));
					pub const WASM_BINARY_BLOATY: Option<&[u8]> = Some(include_bytes!("{wasm_binary_bloaty}"));
				"#,
				wasm_binary = wasm_binary,
				wasm_binary_bloaty = wasm_binary_bloaty,
			),
		);
}

/// Checks if the build of the WASM binary should be skipped.
fn check_skip_build() -> bool {
	env::var(SKIP_BUILD_ENV).is_ok()
}

/// Write to the given `file` if the `content` is different.
fn write_file_if_changed(file: PathBuf, content: String) {
	if fs::read_to_string(&file).ok().as_ref() != Some(&content) {
		fs::write(&file, content).unwrap_or_else(|_| panic!("Writing `{}` can not fail!", file.display()));
	}
}

/// Copy `src` to `dst` if the `dst` does not exist or is different.
fn copy_file_if_changed(src: PathBuf, dst: PathBuf) {
	let src_file = fs::read_to_string(&src).ok();
	let dst_file = fs::read_to_string(&dst).ok();

	if src_file != dst_file {
		fs::copy(&src, &dst)
			.unwrap_or_else(|_| panic!("Copying `{}` to `{}` can not fail; qed", src.display(), dst.display()));
	}
}

/// Get a cargo command that compiles with nightly
fn get_nightly_cargo() -> CargoCommand {
	let env_cargo = CargoCommand::new(
		&env::var("CARGO").expect("`CARGO` env variable is always set by cargo"),
	);
	let default_cargo = CargoCommand::new("cargo");
	let rustup_run_nightly = CargoCommand::new_with_args("rustup", &["run", "nightly", "cargo"]);
	let wasm_toolchain = env::var(WASM_BUILD_TOOLCHAIN).ok();

	// First check if the user requested a specific toolchain
	if let Some(cmd) = wasm_toolchain.and_then(|t| get_rustup_nightly(Some(t))) {
		cmd
	} else if env_cargo.is_nightly() {
		env_cargo
	} else if default_cargo.is_nightly() {
		default_cargo
	} else if rustup_run_nightly.is_nightly() {
		rustup_run_nightly
	} else {
		// If no command before provided us with a nightly compiler, we try to search one
		// with rustup. If that fails as well, we return the default cargo and let the prequisities
		// check fail.
		get_rustup_nightly(None).unwrap_or(default_cargo)
	}
}

/// Get a nightly from rustup. If `selected` is `Some(_)`, a `CargoCommand` using the given
/// nightly is returned.
fn get_rustup_nightly(selected: Option<String>) -> Option<CargoCommand> {
	let host = format!("-{}", env::var("HOST").expect("`HOST` is always set by cargo"));

	let version = match selected {
		Some(selected) => selected,
		None => {
			let output = Command::new("rustup").args(&["toolchain", "list"]).output().ok()?.stdout;
			let lines = output.as_slice().lines();

			let mut latest_nightly = None;
			for line in lines.filter_map(|l| l.ok()) {
				if line.starts_with("nightly-") && line.ends_with(&host) {
					// Rustup prints them sorted
					latest_nightly = Some(line.clone());
				}
			}

			latest_nightly?.trim_end_matches(&host).into()
		}
	};

	Some(CargoCommand::new_with_args("rustup", &["run", &version, "cargo"]))
}

/// Builder for cargo commands
#[derive(Debug)]
struct CargoCommand {
	program: String,
	args: Vec<String>,
}

impl CargoCommand {
	fn new(program: &str) -> Self {
		CargoCommand { program: program.into(), args: Vec::new() }
	}

	fn new_with_args(program: &str, args: &[&str]) -> Self {
		CargoCommand {
			program: program.into(),
			args: args.iter().map(ToString::to_string).collect(),
		}
	}

	fn command(&self) -> Command {
		let mut cmd = Command::new(&self.program);
		cmd.args(&self.args);
		cmd
	}

	/// Check if the supplied cargo command is a nightly version
	fn is_nightly(&self) -> bool {
		// `RUSTC_BOOTSTRAP` tells a stable compiler to behave like a nightly. So, when this env
		// variable is set, we can assume that whatever rust compiler we have, it is a nightly compiler.
		// For "more" information, see:
		// https://github.com/rust-lang/rust/blob/fa0f7d0080d8e7e9eb20aa9cbf8013f96c81287f/src/libsyntax/feature_gate/check.rs#L891
		env::var("RUSTC_BOOTSTRAP").is_ok() ||
			self.command()
				.arg("--version")
				.output()
				.map_err(|_| ())
				.and_then(|o| String::from_utf8(o.stdout).map_err(|_| ()))
				.unwrap_or_default()
				.contains("-nightly")
	}
}

/// Returns `true` when color output is enabled.
fn color_output_enabled() -> bool {
	env::var(crate::WASM_BUILD_NO_COLOR).is_err()
}
