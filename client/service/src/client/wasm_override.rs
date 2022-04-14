// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! # WASM Local Blob-Override
//!
//! WASM Local blob override provides tools to replace on-chain WASM with custom WASM.
//! These customized WASM blobs may include functionality that is not included in the
//! on-chain WASM, such as tracing or debugging information. This extra information is especially
//! useful in external scenarios, like exchanges or archive nodes.
//!
//! ## Usage
//!
//! WASM overrides may be enabled with the `--wasm-runtime-overrides` argument. The argument
//! expects a path to a directory that holds custom WASM.
//!
//! Any file ending in '.wasm' will be scraped and instantiated as a WASM blob. WASM can be built by
//! compiling the required runtime with the changes needed. For example, compiling a runtime with
//! tracing enabled would produce a WASM blob that can used.
//!
//! A custom WASM blob will override on-chain WASM if the spec version matches. If it is
//! required to overrides multiple runtimes, multiple WASM blobs matching each of the spec versions
//! needed must be provided in the given directory.

use sc_executor::RuntimeVersionOf;
use sp_blockchain::Result;
use sp_core::traits::{FetchRuntimeCode, RuntimeCode, WrappedRuntimeCode};
use sp_state_machine::BasicExternalities;
use sp_version::RuntimeVersion;
use std::{
	collections::{hash_map::DefaultHasher, HashMap},
	fs,
	hash::Hasher as _,
	path::{Path, PathBuf},
	time::{Duration, Instant},
};

/// The interval in that we will print a warning when a wasm blob `spec_name`
/// doesn't match with the on-chain `spec_name`.
const WARN_INTERVAL: Duration = Duration::from_secs(30);

/// Auxiliary structure that holds a wasm blob and its hash.
#[derive(Debug)]
struct WasmBlob {
	/// The actual wasm blob, aka the code.
	code: Vec<u8>,
	/// The hash of [`Self::code`].
	hash: Vec<u8>,
	/// The path where this blob was found.
	path: PathBuf,
	/// The `spec_name` found in the runtime version of this blob.
	spec_name: String,
	/// When was the last time we have warned about the wasm blob having
	/// a wrong `spec_name`?
	last_warn: parking_lot::Mutex<Option<Instant>>,
}

impl WasmBlob {
	fn new(code: Vec<u8>, hash: Vec<u8>, path: PathBuf, spec_name: String) -> Self {
		Self { code, hash, path, spec_name, last_warn: Default::default() }
	}

	fn runtime_code(&self, heap_pages: Option<u64>) -> RuntimeCode {
		RuntimeCode { code_fetcher: self, hash: self.hash.clone(), heap_pages }
	}
}

/// Make a hash out of a byte string using the default rust hasher
fn make_hash<K: std::hash::Hash + ?Sized>(val: &K) -> Vec<u8> {
	let mut state = DefaultHasher::new();
	val.hash(&mut state);
	state.finish().to_le_bytes().to_vec()
}

impl FetchRuntimeCode for WasmBlob {
	fn fetch_runtime_code<'a>(&'a self) -> Option<std::borrow::Cow<'a, [u8]>> {
		Some(self.code.as_slice().into())
	}
}

#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
pub enum WasmOverrideError {
	#[error("Failed to get runtime version: {0}")]
	VersionInvalid(String),

	#[error("WASM override IO error")]
	Io(PathBuf, #[source] std::io::Error),

	#[error("Overwriting WASM requires a directory where local \
	WASM is stored. {} is not a directory", .0.display())]
	NotADirectory(PathBuf),

	#[error("Duplicate WASM Runtimes found: \n{}\n", .0.join("\n") )]
	DuplicateRuntime(Vec<String>),
}

impl From<WasmOverrideError> for sp_blockchain::Error {
	fn from(err: WasmOverrideError) -> Self {
		Self::Application(Box::new(err))
	}
}

/// Scrapes WASM from a folder and returns WASM from that folder
/// if the runtime spec version matches.
#[derive(Debug)]
pub struct WasmOverride {
	// Map of runtime spec version -> Wasm Blob
	overrides: HashMap<u32, WasmBlob>,
}

impl WasmOverride {
	pub fn new<P, E>(path: P, executor: &E) -> Result<Self>
	where
		P: AsRef<Path>,
		E: RuntimeVersionOf,
	{
		let overrides = Self::scrape_overrides(path.as_ref(), executor)?;
		Ok(Self { overrides })
	}

	/// Gets an override by it's runtime spec version.
	///
	/// Returns `None` if an override for a spec version does not exist.
	pub fn get<'a, 'b: 'a>(
		&'b self,
		spec: &u32,
		pages: Option<u64>,
		spec_name: &str,
	) -> Option<RuntimeCode<'a>> {
		self.overrides.get(spec).and_then(|w| {
			if spec_name == w.spec_name {
				Some(w.runtime_code(pages))
			} else {
				let mut last_warn = w.last_warn.lock();
				let now = Instant::now();

				if last_warn.map_or(true, |l| l + WARN_INTERVAL <= now) {
					*last_warn = Some(now);

					tracing::warn!(
						target = "wasm_overrides",
						on_chain_spec_name = %spec_name,
						override_spec_name = %w.spec_name,
						spec_version = %spec,
						wasm_file = %w.path.display(),
						"On chain and override `spec_name` do not match! Ignoring override.",
					);
				}

				None
			}
		})
	}

	/// Scrapes a folder for WASM runtimes.
	/// Returns a hashmap of the runtime version and wasm runtime code.
	fn scrape_overrides<E>(dir: &Path, executor: &E) -> Result<HashMap<u32, WasmBlob>>
	where
		E: RuntimeVersionOf,
	{
		let handle_err = |e: std::io::Error| -> sp_blockchain::Error {
			WasmOverrideError::Io(dir.to_owned(), e).into()
		};

		if !dir.is_dir() {
			return Err(WasmOverrideError::NotADirectory(dir.to_owned()).into())
		}

		let mut overrides = HashMap::new();
		let mut duplicates = Vec::new();
		for entry in fs::read_dir(dir).map_err(handle_err)? {
			let entry = entry.map_err(handle_err)?;
			let path = entry.path();
			match path.extension().and_then(|e| e.to_str()) {
				Some("wasm") => {
					let code = fs::read(&path).map_err(handle_err)?;
					let code_hash = make_hash(&code);
					let version = Self::runtime_version(executor, &code, &code_hash, Some(128))?;

					tracing::info!(
						target: "wasm_overrides",
						version = %version,
						file = %path.display(),
						"Found wasm override.",
					);

					let wasm =
						WasmBlob::new(code, code_hash, path.clone(), version.spec_name.to_string());

					if let Some(other) = overrides.insert(version.spec_version, wasm) {
						tracing::info!(
							target: "wasm_overrides",
							first = %other.path.display(),
							second = %path.display(),
							%version,
							"Found duplicate spec version for runtime.",
						);
						duplicates.push(path.display().to_string());
					}
				},
				_ => (),
			}
		}

		if !duplicates.is_empty() {
			return Err(WasmOverrideError::DuplicateRuntime(duplicates).into())
		}

		Ok(overrides)
	}

	fn runtime_version<E>(
		executor: &E,
		code: &[u8],
		code_hash: &[u8],
		heap_pages: Option<u64>,
	) -> Result<RuntimeVersion>
	where
		E: RuntimeVersionOf,
	{
		let mut ext = BasicExternalities::default();
		executor
			.runtime_version(
				&mut ext,
				&RuntimeCode {
					code_fetcher: &WrappedRuntimeCode(code.into()),
					heap_pages,
					hash: code_hash.into(),
				},
			)
			.map_err(|e| WasmOverrideError::VersionInvalid(e.to_string()).into())
	}
}

/// Returns a WasmOverride struct filled with dummy data for testing.
#[cfg(test)]
pub fn dummy_overrides() -> WasmOverride {
	let mut overrides = HashMap::new();
	overrides.insert(
		0,
		WasmBlob::new(vec![0, 0, 0, 0, 0, 0, 0, 0], vec![0], PathBuf::new(), "test".into()),
	);
	overrides.insert(
		1,
		WasmBlob::new(vec![1, 1, 1, 1, 1, 1, 1, 1], vec![1], PathBuf::new(), "test".into()),
	);
	overrides.insert(
		2,
		WasmBlob::new(vec![2, 2, 2, 2, 2, 2, 2, 2], vec![2], PathBuf::new(), "test".into()),
	);
	WasmOverride { overrides }
}

#[cfg(test)]
mod tests {
	use super::*;
	use sc_executor::{NativeElseWasmExecutor, WasmExecutionMethod};
	use std::fs::{self, File};
	use substrate_test_runtime_client::LocalExecutorDispatch;

	fn wasm_test<F>(fun: F)
	where
		F: Fn(&Path, &[u8], &NativeElseWasmExecutor<LocalExecutorDispatch>),
	{
		let exec =
			NativeElseWasmExecutor::<substrate_test_runtime_client::LocalExecutorDispatch>::new(
				WasmExecutionMethod::Interpreted,
				Some(128),
				1,
				2,
			);
		let bytes = substrate_test_runtime::wasm_binary_unwrap();
		let dir = tempfile::tempdir().expect("Create a temporary directory");
		fun(dir.path(), bytes, &exec);
		dir.close().expect("Temporary Directory should close");
	}

	#[test]
	fn should_get_runtime_version() {
		let executor = NativeElseWasmExecutor::<LocalExecutorDispatch>::new(
			WasmExecutionMethod::Interpreted,
			Some(128),
			1,
			2,
		);

		let version = WasmOverride::runtime_version(
			&executor,
			substrate_test_runtime::wasm_binary_unwrap(),
			&[1],
			Some(128),
		)
		.expect("should get the `RuntimeVersion` of the test-runtime wasm blob");
		assert_eq!(version.spec_version, 2);
	}

	#[test]
	fn should_scrape_wasm() {
		wasm_test(|dir, wasm_bytes, exec| {
			fs::write(dir.join("test.wasm"), wasm_bytes).expect("Create test file");
			let overrides =
				WasmOverride::scrape_overrides(dir, exec).expect("HashMap of u32 and WasmBlob");
			let wasm = overrides.get(&2).expect("WASM binary");
			assert_eq!(wasm.code, substrate_test_runtime::wasm_binary_unwrap().to_vec())
		});
	}

	#[test]
	fn should_check_for_duplicates() {
		wasm_test(|dir, wasm_bytes, exec| {
			fs::write(dir.join("test0.wasm"), wasm_bytes).expect("Create test file");
			fs::write(dir.join("test1.wasm"), wasm_bytes).expect("Create test file");
			let scraped = WasmOverride::scrape_overrides(dir, exec);

			match scraped {
				Err(sp_blockchain::Error::Application(e)) => {
					match e.downcast_ref::<WasmOverrideError>() {
						Some(WasmOverrideError::DuplicateRuntime(duplicates)) => {
							assert_eq!(duplicates.len(), 1);
						},
						_ => panic!("Test should end with Msg Error Variant"),
					}
				},
				_ => panic!("Test should end in error"),
			}
		});
	}

	#[test]
	fn should_ignore_non_wasm() {
		wasm_test(|dir, wasm_bytes, exec| {
			File::create(dir.join("README.md")).expect("Create test file");
			File::create(dir.join("LICENSE")).expect("Create a test file");
			fs::write(dir.join("test0.wasm"), wasm_bytes).expect("Create test file");
			let scraped =
				WasmOverride::scrape_overrides(dir, exec).expect("HashMap of u32 and WasmBlob");
			assert_eq!(scraped.len(), 1);
		});
	}
}
