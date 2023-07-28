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

use std::io::Write;

/// Get the latest migration version.
///
/// Find the highest version number from the available migration files.
/// Each migration file should follow the naming convention `vXX.rs`, where `XX` is the version
/// number.
fn get_latest_version() -> u16 {
	std::fs::read_dir("src/migration")
		.expect("Folder `src/migration` not found.")
		.filter_map(|entry| {
			let file_name = entry.ok()?.file_name();
			let file_name = file_name.to_str()?;
			if file_name.starts_with('v') && file_name.ends_with(".rs") {
				let version = &file_name[1..&file_name.len() - 3];
				let version = version.parse::<u16>().ok()?;
				return Some(version)
			}
			None
		})
		.max()
		.expect("Failed to find any files matching the 'src/migration/vxx.rs' pattern.")
}

/// Generates a module that exposes the latest migration version.
fn main() {
	let out_dir = std::env::var("OUT_DIR").unwrap();
	let path = std::path::Path::new(&out_dir).join("generated_version.rs");
	let mut f = std::fs::File::create(&path).unwrap();

	write!(
		f,
		"pub mod generated_version {{ pub const LATEST_MIGRATION_VERSION: u16 = {}; }}",
		get_latest_version()
	)
	.unwrap();
}
