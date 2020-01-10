// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Crate with utility functions for `build.rs` scripts.

use std::{env, path::PathBuf};

/// Make sure the calling `build.rs` script is rerun when `.git/HEAD` changed.
///
/// The file is searched from the `CARGO_MANIFEST_DIR` upwards. If the file can not be found,
/// a warning is generated.
pub fn rerun_if_git_head_changed() {
	let mut manifest_dir = PathBuf::from(
		env::var("CARGO_MANIFEST_DIR").expect("`CARGO_MANIFEST_DIR` is always set by cargo.")
	);
	let manifest_dir_copy = manifest_dir.clone();

	while manifest_dir.parent().is_some() {
		if manifest_dir.join(".git/HEAD").exists() {
			println!("cargo:rerun-if-changed={}", manifest_dir.join(".git/HEAD").display());
			return
		}

		manifest_dir.pop();
	}

	println!(
		"cargo:warning=Could not find `.git/HEAD` searching from `{}` upwards!",
		manifest_dir_copy.display(),
	);
}
