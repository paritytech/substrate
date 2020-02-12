// Copyright 2020 Parity Technologies (UK) Ltd.
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

#![cfg(unix)]

use assert_cmd::cargo::cargo_bin;
use std::{process::{Command, Stdio}, fs, path::PathBuf};

mod common;

#[test]
fn factory_works() {
	let base_path = "factory_test";

	let _ = fs::remove_dir_all(base_path);
	let status = Command::new(cargo_bin("substrate"))
		.stdout(Stdio::null())
		.args(&["factory", "--dev", "-d", base_path])
		.status()
		.unwrap();
	assert!(status.success());

	// Make sure that the `dev` chain folder exists & `db`
	assert!(PathBuf::from(base_path).join("chains/dev/").exists());
	assert!(PathBuf::from(base_path).join("chains/dev/db").exists());
}
