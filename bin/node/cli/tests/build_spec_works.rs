// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use assert_cmd::cargo::cargo_bin;
use std::process::Command;
use tempfile::tempdir;

#[test]
fn build_spec_works() {
	let base_path = tempdir().expect("could not create a temp dir");

	let output = Command::new(cargo_bin("substrate"))
		.args(&["build-spec", "--dev", "-d"])
		.arg(base_path.path())
		.output()
		.unwrap();
	assert!(output.status.success());

	// Make sure that the `dev` chain folder exists, but the `db` doesn't
	assert!(base_path.path().join("chains/dev/").exists());
	assert!(!base_path.path().join("chains/dev/db").exists());

	let _value: serde_json::Value = serde_json::from_slice(output.stdout.as_slice()).unwrap();
}
