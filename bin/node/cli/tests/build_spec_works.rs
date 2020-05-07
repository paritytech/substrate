// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
