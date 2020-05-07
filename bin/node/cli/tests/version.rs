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
use platforms::*;
use regex::Regex;
use std::process::Command;

fn expected_regex() -> Regex {
	Regex::new(r"^substrate (\d+\.\d+\.\d+(?:-.+?)?)-([a-f\d]+|unknown-commit)-(.+?)-(.+?)(?:-(.+))?$").unwrap()
}

#[test]
fn version_is_full() {
	let expected = expected_regex();
	let output = Command::new(cargo_bin("substrate"))
		.args(&["--version"])
		.output()
		.unwrap();

	assert!(
		output.status.success(),
		"command returned with non-success exit code"
	);

	let output = String::from_utf8_lossy(&output.stdout).trim().to_owned();
	let captures = expected
		.captures(output.as_str())
		.expect("could not parse version in output");

	assert_eq!(&captures[1], env!("CARGO_PKG_VERSION"));
	assert_eq!(&captures[3], TARGET_ARCH.as_str());
	assert_eq!(&captures[4], TARGET_OS.as_str());
	assert_eq!(
		captures.get(5).map(|x| x.as_str()),
		TARGET_ENV.map(|x| x.as_str())
	);
}

#[test]
fn test_regex_matches_properly() {
	let expected = expected_regex();

	let captures = expected
		.captures("substrate 2.0.0-da487d19d-x86_64-linux-gnu")
		.unwrap();
	assert_eq!(&captures[1], "2.0.0");
	assert_eq!(&captures[2], "da487d19d");
	assert_eq!(&captures[3], "x86_64");
	assert_eq!(&captures[4], "linux");
	assert_eq!(captures.get(5).map(|x| x.as_str()), Some("gnu"));

	let captures = expected
		.captures("substrate 2.0.0-alpha.5-da487d19d-x86_64-linux-gnu")
		.unwrap();
	assert_eq!(&captures[1], "2.0.0-alpha.5");
	assert_eq!(&captures[2], "da487d19d");
	assert_eq!(&captures[3], "x86_64");
	assert_eq!(&captures[4], "linux");
	assert_eq!(captures.get(5).map(|x| x.as_str()), Some("gnu"));

	let captures = expected
		.captures("substrate 2.0.0-alpha.5-da487d19d-x86_64-linux")
		.unwrap();
	assert_eq!(&captures[1], "2.0.0-alpha.5");
	assert_eq!(&captures[2], "da487d19d");
	assert_eq!(&captures[3], "x86_64");
	assert_eq!(&captures[4], "linux");
	assert_eq!(captures.get(5).map(|x| x.as_str()), None);
}
