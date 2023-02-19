// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
use regex::Regex;
use std::process::Command;

fn expected_regex() -> Regex {
	Regex::new(r"^substrate (.+)-([a-f\d]+)$").unwrap()
}

#[test]
fn version_is_full() {
	let expected = expected_regex();
	let output = Command::new(cargo_bin("substrate")).args(&["--version"]).output().unwrap();

	assert!(output.status.success(), "command returned with non-success exit code");

	let output = String::from_utf8_lossy(&output.stdout).trim().to_owned();
	let captures = expected.captures(output.as_str()).expect("could not parse version in output");

	assert_eq!(&captures[1], env!("CARGO_PKG_VERSION"));
}

#[test]
fn test_regex_matches_properly() {
	let expected = expected_regex();

	let captures = expected.captures("substrate 2.0.0-da487d19d").unwrap();
	assert_eq!(&captures[1], "2.0.0");
	assert_eq!(&captures[2], "da487d19d");

	let captures = expected.captures("substrate 2.0.0-alpha.5-da487d19d").unwrap();
	assert_eq!(&captures[1], "2.0.0-alpha.5");
	assert_eq!(&captures[2], "da487d19d");
}
