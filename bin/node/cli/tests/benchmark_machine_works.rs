// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

/// Tests that the `benchmark machine` command works for the substrate dev runtime.
#[test]
fn benchmark_machine_works() {
	let status = Command::new(cargo_bin("substrate"))
		.args(["benchmark", "machine", "--dev"])
		.args(["--verify-duration", "0.1"])
		// Disable the check to make it succeed.
		.args(["--no-check"])
		.status()
		.unwrap();

	assert!(status.success());
}

/// Test that the command fails when run with the test profile.
#[test]
fn benchmark_machine_fails_with_bad_build_profile() {
	let output = Command::new(cargo_bin("substrate"))
		.args(["benchmark", "machine", "--dev"])
		.args(["--verify-duration", "0.1"])
		// Set the tolerance to 100% so that the hardware check passes.
		.args(["--tolerance", "100.0"])
		.output()
		.unwrap();

	// Command should have failed.
	assert!(!output.status.success());
	// A `BadBuildProfile` error should have been printed.
	let log = String::from_utf8_lossy(&output.stderr).to_string();
	assert!(log.contains("BadBuildProfile"));
}

/// Test that the hardware fails the check.
///
/// This is most likely the case since it using a test profile.
#[test]
fn benchmark_machine_fails_with_slow_hardware() {
	let output = Command::new(cargo_bin("substrate"))
		.args(["benchmark", "machine", "--dev"])
		.args(["--verify-duration", "0.1", "--tolerance", "0"])
		.output()
		.unwrap();

	// Command should have failed.
	assert!(!output.status.success());
	// A `UnmetRequirement` error should have been printed.
	let log = String::from_utf8_lossy(&output.stderr).to_string();
	assert!(log.contains("UnmetRequirement"));
}
