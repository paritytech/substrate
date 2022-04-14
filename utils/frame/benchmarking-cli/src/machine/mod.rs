// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Contains the [`MachineCmd`] as entry point for the node
//! and the core benchmarking logic.

use sc_cli::{CliConfiguration, Result, SharedParams};
use sc_service::Configuration;
use sc_sysinfo::{
	benchmark_cpu, benchmark_disk_random_writes, benchmark_disk_sequential_writes,
	benchmark_memory, benchmark_sr25519_verify, ExecutionLimit,
};

use clap::Parser;
use log::info;
use prettytable::{cell, row, table};
use std::{fmt::Debug, fs, time::Duration};

/// Command to benchmark the hardware.
///
/// Runs multiple benchmarks and prints their output to console.
/// Can be used to gauge if the hardware is fast enough to keep up with a chain's requirements.
/// This command must be integrated by the client since the client can set compiler flags
/// which influence the results.
///
/// You can use the `--base-path` flag to set a location for the disk benchmarks.
#[derive(Debug, Parser)]
pub struct MachineCmd {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	/// Time limit for the verification benchmark.
	#[clap(long, default_value = "2.0", value_name = "SECONDS")]
	pub verify_duration: f32,
}

impl MachineCmd {
	/// Execute the benchmark and print the results.
	pub fn run(&self, cfg: &Configuration) -> Result<()> {
		// Ensure that the dir exists since the node is not started to take care of it.
		let dir = cfg.database.path().ok_or("No DB directory provided")?;
		fs::create_dir_all(dir)?;

		info!("Running machine benchmarks...");
		let write = benchmark_disk_sequential_writes(dir)?;
		let read = benchmark_disk_random_writes(dir)?;
		let verify_limit =
			ExecutionLimit::MaxDuration(Duration::from_secs_f32(self.verify_duration));
		let verify = benchmark_sr25519_verify(verify_limit) * 1024.0;

		// Use a table for nicer console output.
		let table = table!(
			["Category", "Function", "Score", "Unit"],
			["CPU", "BLAKE2-256", benchmark_cpu(), "MB/s"],
			["CPU", "SR25519 Verify", format!("{:.1}", verify), "KB/s"],
			["Memory", "Copy", benchmark_memory(), "MB/s"],
			["Disk", "Seq Write", write, "MB/s"],
			["Disk", "Rnd Write", read, "MB/s"]
		);

		info!("\n{}", table);
		Ok(())
	}
}

// Boilerplate
impl CliConfiguration for MachineCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}
}
