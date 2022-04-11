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
use sc_sysinfo::gather_hwbench;
use sp_core::{sr25519, Pair};
use sp_io::crypto::sr25519_verify;
use sp_std::prelude::*;

use clap::Parser;
use log::info;
use prettytable::{cell, row, table};
use rand::RngCore;
use std::{
	fmt::Debug,
	time::{Duration, Instant},
};
use tempfile::tempdir;

use crate::shared::new_rng;

/// Command to benchmark the hardware.
///
/// Runs multiple benchmarks and prints their output to console.
/// Can be used to gauge if the hardware is fast enough to keep up with a chain's requirements.
/// This command must be integrated by the client since the client can set compiler flags
/// which influence the results.
///
/// The output or `benchmark machine --dev` looks like this:
/// ```text
/// +----------+----------------+-------+------+
/// | Category | Function       | Score | Unit |
/// +----------+----------------+-------+------+
/// | Memory   | Copy           | 19983 | MB/s |
/// +----------+----------------+-------+------+
/// | Disk     | Seq Write      | 2699  | MB/s |
/// +----------+----------------+-------+------+
/// | Disk     | Rnd Write      | 295   | MB/s |
/// +----------+----------------+-------+------+
/// | CPU      | BLAKE2-256     | 841   | MB/s |
/// +----------+----------------+-------+------+
/// | CPU      | SR25519 Verify | 21.10 | K/s  |
/// +----------+----------------+-------+------+
/// ```
#[derive(Debug, Parser)]
pub struct MachineCmd {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	/// Iterations of the verification function.
	#[clap(long, default_value = "20000")]
	pub verify_reps: u64,
}

impl MachineCmd {
	/// Execute the benchmark and print the results.
	pub fn run(&self) -> Result<()> {
		info!("Running machine benchmarks...");
		let tmp_dir = tempdir()?;
		let info = gather_hwbench(Some(tmp_dir.path()));

		// Use a table for nicer console output.
		let mut table = table!(
			["Category", "Function", "Score", "Unit"],
			["Memory", "Copy", info.memory_memcpy_score, "MB/s"],
			["Disk", "Seq Write", info.disk_sequential_write_score.unwrap_or_default(), "MB/s"],
			["Disk", "Rnd Write", info.disk_random_write_score.unwrap_or_default(), "MB/s"],
			["CPU", "BLAKE2-256", info.cpu_hashrate_score, "MB/s"]
		);

		// Additionally measure the speed of SR25519::Verify for 32 byte input.
		let input_len = 32;
		let took = Self::sr_verify_speed(self.verify_reps, input_len as usize);
		let speed = (self.verify_reps as f64 / took.as_secs_f64()) / 1000.0;
		table.add_row(row!["CPU", "SR25519 Verify", format!("{:.2}", speed), "K/s"]);

		info!("\n{}", table);
		Ok(())
	}

	/// Verify signatures of different random data `reps` many times.
	fn sr_verify_speed(reps: u64, input_len: usize) -> Duration {
		let pair = sr25519::Pair::from_string("//Alice", None).unwrap();

		let (mut rng, _) = new_rng(None);
		let mut msgs = Vec::new();
		let mut sigs = Vec::new();

		for _ in 0..reps {
			let mut msg = vec![0u8; input_len];
			rng.fill_bytes(&mut msg[..]);

			sigs.push(pair.sign(&msg));
			msgs.push(msg);
		}

		// Measure the time to verify all.
		let start = Instant::now();
		for (sig, msg) in sigs.into_iter().zip(msgs.iter()) {
			sr25519_verify(&sig, &msg[..], &pair.public());
		}

		start.elapsed()
	}
}

// Boilerplate
impl CliConfiguration for MachineCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}
}
