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

//! Contains [`MachineCmd`] as entry point for the node
//! and the core benchmarking logic.

use sc_cli::{CliConfiguration, Result, SharedParams};
use sp_core::{blake2_256, sr25519, Pair};
use sp_io::crypto::sr25519_verify;
use sp_std::prelude::*;

use clap::Parser;
use log::info;
use prettytable::{cell, row, table, Table};
use rand::RngCore;
use std::{
	fmt::Debug,
	time::{Duration, Instant},
};
use thousands::Separable;

use crate::shared::new_rng;

/// Command to benchmark the hardware.
///
/// The implementation of this command is currently a place holder until
/// <https://github.com/paritytech/substrate/pull/11062> is merged.
///
/// The output or `benchmark machine --dev` looks like this:
/// ```text
/// +----------------+------------------+------------+----------+------------+
/// | Function       | Input len [byte] | Iterations | Time [s] | Per second |
/// +----------------+------------------+------------+----------+------------+
/// | BLAKE2-256     | 32               | 10,000,000 | 2.061    | 4,851,958  |
/// +----------------+------------------+------------+----------+------------+
/// | SR25519 verify | 32               | 20,000     | 1.489    | 13,429     |
/// +----------------+------------------+------------+----------+------------+
/// ```
#[derive(Debug, Parser)]
pub struct MachineCmd {
	#[allow(missing_docs)]
	#[clap(flatten)]
	pub shared_params: SharedParams,

	/// Iterations of the hash function.
	#[clap(long, default_value = "10000000")]
	pub hash_reps: u64,

	/// Iterations of the verification function.
	#[clap(long, default_value = "20000")]
	pub verify_reps: u64,
}

impl MachineCmd {
	/// Execute the benchmark and log the results.
	pub fn run(&self) -> Result<()> {
		// Use a table for nicer console output.
		let mut table =
			table!(["Function", "Input len [byte]", "Iterations", "Time [s]", "Per second"]);

		let input_len = 32_usize;
		// Benchmark the BLAKE2-256 hashing speed.
		let name = "BLAKE2-256";
		let duration = Self::blake2_speed(self.hash_reps, input_len);
		Self::put_col(&mut table, name, self.hash_reps, input_len, duration);

		// Benchmark the speed of SR2519 verification.
		let name = "SR25519 verify";
		let duration = Self::sr_verify_speed(self.verify_reps, input_len);
		Self::put_col(&mut table, name, self.verify_reps, input_len, duration);

		info!("\n{}", table);
		Ok(())
	}

	/// Recursively hashes a value `reps` many times.
	fn blake2_speed(reps: u64, input_len: usize) -> Duration {
		let mut data = vec![0u8; input_len];

		let start = Instant::now();
		for _ in 0..reps {
			data = blake2_256(&data).into();
		}
		start.elapsed()
	}

	/// Verify the signature of different random data `reps` many times.
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

	/// Format the data and put it as column into the table.
	fn put_col(table: &mut Table, name: &str, reps: u64, size: usize, d: Duration) {
		let d = d.as_secs_f32();
		let s = (reps as f32 / d) as u64;
		table.add_row(row![
			name,
			size,
			reps.separate_with_commas(),
			format!("{:.3}", d),
			s.separate_with_commas()
		]);
	}
}

// Boilerplate
impl CliConfiguration for MachineCmd {
	fn shared_params(&self) -> &SharedParams {
		&self.shared_params
	}
}
