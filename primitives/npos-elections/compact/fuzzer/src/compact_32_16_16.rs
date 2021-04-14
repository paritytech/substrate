// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Fuzzing which ensures that the generated implementation of `encoded_size_for` always accurately
//! predicts the correct encoded size.
//!
//! ## Running a single iteration
//!
//! Simply run the program without the `fuzzing` configuration to run a single iteration:
//! `cargo run --bin compact_16`.
//!
//! ## Running
//!
//! Run with `cargo hfuzz run compact_16`.
//!
//! ## Debugging a panic
//!
//! Once a panic is found, it can be debugged with
//! `cargo hfuzz run-debug compact_16 hfuzz_workspace/compact_16/*.fuzz`.

use _npos::CompactSolution;
use codec::Encode;
#[cfg(fuzzing)]
use honggfuzz::fuzz;

#[cfg(not(fuzzing))]
use structopt::StructOpt;

mod common;

use common::{Accuracy, generate_random_votes, make_target_fn, make_voter_fn, to_range};
use rand::{self, SeedableRng};

sp_npos_elections::generate_solution_type!(
	#[compact]
	pub struct Compact::<VoterIndex = u32, TargetIndex = u16, Accuracy = Accuracy>(16)
);

const MIN_CANDIDATES: usize = 250;
const MAX_CANDIDATES: usize = 1000;
const MIN_VOTERS: usize = 500;
const MAX_VOTERS: usize = 2500;

#[cfg(fuzzing)]
fn main() {
	loop {
		fuzz!(|data: (usize, usize, u64)| {
			let (candidate_count, voter_count, seed) = data;
			iteration(candidate_count, voter_count, seed);
		});
	}
}

#[cfg(not(fuzzing))]
#[derive(Debug, StructOpt)]
struct Opt {
	/// How many candidates participate in this election
	#[structopt(short, long)]
	candidates: Option<usize>,

	/// How many voters participate in this election
	#[structopt(short, long)]
	voters: Option<usize>,

	/// Random seed to use in this election
	#[structopt(long)]
	seed: Option<u64>,
}

#[cfg(not(fuzzing))]
fn main() {
	let opt = Opt::from_args();
	// candidates and voters by default use the maxima, which turn out to be one less than
	// the constant.
	iteration(
		opt.candidates.unwrap_or(MAX_CANDIDATES - 1),
		opt.voters.unwrap_or(MAX_VOTERS - 1),
		opt.seed.unwrap_or_default(),
	);
}

fn iteration(mut candidate_count: usize, mut voter_count: usize, seed: u64) {
	let rng = rand::rngs::SmallRng::seed_from_u64(seed);
	candidate_count = to_range(candidate_count, MIN_CANDIDATES, MAX_CANDIDATES);
	voter_count = to_range(voter_count, MIN_VOTERS, MAX_VOTERS);

	let (voters, assignments, candidates) =
		generate_random_votes(candidate_count, voter_count, rng);

	let predicted_size = Compact::encoded_size_for(&assignments);

	let compact =
		Compact::from_assignment(assignments, make_voter_fn(&voters), make_target_fn(&candidates))
			.unwrap();
	let encoding = compact.encode();

	assert_eq!(predicted_size, encoding.len());
}
