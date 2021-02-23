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

//! Fuzzing which ensures that running unbalanced sequential phragmen always produces a result
//! which satisfies our PJR checker.
//!
//! ## Running a single iteration
//!
//! Honggfuzz shuts down each individual loop iteration after a configurable time limit.
//! It can be helpful to run a single iteration on your hardware to help benchmark how long that time
//! limit should reasonably be. Simply run the program without the `fuzzing` configuration to run a
//! single iteration: `cargo run --bin phragmen_pjr`.
//!
//! On a relatively modern machine (late 2019 era), a single iteration takes ~30 seconds with maximum
//! parameters.
//!
//! ## Running
//!
//! Run with `HFUZZ_RUN_ARGS="-t 60" cargo hfuzz run phragmen_pjr`.
//!
//! Note the environment variable: by default, `cargo hfuzz` shuts down each iteration after 1 second
//! of runtime. We significantly increase that to ensure that the fuzzing gets a chance to complete.
//!
//! ## Debugging a panic
//!
//! Once a panic is found, it can be debugged with
//! `HFUZZ_RUN_ARGS="-t 60" cargo hfuzz run-debug phragmen_pjr hfuzz_workspace/phragmen_pjr/*.fuzz`.
//!

#[cfg(fuzzing)]
use honggfuzz::fuzz;

#[cfg(not(fuzzing))]
use structopt::StructOpt;

mod common;
use common::{generate_random_npos_inputs, to_range};
use rand::{self, SeedableRng};
use sp_npos_elections::{
	assignment_ratio_to_staked, pjr_check, seq_phragmen, to_supports, to_without_backing,
	ElectionResult, Supports,
};

type AccountId = u64;
type PerThing = sp_arithmetic::PerU16;

const MIN_CANDIDATES: usize = 100;
const MAX_CANDIDATES: usize = 1000;
const MIN_VOTERS: usize = 100;
const MAX_VOTERS: usize = 2000;

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
		opt.candidates.unwrap_or(MAX_CANDIDATES-1),
		opt.voters.unwrap_or(MAX_VOTERS-1),
		opt.seed.unwrap_or_default(),
	);
}

fn iteration(mut candidate_count: usize, mut voter_count: usize, seed: u64) {
	let rng = rand::rngs::SmallRng::seed_from_u64(seed);
	candidate_count = to_range(candidate_count, MIN_CANDIDATES, MAX_CANDIDATES);
	voter_count = to_range(voter_count, MIN_VOTERS, MAX_VOTERS);

	let (rounds, candidates, voters) =
		generate_random_npos_inputs(candidate_count, voter_count, rng);

	// Run seq-phragmen
	let ElectionResult {
		winners,
		assignments,
	} = seq_phragmen::<AccountId, PerThing>(rounds, candidates.clone(), voters.clone(), None)
		.expect("seq_phragmen must succeed");

	// pjr_check only cares about the identity of the winner, not its balance
	let winners = to_without_backing(winners);

	// convert assignments into staked assignments
	let assignments = assignment_ratio_to_staked(assignments, |who| {
		let voter_idx = voters
			.binary_search_by_key(who, |(id, _weight, _assignments)| *id)
			.expect("voter must be present in voters list");
		voters[voter_idx].1
	});

	let supports: Supports<AccountId> = to_supports(&winners, &assignments)
		.expect("election result must be structurally valid");

	assert!(
		pjr_check(&supports, candidates, voters),
		"unbalanced sequential phragmen must satisfy PJR",
	);
}
