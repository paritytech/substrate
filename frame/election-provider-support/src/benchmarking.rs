// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Election provider support pallet benchmarking.
//! This is separated into its own crate to avoid bloating the size of the runtime.

#![cfg(feature = "runtime-benchmarks")]
#![cfg_attr(not(feature = "std"), no_std)]

use crate::{ApprovalVoting, NposSolver, PhragMMS, SequentialPhragmen};
use codec::Decode;
use frame_benchmarking::v1::{benchmarks, Vec};

pub struct Pallet<T: Config>(frame_system::Pallet<T>);
pub trait Config: frame_system::Config {}

const MAX_CANDIDATES: u32 = 1000;
const MAX_VOTERS: u32 = 10 * 1000;
const MAX_VOTES_PER_VOTER: u32 = 16;
const DESIRED_MEMBERS: u32 = 16;

const SEED: u32 = 999;
fn set_up_voters_targets<AccountId: Decode + Clone>(
	voters_len: u32,
	targets_len: u32,
	degree: usize,
) -> (Vec<(AccountId, u64, impl IntoIterator<Item = AccountId>)>, Vec<AccountId>) {
	// fill targets.
	let mut targets = (0..targets_len)
		.map(|i| frame_benchmarking::account::<AccountId>("Target", i, SEED))
		.collect::<Vec<_>>();
	assert!(targets.len() > degree, "we should always have enough voters to fill");
	targets.truncate(degree);

	// fill voters.
	let voters = (0..voters_len)
		.map(|i| {
			let voter = frame_benchmarking::account::<AccountId>("Voter", i, SEED);
			// each voters votes in `degree` candidates.
			(voter, 1_000, targets.clone())
		})
		.collect::<Vec<_>>();

	(voters, targets)
}

benchmarks! {
	phragmen {
		// number of votes in snapshot.
		let v in 1 .. MAX_VOTERS;
		// number of targets in snapshot. the minimum number of targets must be larger than
		// `MAX_VOTES_PER_VOTER`.
		let t in (MAX_VOTES_PER_VOTER + 1) .. MAX_CANDIDATES;
		// number of votes per voter (ie the degree).
		let d in (MAX_VOTERS) .. MAX_VOTERS * MAX_VOTES_PER_VOTER;

		// we want to set the a voting degree per voter between the number of targets and the
		// maximum votes allowed per voter. with the current benchmarking framework, `t` cannot be
		// used as a parameter. thus, we try to use `d` as the voting degree, capped by the maximum
		// number of votes per voter.
		let votes_per_voter = d.min(MAX_VOTES_PER_VOTER);

		let (voters, targets) = set_up_voters_targets::<T::AccountId>(v, t, votes_per_voter as usize);
	}: {
		assert!(
			// why d as `num_to_elect`?
			SequentialPhragmen::<T::AccountId, sp_runtime::Perbill>
				::solve(DESIRED_MEMBERS as usize, targets, voters).is_ok()
		);
	}

	phragmms {
		// number of votes in snapshot.
		let v in 1 .. MAX_VOTERS;
		// number of targets in snapshot. the minimum number of targets must be larger than
		// `MAX_VOTES_PER_VOTER`.
		let t in (MAX_VOTES_PER_VOTER + 1) .. MAX_CANDIDATES;
		// number of votes per voter (ie the degree).
		let d in (MAX_VOTERS) .. MAX_VOTERS * MAX_VOTES_PER_VOTER;

		// we want to set the a voting degree per voter between the number of targets and the
		// maximum votes allowed per voter. with the current benchmarking framework, `t` cannot be
		// used as a parameter. thus, we try to use `d` as the voting degree, capped by the maximum
		// number of votes per voter.
		let votes_per_voter = d.min(MAX_VOTES_PER_VOTER);

		let (voters, targets) = set_up_voters_targets::<T::AccountId>(v, t, votes_per_voter as usize);
	}: {
		assert!(
			PhragMMS::<T::AccountId, sp_runtime::Perbill>
				::solve(DESIRED_MEMBERS as usize, targets, voters).is_ok()
		);
	}

	approval_voting {
		// number of votes in snapshot.
		let v in 1 .. MAX_VOTERS;
		// number of targets in snapshot. the minimum number of targets must be larger than
		// `MAX_VOTES_PER_VOTER`.
		let t in (MAX_VOTES_PER_VOTER + 1) .. MAX_CANDIDATES;
		// number of votes per voter (ie the degree).
		let d in (MAX_VOTERS) .. MAX_VOTERS * MAX_VOTES_PER_VOTER;

		// we want to set the a voting degree per voter between the number of targets and the
		// maximum votes allowed per voter. with the current benchmarking framework, `t` cannot be
		// used as a parameter. thus, we try to use `d` as the voting degree, capped by the maximum
		// number of votes per voter.
		let votes_per_voter = d.min(MAX_VOTES_PER_VOTER);

		let (voters, targets) = set_up_voters_targets::<T::AccountId>(v, t, votes_per_voter as usize);
	}: {
		assert!(
			ApprovalVoting::<T::AccountId, sp_runtime::Perbill>
				::solve(DESIRED_MEMBERS as usize, targets, voters).is_ok()
		);
	}
}
