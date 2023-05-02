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

use crate::{ApprovalVoting, NposSolver, PhragMMS, SequentialPhragmen};
use codec::Decode;
use frame_benchmarking::v1::{benchmarks, Vec};

pub struct Pallet<T: Config>(frame_system::Pallet<T>);
pub trait Config: frame_system::Config {}

const MAX_CANDIDATES: u32 = 2000;
const MIN_VOTERS: u32 = 1000;
const MAX_VOTERS: u32 = 10 * 1000;
const MIN_VOTES_PER_VOTER: u32 = 5;
const MAX_VOTES_PER_VOTER: u32 = 16;
const DESIRED_MEMBERS: u32 = 16;

const SEED: u32 = 999;
fn set_up_voters_targets<AccountId: Decode + Clone>(
	voters_len: u32,
	targets_len: u32,
	votes_per_voter: usize,
) -> (Vec<(AccountId, u64, impl IntoIterator<Item = AccountId>)>, Vec<AccountId>) {
	// fill targets.
	let total_targets = (0..targets_len)
		.map(|i| frame_benchmarking::account::<AccountId>("Target", i, SEED))
		.collect::<Vec<_>>();
	assert!(total_targets.len() > votes_per_voter, "we should always have enough voters to fill");

	let mut targets = total_targets.clone();
	targets.truncate(votes_per_voter);

	// fill voters.
	let voters = (0..voters_len)
		.map(|i| {
			let voter = frame_benchmarking::account::<AccountId>("Voter", i, SEED);
			// each voters votes in `degree` candidates.
			(voter, 1_000, targets.clone())
		})
		.collect::<Vec<_>>();

	(voters, total_targets)
}

benchmarks! {
	phragmen {
		// number of targets in the snapshot. the minimum number of targets must be larger than
		// `MAX_VOTES_PER_VOTER`.
		let t in (MAX_VOTES_PER_VOTER + 1) .. MAX_CANDIDATES;
		// number of votes in snapshot.
		let v in (MIN_VOTERS) .. MAX_VOTERS;
		// number of edges (total votes for all voters).
		let e in (MAX_VOTERS) .. MAX_VOTERS  * MAX_VOTES_PER_VOTER;

		// when v is being iterated, e is set to max and that's a problem. thus, we calculate the
		// total edges as MAX_VOTERS .. MAX_VOTERS * MAX_VOTES_PER_VOTER and extract the votes
		// per voter, capped by MAX_VOTES_PER_VOTER.
		let votes_per_voter = (e / v).clamp(MIN_VOTES_PER_VOTER, MAX_VOTES_PER_VOTER);

		let (voters, total_targets) = set_up_voters_targets::<T::AccountId>(v, t, votes_per_voter as usize);
	}: {
		assert!(
			SequentialPhragmen::<T::AccountId, sp_runtime::Perbill>
				::solve(DESIRED_MEMBERS as usize, total_targets, voters).is_ok()
		);
	}

	phragmms {
		// number of targets in the snapshot. the minimum number of targets must be larger than
		// `MAX_VOTES_PER_VOTER`.
		let t in (MAX_VOTES_PER_VOTER + 1) .. MAX_CANDIDATES;
		// number of votes in snapshot.
		let v in (MIN_VOTERS) .. MAX_VOTERS;
		// number of edges (total votes for all voters).
		let e in (MAX_VOTERS) .. MAX_VOTERS  * MAX_VOTES_PER_VOTER;

		// when v is being iterated, e is set to max and that's a problem. thus, we calculate the
		// total edges as MAX_VOTERS .. MAX_VOTERS * MAX_VOTES_PER_VOTER and extract the votes
		// per voter, capped by MAX_VOTES_PER_VOTER.
		let votes_per_voter = (e / v).clamp(MIN_VOTES_PER_VOTER, MAX_VOTES_PER_VOTER);

		let (voters, total_targets) = set_up_voters_targets::<T::AccountId>(v, t, votes_per_voter as usize);
	}: {
		assert!(
			PhragMMS::<T::AccountId, sp_runtime::Perbill>
				::solve(DESIRED_MEMBERS as usize, total_targets, voters).is_ok()
		);
	}

	approval_voting {
		// number of targets in the snapshot. the minimum number of targets must be larger than
		// `MAX_VOTES_PER_VOTER`.
		let t in (MAX_VOTES_PER_VOTER + 1) .. MAX_CANDIDATES;
		// number of votes in snapshot.
		let v in (MIN_VOTERS) .. MAX_VOTERS;
		// number of edges (total votes for all voters).
		let e in (MAX_VOTERS) .. MAX_VOTERS  * MAX_VOTES_PER_VOTER;

		// when v is being iterated, e is set to max and that's a problem. thus, we calculate the
		// total edges as MAX_VOTERS .. MAX_VOTERS * MAX_VOTES_PER_VOTER and extract the votes
		// per voter, capped by MAX_VOTES_PER_VOTER.
		let votes_per_voter = (e / v).clamp(MIN_VOTES_PER_VOTER, MAX_VOTES_PER_VOTER);

		let (voters, total_targets) = set_up_voters_targets::<T::AccountId>(v, t, votes_per_voter as usize);
	}: {
		assert!(
			ApprovalVoting::<T::AccountId, sp_runtime::Perbill>
				::solve(DESIRED_MEMBERS as usize, total_targets, voters).is_ok()
		);
	}
}
