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

//! Democracy pallet benchmarking.

use super::*;

use frame_benchmarking::{account, benchmarks, whitelist_account};
use frame_support::{
	assert_noop, assert_ok,
	codec::Decode,
	traits::{
		schedule::DispatchTime, Currency, EnsureOrigin, Get, OnInitialize, UnfilteredDispatchable,
	},
};
use frame_system::{Pallet as System, RawOrigin};
use sp_runtime::traits::{BadOrigin, Bounded, One};

use crate::Pallet as Democracy;

const SEED: u32 = 0;

fn assert_last_event<T: Config>(generic_event: <T as Config>::Event) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

fn funded_account<T: Config>(name: &'static str, index: u32) -> T::AccountId {
	let caller: T::AccountId = account(name, index, SEED);
	T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	caller
}
/*
fn add_proposal<T: Config>(track: TrackIfOf<T>, n: u32) -> Result<T::Hash, &'static str> {
	let other = funded_account::<T>("proposer", n);
	let value = T::SubmissionDeposit::get();
	let proposal_hash: T::Hash = T::Hashing::hash_of(&n);

	Referenda::<T>::submit(RawOrigin::Signed(other).into(), proposal_hash, AtOrAfter::After(0))?;

	Ok(proposal_hash)
}

fn add_referendum<T: Config>(n: u32) -> Result<ReferendumIndex, &'static str> {
	let proposal_hash: T::Hash = T::Hashing::hash_of(&n);
	let vote_threshold = VoteThreshold::SimpleMajority;

	Democracy::<T>::inject_referendum(
		T::LaunchPeriod::get(),
		proposal_hash,
		vote_threshold,
		0u32.into(),
	);
	let referendum_index: ReferendumIndex = ReferendumCount::<T>::get() - 1;
	T::Scheduler::schedule_named(
		(DEMOCRACY_ID, referendum_index).encode(),
		DispatchTime::At(2u32.into()),
		None,
		63,
		frame_system::RawOrigin::Root.into(),
		Call::enact_proposal { proposal_hash, index: referendum_index }.into(),
	)
	.map_err(|_| "failed to schedule named")?;
	Ok(referendum_index)
}

fn account_vote<T: Config>(b: BalanceOf<T>) -> AccountVote<BalanceOf<T>> {
	let v = Vote { aye: true, conviction: Conviction::Locked1x };

	AccountVote::Standard { vote: v, balance: b }
}
*/
benchmarks! {
	submit {
		let p = T::MaxProposals::get();

		for i in 0 .. (p - 1) {
			add_proposal::<T>(i)?;
		}

		let caller = funded_account::<T>("caller", 0);
		let proposal_hash: T::Hash = T::Hashing::hash_of(&0);
		let value = T::MinimumDeposit::get();
		whitelist_account!(caller);
	}: _(RawOrigin::Signed(caller), proposal_hash, value.into())
	verify {
		assert_eq!(Democracy::<T>::public_props().len(), p as usize, "Proposals not created.");
	}

	impl_benchmark_test_suite!(
		Democracy,
		crate::tests::new_test_ext(),
		crate::tests::Test
	);
}
