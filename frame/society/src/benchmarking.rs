// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! Society pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_benchmarking::{account, benchmarks_instance_pallet, whitelisted_caller};
use frame_system::RawOrigin;

use sp_runtime::traits::Bounded;

use crate::Pallet as Society;

// Set up Society
fn setup_society<T: Config<I>, I: 'static>(founder: T::AccountId) -> Result<(), &'static str> {
	let candidate_deposit = T::Currency::minimum_balance();
	let origin = T::FounderSetOrigin::successful_origin();
	let max_members = 5u32;
	let max_intake = 3u32;
	let max_strikes = 3u32;
	Society::<T, I>::found_society(
		origin,
		founder,
		max_members,
		max_intake,
		max_strikes,
		candidate_deposit,
		b"benchmarking-society".to_vec(),
	)?;
	Ok(())
}

fn add_candidate<T: Config<I>, I: 'static>(
	name: &'static str,
	tally: Tally,
	skeptic_struck: bool,
) -> T::AccountId {
	let candidate: T::AccountId = account(name, 0, 0);
	T::Currency::make_free_balance_be(&candidate, BalanceOf::<T, I>::max_value());
	let deposit: BalanceOf<T, I> = T::Currency::minimum_balance();

	let candidacy = Candidacy {
		round: RoundCount::<T, I>::get(),
		kind: BidKind::Deposit(deposit),
		bid: 0u32.into(),
		tally,
		skeptic_struck,
	};
	Candidates::<T, I>::insert(&candidate, &candidacy);
	candidate
}

fn increment_round<T: Config<I>, I: 'static>() {
	let mut round_count = RoundCount::<T, I>::get();
	round_count.saturating_inc();
	RoundCount::<T, I>::put(round_count);
}

benchmarks_instance_pallet! {

	bid {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder)?;

		let caller: T::AccountId = whitelisted_caller();
		let deposit: BalanceOf<T, I> = T::Currency::minimum_balance();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T, I>::max_value());
	}: _(RawOrigin::Signed(caller.clone()), 10u32.into())
	verify {
		let first_bid: Bid<T::AccountId, BalanceOf<T, I>> = Bid {
			who: caller.clone(),
			kind: BidKind::Deposit(deposit),
			value: 10u32.into(),
		};
		assert_eq!(Bids::<T, I>::get(), vec![first_bid]);
	}

	unbid {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder)?;

		let caller: T::AccountId = whitelisted_caller();
		let deposit: BalanceOf<T, I> = T::Currency::minimum_balance();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T, I>::max_value());

		let mut bids = Bids::<T, I>::get();
		Society::<T, I>::insert_bid(&mut bids, &caller, 10u32.into(), BidKind::Deposit(deposit));
		Bids::<T, I>::put(bids);
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		assert_eq!(Bids::<T, I>::get(), vec![]);
	}

	vouch {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder)?;

		let caller: T::AccountId = whitelisted_caller();
		let vouched: T::AccountId = account("vouched", 0, 0);
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T, I>::max_value());

		let _ = Society::<T, I>::insert_member(&caller, 1u32.into());
	}: _(RawOrigin::Signed(caller.clone()), vouched.clone(), 0u32.into(), 0u32.into())
	verify {
		let bids = Bids::<T, I>::get();
		let vouched_bid: Bid<T::AccountId, BalanceOf<T, I>> = Bid {
			who: vouched.clone(),
			kind: BidKind::Vouch(caller.clone(), 0u32.into()),
			value: 0u32.into(),
		};
		assert_eq!(bids, vec![vouched_bid]);
	}

	unvouch {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder)?;

		let caller: T::AccountId = whitelisted_caller();
		let vouched: T::AccountId = account("vouched", 0, 0);
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T, I>::max_value());

		let mut bids = Bids::<T, I>::get();
		Society::<T, I>::insert_bid(&mut bids, &caller, 10u32.into(), BidKind::Vouch(caller.clone(), 0u32.into()));
		Bids::<T, I>::put(bids);
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		assert_eq!(Bids::<T, I>::get(), vec![]);
	}

	vote {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder)?;

		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T, I>::max_value());
		let _ = Society::<T, I>::insert_member(&caller, 1u32.into());

		let candidate = add_candidate::<T, I>("candidate", Default::default(), false);
		let candidate_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(candidate.clone());
	}: _(RawOrigin::Signed(caller.clone()), candidate_lookup, true)
	verify {
		let maybe_vote: Vote = <Votes<T, I>>::get(candidate.clone(), caller).unwrap();
		assert_eq!(maybe_vote.approve, true);
	}

	defender_vote {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder)?;

		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T, I>::max_value());
		let _ = Society::<T, I>::insert_member(&caller, 1u32.into());

		let defender: T::AccountId = account("defender", 0, 0);
		Defending::<T, I>::put((defender, caller.clone(), Tally::default()));
	}: _(RawOrigin::Signed(caller.clone()), false)
	verify {
		let round = RoundCount::<T, I>::get();
		let skeptic_vote: Vote = DefenderVotes::<T, I>::get(round, &caller).unwrap();
		assert_eq!(skeptic_vote.approve, false);
	}

	payout {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder)?;

		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, T::Currency::minimum_balance() * 10u32.into());
		let _ = Society::<T, I>::insert_member(&caller, 0u32.into());

		T::Currency::make_free_balance_be(&Society::<T, I>::payouts(), BalanceOf::<T, I>::max_value());

		let mut pot = <Pot<T, I>>::get();
		pot = pot.saturating_add(BalanceOf::<T, I>::max_value());
		Pot::<T, I>::put(&pot);

		Society::<T, I>::bump_payout(&caller, 0u32.into(), 1u32.into());
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		let record = Payouts::<T, I>::get(caller);
		assert!(record.payouts.is_empty());
	}

	waive_repay {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder)?;

		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T, I>::max_value());
		let _ = Society::<T, I>::insert_member(&caller, 0u32.into());

		T::Currency::make_free_balance_be(&Society::<T, I>::payouts(), BalanceOf::<T, I>::max_value());

		Society::<T, I>::bump_payout(&caller, 0u32.into(), 1u32.into());
	}: _(RawOrigin::Signed(caller.clone()), 1u32.into())
	verify {
		let record = Payouts::<T, I>::get(caller);
		assert!(record.payouts.is_empty());
	}

	found_society {
		let founder: T::AccountId = whitelisted_caller();
		let can_found = T::FounderSetOrigin::successful_origin();
		let candidate_deposit: BalanceOf<T, I> = T::Currency::minimum_balance();
	}: _<T::Origin>(can_found, founder.clone(), 5, 3, 3, candidate_deposit, b"benchmarking-society".to_vec())
	verify {
		assert_eq!(Founder::<T, I>::get(), Some(founder.clone()));
	}

	dissolve {
		let founder: T::AccountId = whitelisted_caller();
		setup_society::<T, I>(founder.clone())?;
	}: _(RawOrigin::Signed(founder))
	verify {
		assert_eq!(Founder::<T, I>::get(), None);
	}

	judge_suspended_member {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder.clone())?;

		let caller: T::AccountId = whitelisted_caller();
		let _ = Society::<T, I>::insert_member(&caller, 0u32.into());
		let _ = Society::<T, I>::suspend_member(&caller);
	}: _(RawOrigin::Signed(founder), caller.clone(), false)
	verify {
		assert_eq!(SuspendedMembers::<T, I>::contains_key(&caller), false);
	}

	set_parameters {
		let founder: T::AccountId = whitelisted_caller();
		setup_society::<T, I>(founder.clone())?;

		let max_members = 10u32;
		let max_intake = 10u32;
		let max_strikes = 10u32;
		let candidate_deposit: BalanceOf<T, I> = 10u32.into();
		let params = GroupParams { max_members, max_intake, max_strikes, candidate_deposit };
	}: _(RawOrigin::Signed(founder), max_members, max_intake, max_strikes, candidate_deposit)
	verify {
		assert_eq!(Parameters::<T, I>::get(), Some(params));
	}

	punish_skeptic {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder)?;

		let candidate = add_candidate::<T, I>("candidate", Default::default(), false);

		let skeptic: T::AccountId = account("skeptic", 0, 0);
		let _ = Society::<T, I>::insert_member(&skeptic, 0u32.into());
		Skeptic::<T, I>::put(&skeptic);
		frame_system::Pallet::<T>::set_block_number(T::VotingPeriod::get() + 1u32.into());
	}: _(RawOrigin::Signed(candidate.clone()))
	verify {
		let candidacy = Candidates::<T, I>::get(&candidate).unwrap();
		assert_eq!(candidacy.skeptic_struck, true);
	}

	claim_membership {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder)?;

		let candidate = add_candidate::<T, I>("candidate", Tally { approvals: 3u32.into(), rejections: 0u32.into() }, false);
		increment_round::<T, I>();
	}: _(RawOrigin::Signed(candidate.clone()))
	verify {
		assert!(!Candidates::<T, I>::contains_key(&candidate));
		assert!(Members::<T, I>::contains_key(&candidate));
	}

	bestow_membership {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder.clone())?;

		let candidate = add_candidate::<T, I>("candidate", Tally { approvals: 3u32.into(), rejections: 1u32.into() }, false);
		increment_round::<T, I>();
	}: _(RawOrigin::Signed(founder), candidate.clone())
	verify {
		assert!(!Candidates::<T, I>::contains_key(&candidate));
		assert!(Members::<T, I>::contains_key(&candidate));
	}

	kick_candidate {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder.clone())?;

		let candidate = add_candidate::<T, I>("candidate", Tally { approvals: 1u32.into(), rejections: 1u32.into() }, false);
		increment_round::<T, I>();
	}: _(RawOrigin::Signed(founder), candidate.clone())
	verify {
		assert!(!Candidates::<T, I>::contains_key(&candidate));
	}

	resign_candidacy {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder)?;

		let candidate = add_candidate::<T, I>("candidate", Tally { approvals: 0u32.into(), rejections: 0u32.into() }, false);
	}: _(RawOrigin::Signed(candidate.clone()))
	verify {
		assert!(!Candidates::<T, I>::contains_key(&candidate));
	}

	drop_candidate {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder)?;

		let candidate = add_candidate::<T, I>("candidate", Tally { approvals: 0u32.into(), rejections: 3u32.into() }, false);

		let caller: T::AccountId = whitelisted_caller();
		let _ = Society::<T, I>::insert_member(&caller, 0u32.into());

		let mut round_count = RoundCount::<T, I>::get();
		round_count = round_count.saturating_add(2u32);
		RoundCount::<T, I>::put(round_count);
	}: _(RawOrigin::Signed(caller), candidate.clone())
	verify {
		assert!(!Candidates::<T, I>::contains_key(&candidate));
	}

	cleanup_candidacy {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder)?;

		let candidate = add_candidate::<T, I>("candidate", Tally { approvals: 0u32.into(), rejections: 0u32.into() }, false);

		let member_one: T::AccountId = account("one", 0, 0);
		let member_two: T::AccountId = account("two", 0, 0);
		let _ = Society::<T, I>::insert_member(&member_one, 0u32.into());
		let _ = Society::<T, I>::insert_member(&member_two, 0u32.into());

		let candidate_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(candidate.clone());
		let _ = Society::<T, I>::vote(RawOrigin::Signed(member_one.clone()).into(), candidate_lookup.clone(), true);
		let _ = Society::<T, I>::vote(RawOrigin::Signed(member_two.clone()).into(), candidate_lookup, true);
		Candidates::<T, I>::remove(&candidate);
	}: _(RawOrigin::Signed(member_one), candidate.clone(), 5)
	verify {
		assert_eq!(Votes::<T, I>::get(&candidate, &member_two), None);
	}

	cleanup_challenge {
		let founder: T::AccountId = account("founder", 0, 0);
		setup_society::<T, I>(founder)?;

		ChallengeRoundCount::<T, I>::put(1u32);

		let member: T::AccountId = whitelisted_caller();
		let _ = Society::<T, I>::insert_member(&member, 0u32.into());
		let defender: T::AccountId = account("defender", 0, 0);
		Defending::<T, I>::put((defender.clone(), member.clone(), Tally::default()));
		let _ = Society::<T, I>::defender_vote(RawOrigin::Signed(member.clone()).into(), true);

		ChallengeRoundCount::<T, I>::put(2u32);
		let mut challenge_round = ChallengeRoundCount::<T, I>::get();
		challenge_round = challenge_round.saturating_sub(1u32);
	}: _(RawOrigin::Signed(member.clone()), challenge_round, 1u32)
	verify {
		assert_eq!(DefenderVotes::<T, I>::get(challenge_round, &defender), None);
	}

	impl_benchmark_test_suite!(
		Society,
		crate::tests_composite::ExtBuilder::default().build(),
		crate::tests_composite::Test,
	)
}
