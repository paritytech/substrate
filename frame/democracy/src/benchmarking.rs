// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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
	traits::{Currency, EnsureOrigin, Get, OnInitialize, UnfilteredDispatchable},
};
use frame_system::RawOrigin;
use sp_core::H256;
use sp_runtime::{traits::Bounded, BoundedVec};

use crate::Pallet as Democracy;

const REFERENDUM_COUNT_HINT: u32 = 10;
const SEED: u32 = 0;

fn funded_account<T: Config>(name: &'static str, index: u32) -> T::AccountId {
	let caller: T::AccountId = account(name, index, SEED);
	// Give the account half of the maximum value of the `Balance` type.
	// Otherwise some transfers will fail with an overflow error.
	T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value() / 2u32.into());
	caller
}

fn make_proposal<T: Config>(n: u32) -> BoundedCallOf<T> {
	let call: CallOf<T> = frame_system::Call::remark { remark: n.encode() }.into();
	<T as Config>::Preimages::bound(call).unwrap()
}

fn add_proposal<T: Config>(n: u32) -> Result<H256, &'static str> {
	let other = funded_account::<T>("proposer", n);
	let value = T::MinimumDeposit::get();
	let proposal = make_proposal::<T>(n);
	Democracy::<T>::propose(RawOrigin::Signed(other).into(), proposal.clone(), value)?;
	Ok(proposal.hash())
}

fn add_referendum<T: Config>(n: u32) -> (ReferendumIndex, H256) {
	let vote_threshold = VoteThreshold::SimpleMajority;
	let proposal = make_proposal::<T>(n);
	let hash = proposal.hash();
	(
		Democracy::<T>::inject_referendum(
			T::LaunchPeriod::get(),
			proposal,
			vote_threshold,
			0u32.into(),
		),
		hash,
	)
}

fn account_vote<T: Config>(b: BalanceOf<T>) -> AccountVote<BalanceOf<T>> {
	let v = Vote { aye: true, conviction: Conviction::Locked1x };

	AccountVote::Standard { vote: v, balance: b }
}

benchmarks! {
	propose {
		let p = T::MaxProposals::get();

		for i in 0 .. (p - 1) {
			add_proposal::<T>(i)?;
		}

		let caller = funded_account::<T>("caller", 0);
		let proposal = make_proposal::<T>(0);
		let value = T::MinimumDeposit::get();
		whitelist_account!(caller);
	}: _(RawOrigin::Signed(caller), proposal, value)
	verify {
		assert_eq!(Democracy::<T>::public_props().len(), p as usize, "Proposals not created.");
	}

	second {
		let caller = funded_account::<T>("caller", 0);
		add_proposal::<T>(0)?;

		// Create s existing "seconds"
		// we must reserve one deposit for the `proposal` and one for our benchmarked `second` call.
		for i in 0 .. T::MaxDeposits::get() - 2 {
			let seconder = funded_account::<T>("seconder", i);
			Democracy::<T>::second(RawOrigin::Signed(seconder).into(), 0)?;
		}

		let deposits = Democracy::<T>::deposit_of(0).ok_or("Proposal not created")?;
		assert_eq!(deposits.0.len(), (T::MaxDeposits::get() - 1) as usize, "Seconds not recorded");
		whitelist_account!(caller);
	}: _(RawOrigin::Signed(caller), 0)
	verify {
		let deposits = Democracy::<T>::deposit_of(0).ok_or("Proposal not created")?;
		assert_eq!(deposits.0.len(), (T::MaxDeposits::get()) as usize, "`second` benchmark did not work");
	}

	vote_new {
		let caller = funded_account::<T>("caller", 0);
		let account_vote = account_vote::<T>(100u32.into());

		// We need to create existing direct votes
		for i in 0 .. T::MaxVotes::get() - 1 {
			let ref_index = add_referendum::<T>(i).0;
			Democracy::<T>::vote(RawOrigin::Signed(caller.clone()).into(), ref_index, account_vote)?;
		}
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), (T::MaxVotes::get() - 1) as usize, "Votes were not recorded.");

		let ref_index = add_referendum::<T>(T::MaxVotes::get() - 1).0;
		whitelist_account!(caller);
	}: vote(RawOrigin::Signed(caller.clone()), ref_index, account_vote)
	verify {
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), T::MaxVotes::get() as usize, "Vote was not recorded.");
	}

	vote_existing {
		let caller = funded_account::<T>("caller", 0);
		let account_vote = account_vote::<T>(100u32.into());

		// We need to create existing direct votes
		for i in 0..T::MaxVotes::get() {
			let ref_index = add_referendum::<T>(i).0;
			Democracy::<T>::vote(RawOrigin::Signed(caller.clone()).into(), ref_index, account_vote)?;
		}
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), T::MaxVotes::get() as usize, "Votes were not recorded.");

		// Change vote from aye to nay
		let nay = Vote { aye: false, conviction: Conviction::Locked1x };
		let new_vote = AccountVote::Standard { vote: nay, balance: 1000u32.into() };
		let ref_index = Democracy::<T>::referendum_count() - 1;

		// This tests when a user changes a vote
		whitelist_account!(caller);
	}: vote(RawOrigin::Signed(caller.clone()), ref_index, new_vote)
	verify {
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), T::MaxVotes::get() as usize, "Vote was incorrectly added");
		let referendum_info = Democracy::<T>::referendum_info(ref_index)
			.ok_or("referendum doesn't exist")?;
		let tally =  match referendum_info {
			ReferendumInfo::Ongoing(r) => r.tally,
			_ => return Err("referendum not ongoing".into()),
		};
		assert_eq!(tally.nays, 1000u32.into(), "changed vote was not recorded");
	}

	emergency_cancel {
		let origin = T::CancellationOrigin::successful_origin();
		let ref_index = add_referendum::<T>(0).0;
		assert_ok!(Democracy::<T>::referendum_status(ref_index));
	}: _<T::RuntimeOrigin>(origin, ref_index)
	verify {
		// Referendum has been canceled
		assert_noop!(
			Democracy::<T>::referendum_status(ref_index),
			Error::<T>::ReferendumInvalid,
		);
	}

	blacklist {
		// Place our proposal at the end to make sure it's worst case.
		for i in 0 .. T::MaxProposals::get() - 1 {
			add_proposal::<T>(i)?;
		}
		// We should really add a lot of seconds here, but we're not doing it elsewhere.

		// Add a referendum of our proposal.
		let (ref_index, hash) = add_referendum::<T>(0);
		assert_ok!(Democracy::<T>::referendum_status(ref_index));
		// Place our proposal in the external queue, too.
		assert_ok!(
			Democracy::<T>::external_propose(T::ExternalOrigin::successful_origin(), make_proposal::<T>(0))
		);
		let origin = T::BlacklistOrigin::successful_origin();
	}: _<T::RuntimeOrigin>(origin, hash, Some(ref_index))
	verify {
		// Referendum has been canceled
		assert_noop!(
			Democracy::<T>::referendum_status(ref_index),
			Error::<T>::ReferendumInvalid
		);
	}

	// Worst case scenario, we external propose a previously blacklisted proposal
	external_propose {
		let origin = T::ExternalOrigin::successful_origin();
		let proposal = make_proposal::<T>(0);
		// Add proposal to blacklist with block number 0

		let addresses: BoundedVec<_, _> = (0..(T::MaxBlacklisted::get() - 1))
			.into_iter()
			.map(|i| account::<T::AccountId>("blacklist", i, SEED))
			.collect::<Vec<_>>()
			.try_into()
			.unwrap();
		Blacklist::<T>::insert(proposal.hash(), (T::BlockNumber::zero(), addresses));
	}: _<T::RuntimeOrigin>(origin, proposal)
	verify {
		// External proposal created
		ensure!(<NextExternal<T>>::exists(), "External proposal didn't work");
	}

	external_propose_majority {
		let origin = T::ExternalMajorityOrigin::successful_origin();
		let proposal = make_proposal::<T>(0);
	}: _<T::RuntimeOrigin>(origin, proposal)
	verify {
		// External proposal created
		ensure!(<NextExternal<T>>::exists(), "External proposal didn't work");
	}

	external_propose_default {
		let origin = T::ExternalDefaultOrigin::successful_origin();
		let proposal = make_proposal::<T>(0);
	}: _<T::RuntimeOrigin>(origin, proposal)
	verify {
		// External proposal created
		ensure!(<NextExternal<T>>::exists(), "External proposal didn't work");
	}

	fast_track {
		let origin_propose = T::ExternalDefaultOrigin::successful_origin();
		let proposal = make_proposal::<T>(0);
		let proposal_hash = proposal.hash();
		Democracy::<T>::external_propose_default(origin_propose, proposal)?;

		// NOTE: Instant origin may invoke a little bit more logic, but may not always succeed.
		let origin_fast_track = T::FastTrackOrigin::successful_origin();
		let voting_period = T::FastTrackVotingPeriod::get();
		let delay = 0u32;
	}: _<T::RuntimeOrigin>(origin_fast_track, proposal_hash, voting_period, delay.into())
	verify {
		assert_eq!(Democracy::<T>::referendum_count(), 1, "referendum not created")
	}

	veto_external {
		let proposal = make_proposal::<T>(0);
		let proposal_hash = proposal.hash();

		let origin_propose = T::ExternalDefaultOrigin::successful_origin();
		Democracy::<T>::external_propose_default(origin_propose, proposal)?;

		let mut vetoers: BoundedVec<T::AccountId, _> = Default::default();
		for i in 0 .. (T::MaxBlacklisted::get() - 1) {
			vetoers.try_push(account::<T::AccountId>("vetoer", i, SEED)).unwrap();
		}
		vetoers.sort();
		Blacklist::<T>::insert(proposal_hash, (T::BlockNumber::zero(), vetoers));

		let origin = T::VetoOrigin::successful_origin();
		ensure!(NextExternal::<T>::get().is_some(), "no external proposal");
	}: _<T::RuntimeOrigin>(origin, proposal_hash)
	verify {
		assert!(NextExternal::<T>::get().is_none());
		let (_, new_vetoers) = <Blacklist<T>>::get(&proposal_hash).ok_or("no blacklist")?;
		assert_eq!(new_vetoers.len(), T::MaxBlacklisted::get() as usize, "vetoers not added");
	}

	cancel_proposal {
		// Place our proposal at the end to make sure it's worst case.
		for i in 0 .. T::MaxProposals::get() {
			add_proposal::<T>(i)?;
		}
		let cancel_origin = T::CancelProposalOrigin::successful_origin();
	}: _<T::RuntimeOrigin>(cancel_origin, 0)

	cancel_referendum {
		let ref_index = add_referendum::<T>(0).0;
	}: _(RawOrigin::Root, ref_index)

	#[extra]
	on_initialize_external {
		let r in 0 .. REFERENDUM_COUNT_HINT;

		for i in 0..r {
			add_referendum::<T>(i);
		}

		assert_eq!(Democracy::<T>::referendum_count(), r, "referenda not created");

		// Launch external
		LastTabledWasExternal::<T>::put(false);

		let origin = T::ExternalMajorityOrigin::successful_origin();
		let proposal = make_proposal::<T>(r);
		let call = Call::<T>::external_propose_majority { proposal };
		call.dispatch_bypass_filter(origin)?;
		// External proposal created
		ensure!(<NextExternal<T>>::exists(), "External proposal didn't work");

		let block_number = T::LaunchPeriod::get();

	}: { Democracy::<T>::on_initialize(block_number) }
	verify {
		// One extra because of next external
		assert_eq!(Democracy::<T>::referendum_count(), r + 1, "referenda not created");
		ensure!(!<NextExternal<T>>::exists(), "External wasn't taken");

		// All but the new next external should be finished
		for i in 0 .. r {
			if let Some(value) = ReferendumInfoOf::<T>::get(i) {
				match value {
					ReferendumInfo::Finished { .. } => (),
					ReferendumInfo::Ongoing(_) => return Err("Referendum was not finished".into()),
				}
			}
		}
	}

	#[extra]
	on_initialize_public {
		let r in 0 .. (T::MaxVotes::get() - 1);

		for i in 0..r {
			add_referendum::<T>(i);
		}

		assert_eq!(Democracy::<T>::referendum_count(), r, "referenda not created");

		// Launch public
		assert!(add_proposal::<T>(r).is_ok(), "proposal not created");
		LastTabledWasExternal::<T>::put(true);

		let block_number = T::LaunchPeriod::get();

	}: { Democracy::<T>::on_initialize(block_number) }
	verify {
		// One extra because of next public
		assert_eq!(Democracy::<T>::referendum_count(), r + 1, "proposal not accepted");

		// All should be finished
		for i in 0 .. r {
			if let Some(value) = ReferendumInfoOf::<T>::get(i) {
				match value {
					ReferendumInfo::Finished { .. } => (),
					ReferendumInfo::Ongoing(_) => return Err("Referendum was not finished".into()),
				}
			}
		}
	}

	// No launch no maturing referenda.
	on_initialize_base {
		let r in 0 .. (T::MaxVotes::get() - 1);

		for i in 0..r {
			add_referendum::<T>(i);
		}

		for (key, mut info) in ReferendumInfoOf::<T>::iter() {
			if let ReferendumInfo::Ongoing(ref mut status) = info {
				status.end += 100u32.into();
			}
			ReferendumInfoOf::<T>::insert(key, info);
		}

		assert_eq!(Democracy::<T>::referendum_count(), r, "referenda not created");
		assert_eq!(Democracy::<T>::lowest_unbaked(), 0, "invalid referenda init");

	}: { Democracy::<T>::on_initialize(1u32.into()) }
	verify {
		// All should be on going
		for i in 0 .. r {
			if let Some(value) = ReferendumInfoOf::<T>::get(i) {
				match value {
					ReferendumInfo::Finished { .. } => return Err("Referendum has been finished".into()),
					ReferendumInfo::Ongoing(_) => (),
				}
			}
		}
	}

	on_initialize_base_with_launch_period {
		let r in 0 .. (T::MaxVotes::get() - 1);

		for i in 0..r {
			add_referendum::<T>(i);
		}

		for (key, mut info) in ReferendumInfoOf::<T>::iter() {
			if let ReferendumInfo::Ongoing(ref mut status) = info {
				status.end += 100u32.into();
			}
			ReferendumInfoOf::<T>::insert(key, info);
		}

		assert_eq!(Democracy::<T>::referendum_count(), r, "referenda not created");
		assert_eq!(Democracy::<T>::lowest_unbaked(), 0, "invalid referenda init");

		let block_number = T::LaunchPeriod::get();

	}: { Democracy::<T>::on_initialize(block_number) }
	verify {
		// All should be on going
		for i in 0 .. r {
			if let Some(value) = ReferendumInfoOf::<T>::get(i) {
				match value {
					ReferendumInfo::Finished { .. } => return Err("Referendum has been finished".into()),
					ReferendumInfo::Ongoing(_) => (),
				}
			}
		}
	}

	delegate {
		let r in 0 .. (T::MaxVotes::get() - 1);

		let initial_balance: BalanceOf<T> = 100u32.into();
		let delegated_balance: BalanceOf<T> = 1000u32.into();

		let caller = funded_account::<T>("caller", 0);
		// Caller will initially delegate to `old_delegate`
		let old_delegate: T::AccountId = funded_account::<T>("old_delegate", r);
		let old_delegate_lookup = T::Lookup::unlookup(old_delegate.clone());
		Democracy::<T>::delegate(
			RawOrigin::Signed(caller.clone()).into(),
			old_delegate_lookup,
			Conviction::Locked1x,
			delegated_balance,
		)?;
		let (target, balance) = match VotingOf::<T>::get(&caller) {
			Voting::Delegating { target, balance, .. } => (target, balance),
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(target, old_delegate, "delegation target didn't work");
		assert_eq!(balance, delegated_balance, "delegation balance didn't work");
		// Caller will now switch to `new_delegate`
		let new_delegate: T::AccountId = funded_account::<T>("new_delegate", r);
		let new_delegate_lookup = T::Lookup::unlookup(new_delegate.clone());
		let account_vote = account_vote::<T>(initial_balance);
		// We need to create existing direct votes for the `new_delegate`
		for i in 0..r {
			let ref_index = add_referendum::<T>(i).0;
			Democracy::<T>::vote(RawOrigin::Signed(new_delegate.clone()).into(), ref_index, account_vote)?;
		}
		let votes = match VotingOf::<T>::get(&new_delegate) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), r as usize, "Votes were not recorded.");
		whitelist_account!(caller);
	}: _(RawOrigin::Signed(caller.clone()), new_delegate_lookup, Conviction::Locked1x, delegated_balance)
	verify {
		let (target, balance) = match VotingOf::<T>::get(&caller) {
			Voting::Delegating { target, balance, .. } => (target, balance),
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(target, new_delegate, "delegation target didn't work");
		assert_eq!(balance, delegated_balance, "delegation balance didn't work");
		let delegations = match VotingOf::<T>::get(&new_delegate) {
			Voting::Direct { delegations, .. } => delegations,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(delegations.capital, delegated_balance, "delegation was not recorded.");
	}

	undelegate {
		let r in 0 .. (T::MaxVotes::get() - 1);

		let initial_balance: BalanceOf<T> = 100u32.into();
		let delegated_balance: BalanceOf<T> = 1000u32.into();

		let caller = funded_account::<T>("caller", 0);
		// Caller will delegate
		let the_delegate: T::AccountId = funded_account::<T>("delegate", r);
		let the_delegate_lookup = T::Lookup::unlookup(the_delegate.clone());
		Democracy::<T>::delegate(
			RawOrigin::Signed(caller.clone()).into(),
			the_delegate_lookup,
			Conviction::Locked1x,
			delegated_balance,
		)?;
		let (target, balance) = match VotingOf::<T>::get(&caller) {
			Voting::Delegating { target, balance, .. } => (target, balance),
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(target, the_delegate, "delegation target didn't work");
		assert_eq!(balance, delegated_balance, "delegation balance didn't work");
		// We need to create votes direct votes for the `delegate`
		let account_vote = account_vote::<T>(initial_balance);
		for i in 0..r {
			let ref_index = add_referendum::<T>(i).0;
			Democracy::<T>::vote(
				RawOrigin::Signed(the_delegate.clone()).into(),
				ref_index,
				account_vote
			)?;
		}
		let votes = match VotingOf::<T>::get(&the_delegate) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), r as usize, "Votes were not recorded.");
		whitelist_account!(caller);
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		// Voting should now be direct
		match VotingOf::<T>::get(&caller) {
			Voting::Direct { .. } => (),
			_ => return Err("undelegation failed".into()),
		}
	}

	clear_public_proposals {
		add_proposal::<T>(0)?;

	}: _(RawOrigin::Root)

	// Test when unlock will remove locks
	unlock_remove {
		let r in 0 .. (T::MaxVotes::get() - 1);

		let locker = funded_account::<T>("locker", 0);
		let locker_lookup = T::Lookup::unlookup(locker.clone());
		// Populate votes so things are locked
		let base_balance: BalanceOf<T> = 100u32.into();
		let small_vote = account_vote::<T>(base_balance);
		// Vote and immediately unvote
		for i in 0 .. r {
			let ref_index = add_referendum::<T>(i).0;
			Democracy::<T>::vote(RawOrigin::Signed(locker.clone()).into(), ref_index, small_vote)?;
			Democracy::<T>::remove_vote(RawOrigin::Signed(locker.clone()).into(), ref_index)?;
		}

		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
	}: unlock(RawOrigin::Signed(caller), locker_lookup)
	verify {
		// Note that we may want to add a `get_lock` api to actually verify
		let voting = VotingOf::<T>::get(&locker);
		assert_eq!(voting.locked_balance(), BalanceOf::<T>::zero());
	}

	// Test when unlock will set a new value
	unlock_set {
		let r in 0 .. (T::MaxVotes::get() - 1);

		let locker = funded_account::<T>("locker", 0);
		let locker_lookup = T::Lookup::unlookup(locker.clone());
		// Populate votes so things are locked
		let base_balance: BalanceOf<T> = 100u32.into();
		let small_vote = account_vote::<T>(base_balance);
		for i in 0 .. r {
			let ref_index = add_referendum::<T>(i).0;
			Democracy::<T>::vote(RawOrigin::Signed(locker.clone()).into(), ref_index, small_vote)?;
		}

		// Create a big vote so lock increases
		let big_vote = account_vote::<T>(base_balance * 10u32.into());
		let ref_index = add_referendum::<T>(r).0;
		Democracy::<T>::vote(RawOrigin::Signed(locker.clone()).into(), ref_index, big_vote)?;

		let votes = match VotingOf::<T>::get(&locker) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), (r + 1) as usize, "Votes were not recorded.");

		let voting = VotingOf::<T>::get(&locker);
		assert_eq!(voting.locked_balance(), base_balance * 10u32.into());

		Democracy::<T>::remove_vote(RawOrigin::Signed(locker.clone()).into(), ref_index)?;

		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
	}: unlock(RawOrigin::Signed(caller), locker_lookup)
	verify {
		let votes = match VotingOf::<T>::get(&locker) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), r as usize, "Vote was not removed");

		let voting = VotingOf::<T>::get(&locker);
		// Note that we may want to add a `get_lock` api to actually verify
		assert_eq!(voting.locked_balance(), if r > 0 { base_balance } else { 0u32.into() });
	}

	remove_vote {
		let r in 1 .. T::MaxVotes::get();

		let caller = funded_account::<T>("caller", 0);
		let account_vote = account_vote::<T>(100u32.into());

		for i in 0 .. r {
			let ref_index = add_referendum::<T>(i).0;
			Democracy::<T>::vote(RawOrigin::Signed(caller.clone()).into(), ref_index, account_vote)?;
		}

		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), r as usize, "Votes not created");

		let ref_index = r - 1;
		whitelist_account!(caller);
	}: _(RawOrigin::Signed(caller.clone()), ref_index)
	verify {
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), (r - 1) as usize, "Vote was not removed");
	}

	// Worst case is when target == caller and referendum is ongoing
	remove_other_vote {
		let r in 1 .. T::MaxVotes::get();

		let caller = funded_account::<T>("caller", r);
		let caller_lookup = T::Lookup::unlookup(caller.clone());
		let account_vote = account_vote::<T>(100u32.into());

		for i in 0 .. r {
			let ref_index = add_referendum::<T>(i).0;
			Democracy::<T>::vote(RawOrigin::Signed(caller.clone()).into(), ref_index, account_vote)?;
		}

		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), r as usize, "Votes not created");

		let ref_index = r - 1;
		whitelist_account!(caller);
	}: _(RawOrigin::Signed(caller.clone()), caller_lookup, ref_index)
	verify {
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct".into()),
		};
		assert_eq!(votes.len(), (r - 1) as usize, "Vote was not removed");
	}

	impl_benchmark_test_suite!(
		Democracy,
		crate::tests::new_test_ext(),
		crate::tests::Test
	);
}
