// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Democracy pallet benchmarking.

use super::*;

use frame_benchmarking::{benchmarks, account};
use frame_support::{
	IterableStorageMap,
	traits::{Currency, Get, EnsureOrigin, OnInitialize},
};
use frame_system::{RawOrigin, Module as System, self, EventRecord};
use sp_runtime::traits::{Bounded, One};

use crate::Module as Democracy;

const SEED: u32 = 0;
const MAX_USERS: u32 = 1000;
const MAX_REFERENDUMS: u32 = 100;
const MAX_PROPOSALS: u32 = 100;
const MAX_SECONDERS: u32 = 100;
const MAX_VETOERS: u32 = 100;
const MAX_BYTES: u32 = 16_384;

fn assert_last_event<T: Trait>(generic_event: <T as Trait>::Event) {
	let events = System::<T>::events();
	let system_event: <T as frame_system::Trait>::Event = generic_event.into();
	// compare to the last event record
	let EventRecord { event, .. } = &events[events.len() - 1];
	assert_eq!(event, &system_event);
}

fn funded_account<T: Trait>(name: &'static str, index: u32) -> T::AccountId {
	let caller: T::AccountId = account(name, index, SEED);
	T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	caller
}

fn add_proposal<T: Trait>(n: u32) -> Result<T::Hash, &'static str> {
	let other = funded_account::<T>("proposer", n);
	let value = T::MinimumDeposit::get();
	let proposal_hash: T::Hash = T::Hashing::hash_of(&n);

	Democracy::<T>::propose(RawOrigin::Signed(other).into(), proposal_hash, value.into())?;

	Ok(proposal_hash)
}

fn add_referendum<T: Trait>(n: u32) -> Result<ReferendumIndex, &'static str> {
	let proposal_hash = add_proposal::<T>(n)?;
	let vote_threshold = VoteThreshold::SimpleMajority;

	Democracy::<T>::inject_referendum(
		T::LaunchPeriod::get(),
		proposal_hash,
		vote_threshold,
		0.into(),
	);
	let referendum_index: ReferendumIndex = ReferendumCount::get() - 1;
	let _ = T::Scheduler::schedule_named(
		(DEMOCRACY_ID, referendum_index).encode(),
		0.into(),
		None,
		63,
		Call::enact_proposal(proposal_hash, referendum_index).into(),
	);
	Ok(referendum_index)
}

fn account_vote<T: Trait>(b: BalanceOf<T>) -> AccountVote<BalanceOf<T>> {
	let v = Vote {
		aye: true,
		conviction: Conviction::Locked1x,
	};

	AccountVote::Standard {
		vote: v,
		balance: b,
	}
}

fn open_activate_proxy<T: Trait>(u: u32) -> Result<(T::AccountId, T::AccountId), &'static str> {
	let caller = funded_account::<T>("caller", u);
	let voter = funded_account::<T>("voter", u);

	Democracy::<T>::open_proxy(RawOrigin::Signed(caller.clone()).into(), voter.clone())?;
	Democracy::<T>::activate_proxy(RawOrigin::Signed(voter.clone()).into(), caller.clone())?;

	Ok((caller, voter))
}

benchmarks! {
	_ { }

	propose {
		let p in 1 .. MAX_PROPOSALS;

		// Add p proposals
		for i in 0 .. p {
			add_proposal::<T>(i)?;
		}

		assert_eq!(Democracy::<T>::public_props().len(), p as usize, "Proposals not created.");

		let caller = funded_account::<T>("caller", 0);
		let proposal_hash: T::Hash = T::Hashing::hash_of(&p);
		let value = T::MinimumDeposit::get();
	}: _(RawOrigin::Signed(caller), proposal_hash, value.into())
	verify {
		assert_eq!(Democracy::<T>::public_props().len(), (p + 1) as usize, "Proposals not created.");
	}

	second {
		let s in 0 .. MAX_SECONDERS;

		let caller = funded_account::<T>("caller", 0);
		let proposal_hash = add_proposal::<T>(s)?;

		// Create s existing "seconds"
		for i in 0 .. s {
			let seconder = funded_account::<T>("seconder", i);
			Democracy::<T>::second(RawOrigin::Signed(seconder).into(), 0)?;
		}

		let deposits = Democracy::<T>::deposit_of(0).ok_or("Proposal not created")?;
		assert_eq!(deposits.1.len(), (s + 1) as usize, "Seconds not recorded");
	}: _(RawOrigin::Signed(caller), 0)
	verify {
		let deposits = Democracy::<T>::deposit_of(0).ok_or("Proposal not created")?;
		assert_eq!(deposits.1.len(), (s + 2) as usize, "`second` benchmark did not work");
	}

	vote_new {
		let r in 1 .. MAX_REFERENDUMS;

		let caller = funded_account::<T>("caller", 0);
		let account_vote = account_vote::<T>(100.into());

		// We need to create existing direct votes
		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(caller.clone()).into(), ref_idx, account_vote.clone())?;
		}
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), r as usize, "Votes were not recorded.");

		let referendum_index = add_referendum::<T>(r)?;

	}: vote(RawOrigin::Signed(caller.clone()), referendum_index, account_vote)
	verify {
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), (r + 1) as usize, "Vote was not recorded.");
	}

	vote_existing {
		let r in 1 .. MAX_REFERENDUMS;

		let caller = funded_account::<T>("caller", 0);
		let account_vote = account_vote::<T>(100.into());

		// We need to create existing direct votes
		for i in 0 ..=r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(caller.clone()).into(), ref_idx, account_vote.clone())?;
		}
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), (r + 1) as usize, "Votes were not recorded.");

		// Change vote from aye to nay
		let nay = Vote { aye: false, conviction: Conviction::Locked1x };
		let new_vote = AccountVote::Standard { vote: nay, balance: 1000.into() };
		let referendum_index = Democracy::<T>::referendum_count() - 1;

		// This tests when a user changes a vote
	}: vote(RawOrigin::Signed(caller.clone()), referendum_index, new_vote)
	verify {
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), (r + 1) as usize, "Vote was incorrectly added");
		let referendum_info = Democracy::<T>::referendum_info(referendum_index)
			.ok_or("referendum doesn't exist")?;
		let tally =  match referendum_info {
			ReferendumInfo::Ongoing(r) => r.tally,
			_ => return Err("referendum not ongoing"),
		};
		assert_eq!(tally.nays, 1000.into(), "changed vote was not recorded");
	}

	// Basically copy paste of `vote_new`
	proxy_vote_new {
		let r in 1 .. MAX_REFERENDUMS;

		let (caller, voter) = open_activate_proxy::<T>(0)?;
		let account_vote = account_vote::<T>(100.into());

		// Populate existing direct votes for the voter, they can vote on their own behalf
		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(voter.clone()).into(), ref_idx, account_vote.clone())?;
		}

		let referendum_index = add_referendum::<T>(r)?;

	}: proxy_vote(RawOrigin::Signed(caller), referendum_index, account_vote)
	verify {
		let votes = match VotingOf::<T>::get(&voter) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), (r + 1) as usize, "Vote was not recorded.");
	}

	// Basically copy paste of `vote_existing`
	proxy_vote_existing {
		let r in 1 .. MAX_REFERENDUMS;

		let (caller, voter) = open_activate_proxy::<T>(0)?;
		let account_vote = account_vote::<T>(100.into());

		// We need to create existing direct votes
		for i in 0 ..=r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(voter.clone()).into(), ref_idx, account_vote.clone())?;
		}
		let votes = match VotingOf::<T>::get(&voter) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), (r + 1) as usize, "Votes were not recorded.");

		// Change vote from aye to nay
		let nay = Vote { aye: false, conviction: Conviction::Locked1x };
		let new_vote = AccountVote::Standard { vote: nay, balance: 1000.into() };
		let referendum_index = Democracy::<T>::referendum_count() - 1;

		// This tests when a user changes a vote
	}: proxy_vote(RawOrigin::Signed(caller.clone()), referendum_index, new_vote)
	verify {
		let votes = match VotingOf::<T>::get(&voter) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), (r + 1) as usize, "Vote was incorrectly added");
		let referendum_info = Democracy::<T>::referendum_info(referendum_index)
			.ok_or("referendum doesn't exist")?;
		let tally =  match referendum_info {
			ReferendumInfo::Ongoing(r) => r.tally,
			_ => return Err("referendum not ongoing"),
		};
		assert_eq!(tally.nays, 1000.into(), "changed vote was not recorded");
	}

	emergency_cancel {
		let r in 1 .. MAX_REFERENDUMS;
		let origin = T::CancellationOrigin::successful_origin();

		// Create and cancel a bunch of referendums
		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			let call = Call::<T>::emergency_cancel(ref_idx);
			call.dispatch(origin.clone())?;
		}

		// Lets now measure one more
		let referendum_index = add_referendum::<T>(r)?;
		let call = Call::<T>::emergency_cancel(referendum_index);
		assert!(Democracy::<T>::referendum_status(referendum_index).is_ok());
	}: { call.dispatch(origin)? }
	verify {
		// Referendum has been canceled
		assert!(Democracy::<T>::referendum_status(referendum_index).is_err());
	}

	// Worst case scenario, we external propose a previously blacklisted proposal
	external_propose {
		let p in 1 .. MAX_PROPOSALS;
		let v in 1 .. MAX_VETOERS;

		let origin = T::ExternalOrigin::successful_origin();
		let proposal_hash = T::Hashing::hash_of(&p);
		// Add proposal to blacklist with block number 0
		Blacklist::<T>::insert(
			proposal_hash,
			(T::BlockNumber::zero(), vec![T::AccountId::default(); v as usize])
		);

		let call = Call::<T>::external_propose(proposal_hash);
	}: { call.dispatch(origin)? }
	verify {
		// External proposal created
		ensure!(<NextExternal<T>>::exists(), "External proposal didn't work");
	}

	external_propose_majority {
		let p in 1 .. MAX_PROPOSALS;

		let origin = T::ExternalMajorityOrigin::successful_origin();
		let proposal_hash = T::Hashing::hash_of(&p);
		let call = Call::<T>::external_propose_majority(proposal_hash);
	}: { call.dispatch(origin)? }
	verify {
		// External proposal created
		ensure!(<NextExternal<T>>::exists(), "External proposal didn't work");
	}

	external_propose_default {
		let p in 1 .. MAX_PROPOSALS;

		let origin = T::ExternalDefaultOrigin::successful_origin();
		let proposal_hash = T::Hashing::hash_of(&p);
		let call = Call::<T>::external_propose_default(proposal_hash);
	}: { call.dispatch(origin)? }
	verify {
		// External proposal created
		ensure!(<NextExternal<T>>::exists(), "External proposal didn't work");
	}

	fast_track {
		let p in 1 .. MAX_PROPOSALS;

		let origin_propose = T::ExternalDefaultOrigin::successful_origin();
		let proposal_hash: T::Hash = T::Hashing::hash_of(&p);
		Democracy::<T>::external_propose_default(origin_propose, proposal_hash.clone())?;

		// NOTE: Instant origin may invoke a little bit more logic, but may not always succeed.
		let origin_fast_track = T::FastTrackOrigin::successful_origin();
		let voting_period = T::FastTrackVotingPeriod::get();
		let delay = 0;
		let call = Call::<T>::fast_track(proposal_hash, voting_period.into(), delay.into());

	}: { call.dispatch(origin_fast_track)? }
	verify {
		assert_eq!(Democracy::<T>::referendum_count(), 1, "referendum not created")
	}

	veto_external {
		// Existing veto-ers
		let v in 0 .. MAX_VETOERS;

		let proposal_hash: T::Hash = T::Hashing::hash_of(&v);

		let origin_propose = T::ExternalDefaultOrigin::successful_origin();
		Democracy::<T>::external_propose_default(origin_propose, proposal_hash.clone())?;

		let mut vetoers: Vec<T::AccountId> = Vec::new();
		for i in 0 .. v {
			vetoers.push(account("vetoer", i, SEED));
		}
		vetoers.sort();
		Blacklist::<T>::insert(proposal_hash, (T::BlockNumber::zero(), vetoers));

		let call = Call::<T>::veto_external(proposal_hash);
		let origin = T::VetoOrigin::successful_origin();
		ensure!(NextExternal::<T>::get().is_some(), "no external proposal");
	}: { call.dispatch(origin)? }
	verify {
		assert!(NextExternal::<T>::get().is_none());
		let (_, new_vetoers) = <Blacklist<T>>::get(&proposal_hash).ok_or("no blacklist")?;
		assert_eq!(new_vetoers.len(), (v + 1) as usize, "vetoers not added");
	}

	cancel_referendum {
		let r in 0 .. MAX_REFERENDUMS;
		// Should have no effect on the execution time.
		for i in 0..r {
			add_referendum::<T>(i)?;
		}
		let referendum_index = add_referendum::<T>(r)?;
	}: _(RawOrigin::Root, referendum_index)

	cancel_queued {
		let r in 1 .. MAX_REFERENDUMS;
		// Should have no effect on the execution time.
		for i in 0..r {
			add_referendum::<T>(i)?;
		}
		let referendum_index = add_referendum::<T>(r)?;
	}: _(RawOrigin::Root, referendum_index)

	// Note that we have a separate benchmark for `launch_next`
	on_initialize_external {
		let r in 0 .. MAX_REFERENDUMS;

		for i in 0..r {
			add_referendum::<T>(i)?;
		}

		assert_eq!(Democracy::<T>::referendum_count(), r, "referenda not created");

		// Launch external
		LastTabledWasExternal::put(false);

		let origin = T::ExternalMajorityOrigin::successful_origin();
		let proposal_hash = T::Hashing::hash_of(&r);
		let call = Call::<T>::external_propose_majority(proposal_hash);
		call.dispatch(origin)?;
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
					ReferendumInfo::Ongoing(_) => return Err("Referendum was not finished"),
				}
			}
		}
	}

	on_initialize_public {
		let r in 1 .. MAX_REFERENDUMS;

		for i in 0..r {
			add_referendum::<T>(i)?;
		}

		assert_eq!(Democracy::<T>::referendum_count(), r, "referenda not created");

		// Launch public
		LastTabledWasExternal::put(true);

		let block_number = T::LaunchPeriod::get();

	}: { Democracy::<T>::on_initialize(block_number) }
	verify {
		// One extra because of next public
		assert_eq!(Democracy::<T>::referendum_count(), r + 1, "referenda not created");

		// All should be finished
		for i in 0 .. r {
			if let Some(value) = ReferendumInfoOf::<T>::get(i) {
				match value {
					ReferendumInfo::Finished { .. } => (),
					ReferendumInfo::Ongoing(_) => return Err("Referendum was not finished"),
				}
			}
		}
	}

	on_initialize_no_launch_no_maturing {
		let r in 1 .. MAX_REFERENDUMS;

		for i in 0..r {
			add_referendum::<T>(i)?;
		}

		for (key, mut info) in ReferendumInfoOf::<T>::iter() {
			if let ReferendumInfo::Ongoing(ref mut status) = info {
				status.end += 100.into();
			}
			ReferendumInfoOf::<T>::insert(key, info);
		}

		assert_eq!(Democracy::<T>::referendum_count(), r, "referenda not created");
		assert_eq!(Democracy::<T>::lowest_unbaked(), 0, "invalid referenda init");

	}: { Democracy::<T>::on_initialize(0.into()) }
	verify {
		// All should be on going
		for i in 0 .. r {
			if let Some(value) = ReferendumInfoOf::<T>::get(i) {
				match value {
					ReferendumInfo::Finished { .. } => return Err("Referendum has been finished"),
					ReferendumInfo::Ongoing(_) => (),
				}
			}
		}
	}

	activate_proxy {
		let u in 1 .. MAX_USERS;

		let caller: T::AccountId = funded_account::<T>("caller", u);
		let proxy: T::AccountId = funded_account::<T>("proxy", u);
		Democracy::<T>::open_proxy(RawOrigin::Signed(proxy.clone()).into(), caller.clone())?;
	}: _(RawOrigin::Signed(caller.clone()), proxy.clone())
	verify {
		assert_eq!(Democracy::<T>::proxy(proxy), Some(ProxyState::Active(caller)));
	}

	close_proxy {
		let u in 1 .. MAX_USERS;
		let (caller, _) = open_activate_proxy::<T>(u)?;
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		assert_eq!(Democracy::<T>::proxy(caller), None);
	}

	deactivate_proxy {
		let u in 1 .. MAX_USERS;
		let (caller, voter) = open_activate_proxy::<T>(u)?;
	}: _(RawOrigin::Signed(voter.clone()), caller.clone())
	verify {
		assert_eq!(Democracy::<T>::proxy(caller), Some(ProxyState::Open(voter)));
	}

	delegate {
		let r in 1 .. MAX_REFERENDUMS;

		let initial_balance: BalanceOf<T> = 100.into();
		let delegated_balance: BalanceOf<T> = 1000.into();

		let caller = funded_account::<T>("caller", 0);
		// Caller will initially delegate to `old_delegate`
		let old_delegate: T::AccountId = funded_account::<T>("old_delegate", r);
		Democracy::<T>::delegate(
			RawOrigin::Signed(caller.clone()).into(),
			old_delegate.clone(),
			Conviction::Locked1x,
			delegated_balance,
		)?;
		let (target, balance) = match VotingOf::<T>::get(&caller) {
			Voting::Delegating { target, balance, .. } => (target, balance),
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(target, old_delegate, "delegation target didn't work");
		assert_eq!(balance, delegated_balance, "delegation balance didn't work");
		// Caller will now switch to `new_delegate`
		let new_delegate: T::AccountId = funded_account::<T>("new_delegate", r);
		let account_vote = account_vote::<T>(initial_balance);
		// We need to create existing direct votes for the `new_delegate`
		for i in 0..r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(new_delegate.clone()).into(), ref_idx, account_vote.clone())?;
		}
		let votes = match VotingOf::<T>::get(&new_delegate) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), r as usize, "Votes were not recorded.");
	}: _(RawOrigin::Signed(caller.clone()), new_delegate.clone(), Conviction::Locked1x, delegated_balance)
	verify {
		let (target, balance) = match VotingOf::<T>::get(&caller) {
			Voting::Delegating { target, balance, .. } => (target, balance),
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(target, new_delegate, "delegation target didn't work");
		assert_eq!(balance, delegated_balance, "delegation balance didn't work");
		let delegations = match VotingOf::<T>::get(&new_delegate) {
			Voting::Direct { delegations, .. } => delegations,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(delegations.capital, delegated_balance, "delegation was not recorded.");
	}

	undelegate {
		let r in 1 .. MAX_REFERENDUMS;

		let initial_balance: BalanceOf<T> = 100.into();
		let delegated_balance: BalanceOf<T> = 1000.into();

		let caller = funded_account::<T>("caller", 0);
		// Caller will delegate
		let the_delegate: T::AccountId = funded_account::<T>("delegate", r);
		Democracy::<T>::delegate(
			RawOrigin::Signed(caller.clone()).into(),
			the_delegate.clone(),
			Conviction::Locked1x,
			delegated_balance,
		)?;
		let (target, balance) = match VotingOf::<T>::get(&caller) {
			Voting::Delegating { target, balance, .. } => (target, balance),
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(target, the_delegate, "delegation target didn't work");
		assert_eq!(balance, delegated_balance, "delegation balance didn't work");
		// We need to create votes direct votes for the `delegate`
		let account_vote = account_vote::<T>(initial_balance);
		for i in 0..r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(
				RawOrigin::Signed(the_delegate.clone()).into(),
				ref_idx,
				account_vote.clone()
			)?;
		}
		let votes = match VotingOf::<T>::get(&the_delegate) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), r as usize, "Votes were not recorded.");
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		// Voting should now be direct
		match VotingOf::<T>::get(&caller) {
			Voting::Direct { .. } => (),
			_ => return Err("undelegation failed"),
		}
	}

	clear_public_proposals {
		let p in 0 .. MAX_PROPOSALS;

		for i in 0 .. p {
			add_proposal::<T>(i)?;
		}

	}: _(RawOrigin::Root)

	note_preimage {
		// Num of bytes in encoded proposal
		let b in 0 .. MAX_BYTES;

		let caller = funded_account::<T>("caller", 0);
		let encoded_proposal = vec![1; b as usize];
	}: _(RawOrigin::Signed(caller), encoded_proposal.clone())
	verify {
		let proposal_hash = T::Hashing::hash(&encoded_proposal[..]);
		match Preimages::<T>::get(proposal_hash) {
			Some(PreimageStatus::Available { .. }) => (),
			_ => return Err("preimage not available")
		}
	}

	note_imminent_preimage {
		// Num of bytes in encoded proposal
		let b in 0 .. MAX_BYTES;

		// d + 1 to include the one we are testing
		let encoded_proposal = vec![1; b as usize];
		let proposal_hash = T::Hashing::hash(&encoded_proposal[..]);
		let block_number = T::BlockNumber::one();
		Preimages::<T>::insert(&proposal_hash, PreimageStatus::Missing(block_number));

		let caller = funded_account::<T>("caller", 0);
		let encoded_proposal = vec![1; b as usize];
	}: _(RawOrigin::Signed(caller), encoded_proposal.clone())
	verify {
		let proposal_hash = T::Hashing::hash(&encoded_proposal[..]);
		match Preimages::<T>::get(proposal_hash) {
			Some(PreimageStatus::Available { .. }) => (),
			_ => return Err("preimage not available")
		}
	}

	reap_preimage {
		// Num of bytes in encoded proposal
		let b in 0 .. MAX_BYTES;

		let encoded_proposal = vec![1; b as usize];
		let proposal_hash = T::Hashing::hash(&encoded_proposal[..]);

		let submitter = funded_account::<T>("submitter", b);
		Democracy::<T>::note_preimage(RawOrigin::Signed(submitter.clone()).into(), encoded_proposal.clone())?;

		// We need to set this otherwise we get `Early` error.
		let block_number = T::VotingPeriod::get() + T::EnactmentPeriod::get() + T::BlockNumber::one();
		System::<T>::set_block_number(block_number.into());

		assert!(Preimages::<T>::contains_key(proposal_hash));

		let caller = funded_account::<T>("caller", 0);
	}: _(RawOrigin::Signed(caller), proposal_hash.clone())
	verify {
		let proposal_hash = T::Hashing::hash(&encoded_proposal[..]);
		assert!(!Preimages::<T>::contains_key(proposal_hash));
	}

	// Test when unlock will remove locks
	unlock_remove {
		let r in 1 .. MAX_REFERENDUMS;

		let locker = funded_account::<T>("locker", 0);
		// Populate votes so things are locked
		let base_balance: BalanceOf<T> = 100.into();
		let small_vote = account_vote::<T>(base_balance);
		// Vote and immediately unvote
		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(locker.clone()).into(), ref_idx, small_vote.clone())?;
			Democracy::<T>::remove_vote(RawOrigin::Signed(locker.clone()).into(), ref_idx)?;
		}

		let caller = funded_account::<T>("caller", 0);
	}: unlock(RawOrigin::Signed(caller), locker.clone())
	verify {
		// Note that we may want to add a `get_lock` api to actually verify
		let voting = VotingOf::<T>::get(&locker);
		assert_eq!(voting.locked_balance(), BalanceOf::<T>::zero());
	}

	// Test when unlock will set a new value
	unlock_set {
		let r in 1 .. MAX_REFERENDUMS;

		let locker = funded_account::<T>("locker", 0);
		// Populate votes so things are locked
		let base_balance: BalanceOf<T> = 100.into();
		let small_vote = account_vote::<T>(base_balance);
		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(locker.clone()).into(), ref_idx, small_vote.clone())?;
		}

		// Create a big vote so lock increases
		let big_vote = account_vote::<T>(base_balance * 10.into());
		let referendum_index = add_referendum::<T>(r)?;
		Democracy::<T>::vote(RawOrigin::Signed(locker.clone()).into(), referendum_index, big_vote)?;

		let votes = match VotingOf::<T>::get(&locker) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), (r + 1) as usize, "Votes were not recorded.");

		let voting = VotingOf::<T>::get(&locker);
		assert_eq!(voting.locked_balance(), base_balance * 10.into());

		Democracy::<T>::remove_vote(RawOrigin::Signed(locker.clone()).into(), referendum_index)?;

		let caller = funded_account::<T>("caller", 0);
	}: unlock(RawOrigin::Signed(caller), locker.clone())
	verify {
		let votes = match VotingOf::<T>::get(&locker) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), r as usize, "Vote was not removed");

		let voting = VotingOf::<T>::get(&locker);
		// Note that we may want to add a `get_lock` api to actually verify
		assert_eq!(voting.locked_balance(), base_balance);
	}

	open_proxy {
		let u in 1 .. MAX_USERS;

		let caller: T::AccountId = funded_account::<T>("caller", u);
		let proxy: T::AccountId = funded_account::<T>("proxy", u);

	}: _(RawOrigin::Signed(proxy), caller)

	remove_vote {
		let r in 1 .. MAX_REFERENDUMS;

		let caller = funded_account::<T>("caller", 0);
		let account_vote = account_vote::<T>(100.into());

		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(caller.clone()).into(), ref_idx, account_vote.clone())?;
		}

		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), r as usize, "Votes not created");

		let referendum_index = r - 1;

	}: _(RawOrigin::Signed(caller.clone()), referendum_index)
	verify {
		let votes = match VotingOf::<T>::get(&caller) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), (r - 1) as usize, "Vote was not removed");
	}

	remove_other_vote {
		let r in 1 .. MAX_REFERENDUMS;

		let other = funded_account::<T>("other", r);
		let account_vote = account_vote::<T>(100.into());

		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(other.clone()).into(), ref_idx, account_vote.clone())?;
		}

		let votes = match VotingOf::<T>::get(&other) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), r as usize, "Votes not created");

		let referendum_index = r - 1;
		ReferendumInfoOf::<T>::insert(
			referendum_index,
			ReferendumInfo::Finished { end: T::BlockNumber::zero(), approved: true }
		);
		let caller = funded_account::<T>("caller", 0);

		System::<T>::set_block_number(T::EnactmentPeriod::get() * 10u32.into());

	}: _(RawOrigin::Signed(caller), other.clone(), referendum_index)
	verify {
		let votes = match VotingOf::<T>::get(&other) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), (r - 1) as usize, "Vote was not removed");
	}

	// This is a copy of delegate benchmark, but with `open_activate_proxy`
	proxy_delegate {
		let r in 1 .. MAX_REFERENDUMS;

		let initial_balance: BalanceOf<T> = 100.into();
		let delegated_balance: BalanceOf<T> = 1000.into();

		let (caller, voter) = open_activate_proxy::<T>(0)?;

		// Voter will initially delegate to `old_delegate`
		let old_delegate: T::AccountId = funded_account::<T>("old_delegate", r);
		Democracy::<T>::delegate(
			RawOrigin::Signed(voter.clone()).into(),
			old_delegate.clone(),
			Conviction::Locked1x,
			delegated_balance,
		)?;
		let (target, balance) = match VotingOf::<T>::get(&voter) {
			Voting::Delegating { target, balance, .. } => (target, balance),
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(target, old_delegate, "delegation target didn't work");
		assert_eq!(balance, delegated_balance, "delegation balance didn't work");
		// Voter will now switch to `new_delegate`
		let new_delegate: T::AccountId = funded_account::<T>("new_delegate", r);
		let account_vote = account_vote::<T>(initial_balance);
		// We need to create existing direct votes for the `new_delegate`
		for i in 0..r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(new_delegate.clone()).into(), ref_idx, account_vote.clone())?;
		}
		let votes = match VotingOf::<T>::get(&new_delegate) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), r as usize, "Votes were not recorded.");
	}: _(RawOrigin::Signed(caller.clone()), new_delegate.clone(), Conviction::Locked1x, delegated_balance)
	verify {
		let (target, balance) = match VotingOf::<T>::get(&voter) {
			Voting::Delegating { target, balance, .. } => (target, balance),
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(target, new_delegate, "delegation target didn't work");
		assert_eq!(balance, delegated_balance, "delegation balance didn't work");
		let delegations = match VotingOf::<T>::get(&new_delegate) {
			Voting::Direct { delegations, .. } => delegations,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(delegations.capital, delegated_balance, "delegation was not recorded.");
	}

	// This is a copy of undelegate benchmark, but with `open_activate_proxy`
	proxy_undelegate {
		let r in 1 .. MAX_REFERENDUMS;

		let initial_balance: BalanceOf<T> = 100.into();
		let delegated_balance: BalanceOf<T> = 1000.into();

		let (caller, voter) = open_activate_proxy::<T>(0)?;
		// Caller will delegate
		let the_delegate: T::AccountId = funded_account::<T>("delegate", r);
		Democracy::<T>::delegate(
			RawOrigin::Signed(voter.clone()).into(),
			the_delegate.clone(),
			Conviction::Locked1x,
			delegated_balance,
		)?;
		let (target, balance) = match VotingOf::<T>::get(&voter) {
			Voting::Delegating { target, balance, .. } => (target, balance),
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(target, the_delegate, "delegation target didn't work");
		assert_eq!(balance, delegated_balance, "delegation balance didn't work");
		// We need to create votes direct votes for the `delegate`
		let account_vote = account_vote::<T>(initial_balance);
		for i in 0..r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(
				RawOrigin::Signed(the_delegate.clone()).into(),
				ref_idx,
				account_vote.clone()
			)?;
		}
		let votes = match VotingOf::<T>::get(&the_delegate) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), r as usize, "Votes were not recorded.");
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		// Voting should now be direct
		match VotingOf::<T>::get(&voter) {
			Voting::Direct { .. } => (),
			_ => return Err("undelegation failed"),
		}
	}

	proxy_remove_vote {
		let r in 1 .. MAX_REFERENDUMS;

		let (caller, voter) = open_activate_proxy::<T>(0)?;
		let account_vote = account_vote::<T>(100.into());

		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(voter.clone()).into(), ref_idx, account_vote.clone())?;
		}

		let votes = match VotingOf::<T>::get(&voter) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), r as usize, "Votes not created");

		let referendum_index = r - 1;

	}: _(RawOrigin::Signed(caller.clone()), referendum_index)
	verify {
		let votes = match VotingOf::<T>::get(&voter) {
			Voting::Direct { votes, .. } => votes,
			_ => return Err("Votes are not direct"),
		};
		assert_eq!(votes.len(), (r - 1) as usize, "Vote was not removed");
	}

	enact_proposal_execute {
		// Num of bytes in encoded proposal
		let b in 0 .. MAX_BYTES;

		let proposer = funded_account::<T>("proposer", 0);
		let raw_call = Call::note_preimage(vec![1; b as usize]);
		let generic_call: T::Proposal = raw_call.into();
		let encoded_proposal = generic_call.encode();
		let proposal_hash = T::Hashing::hash(&encoded_proposal[..]);
		Democracy::<T>::note_preimage(RawOrigin::Signed(proposer).into(), encoded_proposal)?;

		match Preimages::<T>::get(proposal_hash) {
			Some(PreimageStatus::Available { .. }) => (),
			_ => return Err("preimage not available")
		}
	}: enact_proposal(RawOrigin::Root, proposal_hash, 0)
	verify {
		// Fails due to mismatched origin
		assert_last_event::<T>(RawEvent::Executed(0, false).into());
	}

	enact_proposal_slash {
		// Num of bytes in encoded proposal
		let b in 0 .. MAX_BYTES;

		let proposer = funded_account::<T>("proposer", 0);
		// Random invalid bytes
		let encoded_proposal = vec![200; b as usize];
		let proposal_hash = T::Hashing::hash(&encoded_proposal[..]);
		Democracy::<T>::note_preimage(RawOrigin::Signed(proposer).into(), encoded_proposal)?;

		match Preimages::<T>::get(proposal_hash) {
			Some(PreimageStatus::Available { .. }) => (),
			_ => return Err("preimage not available")
		}
	}: {
		assert_eq!(
			Democracy::<T>::enact_proposal(RawOrigin::Root.into(), proposal_hash, 0),
			Err(Error::<T>::PreimageInvalid.into())
		);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_propose::<Test>());
			assert_ok!(test_benchmark_second::<Test>());
			assert_ok!(test_benchmark_vote_new::<Test>());
			assert_ok!(test_benchmark_vote_existing::<Test>());
			assert_ok!(test_benchmark_proxy_vote_new::<Test>());
			assert_ok!(test_benchmark_proxy_vote_existing::<Test>());
			assert_ok!(test_benchmark_emergency_cancel::<Test>());
			assert_ok!(test_benchmark_external_propose::<Test>());
			assert_ok!(test_benchmark_external_propose_majority::<Test>());
			assert_ok!(test_benchmark_external_propose_default::<Test>());
			assert_ok!(test_benchmark_fast_track::<Test>());
			assert_ok!(test_benchmark_veto_external::<Test>());
			assert_ok!(test_benchmark_cancel_referendum::<Test>());
			assert_ok!(test_benchmark_cancel_queued::<Test>());
			assert_ok!(test_benchmark_on_initialize_external::<Test>());
			assert_ok!(test_benchmark_on_initialize_public::<Test>());
			assert_ok!(test_benchmark_on_initialize_no_launch_no_maturing::<Test>());
			assert_ok!(test_benchmark_open_proxy::<Test>());
			assert_ok!(test_benchmark_activate_proxy::<Test>());
			assert_ok!(test_benchmark_close_proxy::<Test>());
			assert_ok!(test_benchmark_deactivate_proxy::<Test>());
			assert_ok!(test_benchmark_delegate::<Test>());
			assert_ok!(test_benchmark_undelegate::<Test>());
			assert_ok!(test_benchmark_clear_public_proposals::<Test>());
			assert_ok!(test_benchmark_note_preimage::<Test>());
			assert_ok!(test_benchmark_note_imminent_preimage::<Test>());
			assert_ok!(test_benchmark_reap_preimage::<Test>());
			assert_ok!(test_benchmark_unlock_remove::<Test>());
			assert_ok!(test_benchmark_unlock_set::<Test>());
			assert_ok!(test_benchmark_remove_vote::<Test>());
			assert_ok!(test_benchmark_remove_other_vote::<Test>());
			assert_ok!(test_benchmark_proxy_delegate::<Test>());
			assert_ok!(test_benchmark_proxy_undelegate::<Test>());
			assert_ok!(test_benchmark_proxy_remove_vote::<Test>());
			assert_ok!(test_benchmark_enact_proposal_execute::<Test>());
			assert_ok!(test_benchmark_enact_proposal_slash::<Test>());
		});
	}
}
