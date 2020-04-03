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
use frame_support::traits::{Currency, Get, EnsureOrigin};
use frame_system::{RawOrigin, Module as System, self};
use sp_runtime::traits::{Bounded, One};

use crate::Module as Democracy;

const SEED: u32 = 0;
const MAX_USERS: u32 = 1000;
const MAX_REFERENDUMS: u32 = 100;
const MAX_PROPOSALS: u32 = 100;
const MAX_SECONDERS: u32 = 100;
const MAX_VETOERS: u32 = 100;
const MAX_BYTES: u32 = 16_384;

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
		0.into(),
		proposal_hash,
		vote_threshold,
		0.into(),
	);
	let referendum_index: ReferendumIndex = ReferendumCount::get() - 1;
	let _ = T::Scheduler::schedule_named(
		(DEMOCRACY_ID, referendum_index),
		0.into(),
		None,
		63,
		Call::enact_proposal(proposal_hash, referendum_index).into(),
	);
	Ok(referendum_index)
}

fn account_vote<T: Trait>() -> AccountVote<BalanceOf<T>> {
	let v = Vote {
		aye: true,
		conviction: Conviction::Locked1x,
	};

	AccountVote::Standard {
		vote: v,
		balance: BalanceOf::<T>::one(),
	}
}

fn open_activate_proxy<T: Trait>(u: u32) -> Result<T::AccountId, &'static str> {
	let caller = funded_account::<T>("caller", u);
	let proxy = funded_account::<T>("proxy", u);

	Democracy::<T>::open_proxy(RawOrigin::Signed(proxy.clone()).into(), caller.clone())?;
	Democracy::<T>::activate_proxy(RawOrigin::Signed(caller).into(), proxy.clone())?;

	Ok(proxy)
}

benchmarks! {
	_ { }

	propose {
		let p in 1 .. MAX_PROPOSALS;

		// Add p proposals
		for i in 0 .. p {
			add_proposal::<T>(i)?;
		}

		let caller = funded_account::<T>("caller", 0);
		let proposal_hash: T::Hash = T::Hashing::hash_of(&p);
		let value = T::MinimumDeposit::get();
	}: _(RawOrigin::Signed(caller), proposal_hash, value.into())

	second {
		let s in 0 .. MAX_SECONDERS;

		// Create s existing "seconds"
		for i in 0 .. s {
			let seconder = funded_account::<T>("seconder", i);
			Democracy::<T>::second(RawOrigin::Signed(seconder).into(), 0)?;
		}

		let caller = funded_account::<T>("caller", 0);
		let proposal_hash = add_proposal::<T>(s)?;
	}: _(RawOrigin::Signed(caller), 0)

	vote {
		let r in 1 .. MAX_REFERENDUMS;

		let caller = funded_account::<T>("caller", 0);
		let account_vote = account_vote::<T>();

		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(caller.clone()).into(), ref_idx, account_vote.clone())?;
		}

		let referendum_index = r - 1;

	}: _(RawOrigin::Signed(caller), referendum_index, account_vote)

	proxy_vote {
		let r in 1 .. MAX_REFERENDUMS;

		let caller = funded_account::<T>("caller", r);
		let proxy = open_activate_proxy::<T>(r)?;
		let account_vote = account_vote::<T>();

		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(caller.clone()).into(), ref_idx, account_vote.clone())?;
		}

		let referendum_index = r - 1;

	}: _(RawOrigin::Signed(proxy), referendum_index, account_vote)

	emergency_cancel {
		let u in 1 .. MAX_USERS;

		let referendum_index = add_referendum::<T>(u)?;
		let origin = T::CancellationOrigin::successful_origin();
		let call = Call::<T>::emergency_cancel(referendum_index);
	}: {
		let _ = call.dispatch(origin)?;
	}

	external_propose {
		let u in 1 .. MAX_USERS;

		let origin = T::ExternalOrigin::successful_origin();
		let proposal_hash = T::Hashing::hash_of(&u);
		let call = Call::<T>::external_propose(proposal_hash);
	}: {
		let _ = call.dispatch(origin)?;
	}

	external_propose_majority {
		let u in 1 .. MAX_USERS;

		let origin = T::ExternalMajorityOrigin::successful_origin();
		let proposal_hash = T::Hashing::hash_of(&u);
		let call = Call::<T>::external_propose_majority(proposal_hash);

	}: {
		let _ = call.dispatch(origin)?;
	}

	external_propose_default {
		let u in 1 .. MAX_USERS;

		let origin = T::ExternalDefaultOrigin::successful_origin();
		let proposal_hash = T::Hashing::hash_of(&u);
		let call = Call::<T>::external_propose_default(proposal_hash);

	}: {
		let _ = call.dispatch(origin)?;
	}

	fast_track {
		let u in 1 .. MAX_USERS;

		let origin_propose = T::ExternalDefaultOrigin::successful_origin();
		let proposal_hash: T::Hash = T::Hashing::hash_of(&u);
		Democracy::<T>::external_propose_default(origin_propose, proposal_hash.clone())?;

		let origin_fast_track = T::FastTrackOrigin::successful_origin();
		let voting_period = T::FastTrackVotingPeriod::get();
		let delay = 0;
		let call = Call::<T>::fast_track(proposal_hash, voting_period.into(), delay.into());

	}: {
		let _ = call.dispatch(origin_fast_track)?;
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
		Blacklist::<T>::insert(proposal_hash, (T::BlockNumber::zero(), vetoers));

		let call = Call::<T>::veto_external(proposal_hash);
		let origin = T::VetoOrigin::successful_origin();
	}: {
		let _ = call.dispatch(origin)?;
	}

	cancel_referendum {
		let u in 1 .. MAX_USERS;

		let referendum_index = add_referendum::<T>(u)?;
	}: _(RawOrigin::Root, referendum_index)

	cancel_queued {
		let u in 1 .. MAX_USERS;

		let referendum_index = add_referendum::<T>(u)?;
	}: _(RawOrigin::Root, referendum_index)

	open_proxy {
		let u in 1 .. MAX_USERS;

		let caller: T::AccountId = funded_account::<T>("caller", u);
		let proxy: T::AccountId = funded_account::<T>("proxy", u);

	}: _(RawOrigin::Signed(proxy), caller)

	activate_proxy {
		let u in 1 .. MAX_USERS;

		let caller: T::AccountId = funded_account::<T>("caller", u);
		let proxy: T::AccountId = funded_account::<T>("proxy", u);
		Democracy::<T>::open_proxy(RawOrigin::Signed(proxy.clone()).into(), caller.clone())?;

	}: _(RawOrigin::Signed(caller), proxy)

	close_proxy {
		let u in 1 .. MAX_USERS;

		let proxy = open_activate_proxy::<T>(u)?;

	}: _(RawOrigin::Signed(proxy))

	deactivate_proxy {
		let u in 1 .. MAX_USERS;

		let caller = funded_account::<T>("caller", u);
		let proxy = open_activate_proxy::<T>(u)?;

	}: _(RawOrigin::Signed(caller), proxy)

	delegate {
		let u in 1 .. MAX_USERS;

		let caller = funded_account::<T>("caller", u);
		let d: T::AccountId = funded_account::<T>("delegate", u);
		let balance = 1u32;

	}: _(RawOrigin::Signed(caller), d.into(), Conviction::Locked1x, balance.into())

	undelegate {
		let r in 1 .. MAX_REFERENDUMS;

		let other = funded_account::<T>("other", 0);
		let account_vote = account_vote::<T>();

		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(other.clone()).into(), ref_idx, account_vote.clone())?;
		}

		let delegator = funded_account::<T>("delegator", r);
		let conviction = Conviction::Locked1x;
		let balance = 1u32;

		Democracy::<T>::delegate(RawOrigin::Signed(delegator.clone()).into(), other.clone().into(), conviction, balance.into())?;

	}: _(RawOrigin::Signed(delegator))

	clear_public_proposals {
		let p in 0 .. MAX_PROPOSALS;

		for i in 0 .. p {
			add_proposal::<T>(i)?;
		}

	}: _(RawOrigin::Root)

	note_preimage {
		// Num of bytes in encoded proposal
		let b in 0 .. MAX_BYTES;

		let caller = funded_account::<T>("caller", b);
		let encoded_proposal = vec![0; b as usize];
	}: _(RawOrigin::Signed(caller), encoded_proposal)

	note_imminent_preimage {
		// Num of bytes in encoded proposal
		let b in 0 .. MAX_BYTES;

		// d + 1 to include the one we are testing
		let encoded_proposal = vec![0; b as usize];
		let proposal_hash = T::Hashing::hash(&encoded_proposal[..]);
		let block_number = T::BlockNumber::one();
		Preimages::<T>::insert(&proposal_hash, PreimageStatus::Missing(block_number));

		let caller = funded_account::<T>("caller", b);
		let encoded_proposal = vec![0; b as usize];
	}: _(RawOrigin::Signed(caller), encoded_proposal)

	reap_preimage {
		// Num of bytes in encoded proposal
		let b in 0 .. MAX_BYTES;

		let encoded_proposal = vec![0; b as usize];
		let proposal_hash = T::Hashing::hash(&encoded_proposal[..]);

		let caller = funded_account::<T>("caller", b);
		Democracy::<T>::note_preimage(RawOrigin::Signed(caller.clone()).into(), encoded_proposal.clone())?;

		// We need to set this otherwise we get `Early` error.
		let block_number = T::VotingPeriod::get() + T::EnactmentPeriod::get() + T::BlockNumber::one();
		System::<T>::set_block_number(block_number.into());

	}: _(RawOrigin::Signed(caller), proposal_hash)

	unlock {
		let u in 1 .. MAX_USERS;

		let caller = funded_account::<T>("caller", u);
		let locked_until = T::BlockNumber::zero();
		Locks::<T>::insert(&caller, locked_until);

		T::Currency::extend_lock(
			DEMOCRACY_ID,
			&caller,
			Bounded::max_value(),
			WithdrawReason::Transfer.into()
		);

		let other = caller.clone();

	}: _(RawOrigin::Signed(caller), other)

	remove_vote {
		let r in 1 .. MAX_REFERENDUMS;

		let caller = funded_account::<T>("caller", 0);
		let account_vote = account_vote::<T>();

		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(caller.clone()).into(), ref_idx, account_vote.clone())?;
		}

		let referendum_index = r - 1;

	}: _(RawOrigin::Signed(caller), referendum_index)

	remove_other_vote {
		let r in 1 .. MAX_REFERENDUMS;

		let other = funded_account::<T>("other", r);
		let account_vote = account_vote::<T>();

		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(other.clone()).into(), ref_idx, account_vote.clone())?;
		}

		let referendum_index = r - 1;
		ReferendumInfoOf::<T>::insert(
			referendum_index,
			ReferendumInfo::Finished { end: T::BlockNumber::zero(), approved: true }
		);
		let caller = funded_account::<T>("caller", r);

		System::<T>::set_block_number(T::EnactmentPeriod::get() * 10u32.into());

	}: _(RawOrigin::Signed(caller), other, referendum_index)

	proxy_delegate {
		let u in 1 .. MAX_USERS;

		let other: T::AccountId = account("other", u, SEED);
		let proxy = open_activate_proxy::<T>(u)?;
		let conviction = Conviction::Locked1x;
		let balance = 1u32;

	}: _(RawOrigin::Signed(proxy), other, conviction, balance.into())

	proxy_undelegate {
		let r in 1 .. MAX_REFERENDUMS;

		let other = funded_account::<T>("other", 0);
		let account_vote = account_vote::<T>();

		for i in 0 .. r {
			let ref_idx = add_referendum::<T>(i)?;
			Democracy::<T>::vote(RawOrigin::Signed(other.clone()).into(), ref_idx, account_vote.clone())?;
		}

		let proxy = open_activate_proxy::<T>(r)?;
		let conviction = Conviction::Locked1x;
		let balance = 1u32;
		Democracy::<T>::proxy_delegate(RawOrigin::Signed(proxy.clone()).into(), other, conviction, balance.into())?;

	}: _(RawOrigin::Signed(proxy))

	proxy_remove_vote {
		let u in 1 .. MAX_USERS;

		let referendum_index = add_referendum::<T>(u)?;
		let account_vote = account_vote::<T>();
		let proxy = open_activate_proxy::<T>(u)?;

		Democracy::<T>::proxy_vote(RawOrigin::Signed(proxy.clone()).into(), referendum_index, account_vote)?;

	}: _(RawOrigin::Signed(proxy), referendum_index)
}
