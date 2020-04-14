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

//! Staking pallet benchmarking.

use super::*;

use frame_system::RawOrigin as SystemOrigin;
use frame_benchmarking::{benchmarks_instance, account};

use frame_system::Module as System;
use crate::Module as Collective;

const SEED: u32 = 0;

benchmarks_instance! {
	_{
		// User account seed.
		let u in 1 .. 1000 => ();
		// Old members.
		let n in 1 .. 1000 => ();
		// New members.
		let m in 1 .. 1000 => ();
		// Existing proposals.
		let p in 1 .. 100 => ();
	}

	set_members {
		let m in ...;
		let n in ...;

		// Construct `new_members`.
		// It should influence timing since it will sort this vector.
		let mut new_members = vec![];
		for i in 0 .. m {
			let member = account("member", i, SEED);
			new_members.push(member);
		}

		// Set old members.
		// We compute the difference of old and new members, so it should influence timing.
		let mut old_members = vec![];
		for i in 0 .. n {
			let old_member = account("old member", i, SEED);
			old_members.push(old_member);
		}

		let prime = Some(account("prime", 0, SEED));

		Collective::<T, _>::set_members(SystemOrigin::Root.into(), old_members, prime.clone())?;

	}: _(SystemOrigin::Root, new_members.clone(), prime)
	verify {
		new_members.sort();
		assert_eq!(Collective::<T, _>::members(), new_members);
	}

	execute {
		let u in ...;

		let caller: T::AccountId = account("caller", u, SEED);
		let proposal: T::Proposal = Call::<T, I>::close(Default::default(), Default::default()).into();

		Collective::<T, _>::set_members(SystemOrigin::Root.into(), vec![caller.clone()], None)?;

	}: _(SystemOrigin::Signed(caller), Box::new(proposal))

	propose {
		let u in ...;

		let caller: T::AccountId = account("caller", u, SEED);
		let proposal: T::Proposal = Call::<T, I>::close(Default::default(), Default::default()).into();

		Collective::<T, _>::set_members(SystemOrigin::Root.into(), vec![caller.clone()], None)?;

		let member_count = 0;

	}: _(SystemOrigin::Signed(caller), member_count, Box::new(proposal.into()))

	propose_else_branch {
		let u in ...;
		let p in ...;

		let caller: T::AccountId = account("caller", u, SEED);
		let proposal: T::Proposal = Call::<T, I>::close(Default::default(), Default::default()).into();

		Collective::<T, _>::set_members(SystemOrigin::Root.into(), vec![caller.clone()], None)?;

		let member_count = 3;

		// Add previous proposals.
		for i in 0 .. p {
			let proposal: T::Proposal = Call::<T, I>::close(Default::default(), (i + 1).into()).into();
			Collective::<T, _>::propose(SystemOrigin::Signed(caller.clone()).into(), member_count.clone(), Box::new(proposal.into()))?;
		}

	}: propose(SystemOrigin::Signed(caller), member_count, Box::new(proposal.into()))

	vote {
		let u in ...;

		let caller1: T::AccountId = account("caller1", u, SEED);
		let caller2: T::AccountId = account("caller2", u, SEED);

		let proposal: Box<T::Proposal> = Box::new(Call::<T, I>::close(Default::default(), Default::default()).into());
		let proposal_hash = T::Hashing::hash_of(&proposal);

		Collective::<T, _>::set_members(SystemOrigin::Root.into(), vec![caller1.clone(), caller2.clone()], None)?;

		let member_count = 3;
		Collective::<T, _>::propose(SystemOrigin::Signed(caller1.clone()).into(), member_count, proposal)?;

		let index = 0;
		let approve = true;

	}: _(SystemOrigin::Signed(caller2), proposal_hash, index, approve)

	vote_not_approve {
		let u in ...;

		let caller1: T::AccountId = account("caller1", u, SEED);
		let caller2: T::AccountId = account("caller2", u, SEED);

		let proposal: Box<T::Proposal> = Box::new(Call::<T, I>::close(Default::default(), Default::default()).into());
		let proposal_hash = T::Hashing::hash_of(&proposal);

		Collective::<T, _>::set_members(SystemOrigin::Root.into(), vec![caller1.clone(), caller2.clone()], None)?;

		let member_count = 3;
		Collective::<T, _>::propose(SystemOrigin::Signed(caller1.clone()).into(), member_count, proposal)?;

		let index = 0;
		let approve = false;

	}: vote(SystemOrigin::Signed(caller2), proposal_hash, index, approve)

	vote_approved {
		let u in ...;

		let caller1: T::AccountId = account("caller1", u, SEED);
		let caller2: T::AccountId = account("caller2", u, SEED);

		let proposal: Box<T::Proposal> = Box::new(Call::<T, I>::close(Default::default(), Default::default()).into());
		let proposal_hash = T::Hashing::hash_of(&proposal);

		Collective::<T, _>::set_members(SystemOrigin::Root.into(), vec![caller1.clone(), caller2.clone()], None)?;

		let member_count = 2;
		Collective::<T, _>::propose(SystemOrigin::Signed(caller1.clone()).into(), member_count, proposal)?;

		let index = 0;
		let approve = true;

	}: vote(SystemOrigin::Signed(caller2), proposal_hash, index, approve)

	close {
		let u in ...;

		let caller1: T::AccountId = account("caller1", u, SEED);
		let caller2: T::AccountId = account("caller2", u, SEED);

		let proposal: Box<T::Proposal> = Box::new(Call::<T, I>::close(Default::default(), Default::default()).into());
		let proposal_hash = T::Hashing::hash_of(&proposal);

		Collective::<T, _>::set_members(SystemOrigin::Root.into(), vec![caller1.clone(), caller2.clone()], None)?;
		let member_count = 2;
		Collective::<T, _>::propose(SystemOrigin::Signed(caller1.clone()).into(), member_count, proposal)?;

		let index = 0;
		let approve = true;

		let vote_end = T::MotionDuration::get() + 1u32.into();
		System::<T>::set_block_number(vote_end);

	}: _(SystemOrigin::Signed(caller2), proposal_hash, index)
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_set_members::<Test>());
			assert_ok!(test_benchmark_execute::<Test>());
			assert_ok!(test_benchmark_propose::<Test>());
			assert_ok!(test_benchmark_propose_else_branch::<Test>());
			assert_ok!(test_benchmark_vote::<Test>());
			assert_ok!(test_benchmark_vote_not_approve::<Test>());
			assert_ok!(test_benchmark_vote_approved::<Test>());
			assert_ok!(test_benchmark_close::<Test>());
		});
	}
}
