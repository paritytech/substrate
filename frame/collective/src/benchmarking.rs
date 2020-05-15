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
use frame_system::EventRecord;
use frame_benchmarking::{benchmarks_instance, account};
use sp_runtime::traits::Bounded;
use sp_std::mem::size_of;

use frame_system::Call as SystemCall;
use frame_system::Module as System;
use crate::Module as Collective;

const SEED: u32 = 0;

const MAX_BYTES: u32 = 1_024;

fn assert_last_event<T: Trait<I>, I: Instance>(generic_event: <T as Trait<I>>::Event) {
	let events = System::<T>::events();
	let system_event: <T as frame_system::Trait>::Event = generic_event.into();
	// compare to the last event record
	let EventRecord { event, .. } = &events[events.len() - 1];
	assert_eq!(event, &system_event);
}

benchmarks_instance! {
	_{ }

	set_members {
		let m in 1 .. MAX_MEMBERS;
		let n in 1 .. MAX_MEMBERS;
		let p in 1 .. T::MaxProposals::get();

		// Set old members.
		// We compute the difference of old and new members, so it should influence timing.
		let mut old_members = vec![];
		let mut last_old_member = T::AccountId::default();
		for i in 0 .. m {
			last_old_member = account("old member", i, SEED);
			old_members.push(last_old_member.clone());
		}
		let old_members_count = old_members.len() as u32;

		Collective::<T, _>::set_members(
			SystemOrigin::Root.into(),
			old_members.clone(),
			Some(last_old_member.clone()),
			MAX_MEMBERS,
		)?;

		// Set a high threshold for proposals passing so that they stay around.
		let threshold = m.max(2);
		// Length of the proposals should be irrelevant to `set_members`.
		let length = 100;
		for i in 0 .. p {
			// Proposals should be different so that different proposal hashes are generated
			let proposal: T::Proposal = SystemCall::<T>::remark(vec![i as u8; length]).into();
			Collective::<T, _>::propose(
				SystemOrigin::Signed(last_old_member.clone()).into(),
				threshold,
				Box::new(proposal.clone()),
				MAX_BYTES,
			)?;
			let hash = T::Hashing::hash_of(&proposal);
			// Vote on the proposal to increase state relevant for `set_members`.
			// Not voting for `last_old_member` because they proposed and not voting for the first member
			// to keep the proposal from passing.
			for j in 2 .. m - 1 {
				let voter = &old_members[j as usize];
				let approve = true;
				Collective::<T, _>::vote(
					SystemOrigin::Signed(voter.clone()).into(),
					hash,
					i,
					approve,
				)?;
			}
		}

		// Construct `new_members`.
		// It should influence timing since it will sort this vector.
		let mut new_members = vec![];
		let mut last_member = T::AccountId::default();
		for i in 0 .. n {
			last_member = account("member", i, SEED);
			new_members.push(last_member.clone());
		}

	}: _(SystemOrigin::Root, new_members.clone(), Some(last_member), MAX_MEMBERS)
	verify {
		new_members.sort();
		assert_eq!(Collective::<T, _>::members(), new_members);
	}

	execute {
		let m in 1 .. MAX_MEMBERS;
		let b in 1 .. MAX_BYTES;

		let bytes_in_storage = b + size_of::<u32>() as u32;

		// Construct `members`.
		let mut members = vec![];
		for i in 0 .. m - 1 {
			let member = account("member", i, SEED);
			members.push(member);
		}

		let caller: T::AccountId = account("caller", 0, SEED);
		members.push(caller.clone());

		Collective::<T, _>::set_members(SystemOrigin::Root.into(), members, None, MAX_MEMBERS)?;

		let proposal: T::Proposal = SystemCall::<T>::remark(vec![1; b as usize]).into();

	}: _(SystemOrigin::Signed(caller), Box::new(proposal.clone()), bytes_in_storage)
	verify {
		let proposal_hash = T::Hashing::hash_of(&proposal);
		// Note that execution fails due to mis-matched origin
		assert_last_event::<T, I>(
			RawEvent::MemberExecuted(proposal_hash, Err(DispatchError::BadOrigin)).into()
		);
	}

	// This tests when execution would happen immediately after proposal
	propose_execute {
		let m in 1 .. MAX_MEMBERS;
		let b in 1 .. MAX_BYTES;

		let bytes_in_storage = b + size_of::<u32>() as u32;

		// Construct `members`.
		let mut members = vec![];
		for i in 0 .. m - 1 {
			let member = account("member", i, SEED);
			members.push(member);
		}

		let caller: T::AccountId = account("caller", 0, SEED);
		members.push(caller.clone());

		Collective::<T, _>::set_members(SystemOrigin::Root.into(), members, None, MAX_MEMBERS)?;

		let proposal: T::Proposal = SystemCall::<T>::remark(vec![1; b as usize]).into();
		let threshold = 1;

	}: propose(SystemOrigin::Signed(caller), threshold, Box::new(proposal.clone()), bytes_in_storage)
	verify {
		let proposal_hash = T::Hashing::hash_of(&proposal);
		// Note that execution fails due to mis-matched origin
		assert_last_event::<T, I>(
			RawEvent::Executed(proposal_hash, Err(DispatchError::BadOrigin)).into()
		);
	}

	// This tests when proposal is created and queued as "proposed"
	propose_proposed {
		let m in 2 .. MAX_MEMBERS;
		let p in 1 .. T::MaxProposals::get();
		let b in 1 .. MAX_BYTES;

		let bytes_in_storage = b + size_of::<u32>() as u32;

		// Construct `members`.
		let mut members = vec![];
		for i in 0 .. m - 1 {
			let member = account("member", i, SEED);
			members.push(member);
		}
		let caller: T::AccountId = account("caller", 0, SEED);
		members.push(caller.clone());
		Collective::<T, _>::set_members(SystemOrigin::Root.into(), members, None, MAX_MEMBERS)?;

		let threshold = m;
		// Add previous proposals.
		for i in 0 .. p - 1 {
			// Proposals should be different so that different proposal hashes are generated
			let proposal: T::Proposal = SystemCall::<T>::remark(vec![i as u8; b as usize]).into();
			Collective::<T, _>::propose(
				SystemOrigin::Signed(caller.clone()).into(),
				threshold,
				Box::new(proposal),
				bytes_in_storage,
			)?;
		}

		assert_eq!(Collective::<T, _>::proposals().len(), (p - 1) as usize);

		let proposal: T::Proposal = SystemCall::<T>::remark(vec![p as u8; b as usize]).into();

	}: propose(SystemOrigin::Signed(caller.clone()), threshold, Box::new(proposal.clone()), bytes_in_storage)
	verify {
		// New proposal is recorded
		assert_eq!(Collective::<T, _>::proposals().len(), p as usize);
		let proposal_hash = T::Hashing::hash_of(&proposal);
		assert_last_event::<T, I>(RawEvent::Proposed(caller, p - 1, proposal_hash, threshold).into());
	}

	vote {
		// We choose 5 as a minimum so we always trigger a vote in the voting loop (`for j in ...`)
		let m in 5 .. MAX_MEMBERS;

		let p = T::MaxProposals::get();
		let b = MAX_BYTES;
		let bytes_in_storage = b + size_of::<u32>() as u32;

		// Construct `members`.
		let mut members = vec![];
		let proposer: T::AccountId = account("proposer", 0, SEED);
		members.push(proposer.clone());
		for i in 1 .. m - 1 {
			let member = account("member", i, SEED);
			members.push(member);
		}
		let voter: T::AccountId = account("voter", 0, SEED);
		members.push(voter.clone());
		Collective::<T, _>::set_members(SystemOrigin::Root.into(), members.clone(), None, MAX_MEMBERS)?;

		// Threshold is 1 less than the number of members so that one person can vote nay
		let threshold = m - 1;

		// Add previous proposals
		let mut last_hash = T::Hash::default();
		for i in 0 .. p {
			// Proposals should be different so that different proposal hashes are generated
			let proposal: T::Proposal = SystemCall::<T>::remark(vec![i as u8; b as usize]).into();
			Collective::<T, _>::propose(
				SystemOrigin::Signed(proposer.clone()).into(),
				threshold,
				Box::new(proposal.clone()),
				bytes_in_storage,
			)?;
			last_hash = T::Hashing::hash_of(&proposal);
		}

		let index = p - 1;
		// Have almost everyone vote aye on last proposal, while keeping it from passing.
		// Proposer already voted aye so we start at 1.
		for j in 1 .. m - 3 {
			let voter = &members[j as usize];
			let approve = true;
			Collective::<T, _>::vote(
				SystemOrigin::Signed(voter.clone()).into(),
				last_hash.clone(),
				index,
				approve,
			)?;
		}
		// Voter votes aye without resolving the vote.
		let approve = true;
		Collective::<T, _>::vote(
			SystemOrigin::Signed(voter.clone()).into(),
			last_hash.clone(),
			index,
			approve,
		)?;

		assert_eq!(Collective::<T, _>::proposals().len(), p as usize);

		// Voter switches vote to nay, but does not kill the vote, just updates + inserts
		let approve = false;

	}: _(SystemOrigin::Signed(voter), last_hash.clone(), index, approve)
	verify {
		// All proposals exist and the last proposal has just been updated.
		assert_eq!(Collective::<T, _>::proposals().len(), p as usize);
		let voting = Collective::<T, _>::voting(&last_hash).ok_or(Error::<T, I>::ProposalMissing)?;
		assert_eq!(voting.ayes.len(), (m - 3) as usize);
		assert_eq!(voting.nays.len(), 1);
	}

	close_early_disapproved {
		// We choose 4 as a minimum so we always trigger a vote in the voting loop (`for j in ...`)
		let m in 4 .. MAX_MEMBERS;
		let p in 1 .. T::MaxProposals::get();
		let b in 1 .. MAX_BYTES;

		let bytes_in_storage = b + size_of::<u32>() as u32;

		// Construct `members`.
		let mut members = vec![];
		let proposer: T::AccountId = account("proposer", 0, SEED);
		members.push(proposer.clone());
		for i in 1 .. m - 1 {
			let member = account("member", i, SEED);
			members.push(member);
		}
		let voter: T::AccountId = account("voter", 0, SEED);
		members.push(voter.clone());
		Collective::<T, _>::set_members(SystemOrigin::Root.into(), members.clone(), None, MAX_MEMBERS)?;

		// Threshold is total members so that one nay will disapprove the vote
		let threshold = m;

		// Add previous proposals
		let mut last_hash = T::Hash::default();
		for i in 0 .. p {
			// Proposals should be different so that different proposal hashes are generated
			let proposal: T::Proposal = SystemCall::<T>::remark(vec![i as u8; b as usize]).into();
			Collective::<T, _>::propose(
				SystemOrigin::Signed(proposer.clone()).into(),
				threshold,
				Box::new(proposal.clone()),
				bytes_in_storage,
			)?;
			last_hash = T::Hashing::hash_of(&proposal);
		}

		let index = p - 1;
		// Have most everyone vote aye on last proposal, while keeping it from passing.
		// Proposer already voted aye so we start at 1.
		for j in 1 .. m - 2 {
			let voter = &members[j as usize];
			let approve = true;
			Collective::<T, _>::vote(
				SystemOrigin::Signed(voter.clone()).into(),
				last_hash.clone(),
				index,
				approve,
			)?;
		}
		// Voter votes aye without resolving the vote.
		let approve = true;
		Collective::<T, _>::vote(
			SystemOrigin::Signed(voter.clone()).into(),
			last_hash.clone(),
			index,
			approve,
		)?;

		assert_eq!(Collective::<T, _>::proposals().len(), p as usize);

		// Voter switches vote to nay, which kills the vote
		let approve = false;
		Collective::<T, _>::vote(
			SystemOrigin::Signed(voter.clone()).into(),
			last_hash.clone(),
			index,
			approve,
		)?;

	}: close(SystemOrigin::Signed(voter), last_hash.clone(), index, Weight::max_value(), bytes_in_storage)
	verify {
		// The last proposal is removed.
		assert_eq!(Collective::<T, _>::proposals().len(), (p - 1) as usize);
		assert_last_event::<T, I>(RawEvent::Disapproved(last_hash).into());
	}

	close_early_approved {
		// We choose 4 as a minimum so we always trigger a vote in the voting loop (`for j in ...`)
		let m in 4 .. MAX_MEMBERS;
		let p in 1 .. T::MaxProposals::get();
		let b in 1 .. MAX_BYTES;

		let bytes_in_storage = b + size_of::<u32>() as u32;

		// Construct `members`.
		let mut members = vec![];
		for i in 0 .. m - 1 {
			let member = account("member", i, SEED);
			members.push(member);
		}
		let caller: T::AccountId = account("caller", 0, SEED);
		members.push(caller.clone());
		Collective::<T, _>::set_members(SystemOrigin::Root.into(), members.clone(), None, MAX_MEMBERS)?;

		// Threshold is 2 so any two ayes will approve the vote
		let threshold = 2;

		// Add previous proposals
		let mut last_hash = T::Hash::default();
		for i in 0 .. p {
			// Proposals should be different so that different proposal hashes are generated
			let proposal: T::Proposal = SystemCall::<T>::remark(vec![i as u8; b as usize]).into();
			Collective::<T, _>::propose(
				SystemOrigin::Signed(caller.clone()).into(),
				threshold,
				Box::new(proposal.clone()),
				bytes_in_storage,
			)?;
			last_hash = T::Hashing::hash_of(&proposal);
		}

		// Caller switches vote to nay on their own proposal, allowing them to be the deciding approval vote
		Collective::<T, _>::vote(
			SystemOrigin::Signed(caller.clone()).into(),
			last_hash.clone(),
			p - 1,
			false,
		)?;

		// Have almost everyone vote nay on last proposal, while keeping it from failing.
		for j in 2 .. m - 1 {
			let voter = &members[j as usize];
			let approve = false;
			Collective::<T, _>::vote(
				SystemOrigin::Signed(voter.clone()).into(),
				last_hash.clone(),
				p - 1,
				approve,
			)?;
		}

		// Member zero is the first aye
		Collective::<T, _>::vote(
			SystemOrigin::Signed(members[0].clone()).into(),
			last_hash.clone(),
			p - 1,
			true,
		)?;

		assert_eq!(Collective::<T, _>::proposals().len(), p as usize);

		// Caller switches vote to aye, which passes the vote
		let index = p - 1;
		let approve = true;
		Collective::<T, _>::vote(
			SystemOrigin::Signed(caller.clone()).into(),
			last_hash.clone(),
			index, approve,
		)?;

	}: close(SystemOrigin::Signed(caller), last_hash.clone(), index, Weight::max_value(), bytes_in_storage)
	verify {
		// The last proposal is removed.
		assert_eq!(Collective::<T, _>::proposals().len(), (p - 1) as usize);
		assert_last_event::<T, I>(RawEvent::Executed(last_hash, Err(DispatchError::BadOrigin)).into());
	}

	close_disapproved {
		// We choose 4 as a minimum so we always trigger a vote in the voting loop (`for j in ...`)
		let m in 4 .. MAX_MEMBERS;
		let p in 1 .. T::MaxProposals::get();
		let b in 1 .. MAX_BYTES;

		let bytes_in_storage = b + size_of::<u32>() as u32;

		// Construct `members`.
		let mut members = vec![];
		for i in 0 .. m - 1 {
			let member = account("member", i, SEED);
			members.push(member);
		}
		let caller: T::AccountId = account("caller", 0, SEED);
		members.push(caller.clone());
		Collective::<T, _>::set_members(
			SystemOrigin::Root.into(),
			members.clone(),
			Some(caller.clone()),
			MAX_MEMBERS,
		)?;

		// Threshold is one less than total members so that two nays will disapprove the vote
		let threshold = m - 1;

		// Add proposals
		let mut last_hash = T::Hash::default();
		for i in 0 .. p {
			// Proposals should be different so that different proposal hashes are generated
			let proposal: T::Proposal = SystemCall::<T>::remark(vec![i as u8; b as usize]).into();
			Collective::<T, _>::propose(
				SystemOrigin::Signed(caller.clone()).into(),
				threshold,
				Box::new(proposal.clone()),
				bytes_in_storage,
			)?;
			last_hash = T::Hashing::hash_of(&proposal);
		}

		let index = p - 1;
		// Have almost everyone vote aye on last proposal, while keeping it from passing.
		// A few abstainers will be the nay votes needed to fail the vote.
		for j in 2 .. m - 1 {
			let voter = &members[j as usize];
			let approve = true;
			Collective::<T, _>::vote(
				SystemOrigin::Signed(voter.clone()).into(),
				last_hash.clone(),
				index,
				approve,
			)?;
		}

		// caller is prime, prime votes nay
		Collective::<T, _>::vote(
			SystemOrigin::Signed(caller.clone()).into(),
			last_hash.clone(),
			index,
			false,
		)?;

		System::<T>::set_block_number(T::BlockNumber::max_value());
		assert_eq!(Collective::<T, _>::proposals().len(), p as usize);

		// Prime nay will close it as disapproved
	}: close(SystemOrigin::Signed(caller), last_hash, index, Weight::max_value(), bytes_in_storage)
	verify {
		assert_eq!(Collective::<T, _>::proposals().len(), (p - 1) as usize);
		assert_last_event::<T, I>(RawEvent::Disapproved(last_hash).into());
	}

	close_approved {
		// We choose 4 as a minimum so we always trigger a vote in the voting loop (`for j in ...`)
		let m in 4 .. MAX_MEMBERS;
		let p in 1 .. T::MaxProposals::get();
		let b in 1 .. MAX_BYTES;

		let bytes_in_storage = b + size_of::<u32>() as u32;

		// Construct `members`.
		let mut members = vec![];
		for i in 0 .. m - 1 {
			let member = account("member", i, SEED);
			members.push(member);
		}
		let caller: T::AccountId = account("caller", 0, SEED);
		members.push(caller.clone());
		Collective::<T, _>::set_members(
			SystemOrigin::Root.into(),
			members.clone(),
			Some(caller.clone()),
			MAX_MEMBERS,
		)?;

		// Threshold is two, so any two ayes will pass the vote
		let threshold = 2;

		// Add proposals
		let mut last_hash = T::Hash::default();
		for i in 0 .. p {
			// Proposals should be different so that different proposal hashes are generated
			let proposal: T::Proposal = SystemCall::<T>::remark(vec![i as u8; b as usize]).into();
			Collective::<T, _>::propose(
				SystemOrigin::Signed(caller.clone()).into(),
				threshold,
				Box::new(proposal.clone()),
				bytes_in_storage,
			)?;
			last_hash = T::Hashing::hash_of(&proposal);
		}

		// Have almost everyone vote nay on last proposal, while keeping it from failing.
		// A few abstainers will be the aye votes needed to pass the vote.
		for j in 2 .. m - 1 {
			let voter = &members[j as usize];
			let approve = false;
			Collective::<T, _>::vote(
				SystemOrigin::Signed(voter.clone()).into(),
				last_hash.clone(),
				p - 1,
				approve
			)?;
		}

		// caller is prime, prime already votes aye by creating the proposal
		System::<T>::set_block_number(T::BlockNumber::max_value());
		assert_eq!(Collective::<T, _>::proposals().len(), p as usize);

		// Prime aye will close it as approved
	}: close(SystemOrigin::Signed(caller), last_hash, p - 1, Weight::max_value(), bytes_in_storage)
	verify {
		assert_eq!(Collective::<T, _>::proposals().len(), (p - 1) as usize);
		assert_last_event::<T, I>(RawEvent::Executed(last_hash, Err(DispatchError::BadOrigin)).into());
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn set_members() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_set_members::<Test>());
		});
	}

	#[test]
	fn execute() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_execute::<Test>());
		});
	}

	#[test]
	fn propose_execute() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_propose_execute::<Test>());
		});
	}

	#[test]
	fn propose_proposed() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_propose_proposed::<Test>());
		});
	}

	#[test]
	fn vote() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_vote::<Test>());
		});
	}

	#[test]
	fn close_early_disapproved() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_close_early_disapproved::<Test>());
		});
	}

	#[test]
	fn close_early_approved() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_close_early_approved::<Test>());
		});
	}

	#[test]
	fn close_disapproved() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_close_disapproved::<Test>());
		});
	}

	#[test]
	fn close_approved() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_close_approved::<Test>());
		});
	}
}
