// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Democratic system: Handles administration of general stakeholder voting.

use rstd::prelude::*;
use integer_sqrt::IntegerSquareRoot;
use codec::KeyedVec;
use runtime_support::storage;
use demo_primitives::{Proposal, AccountId, Hash, BlockNumber};
use runtime::{staking, system, session};

const CURRENT_PROPOSAL: &[u8] = b"gov:pro";
const VOTE_OF: &[u8] = b"gov:vot:";
const VOTERS: &[u8] = b"gov:vtr:";

pub mod public {
	use super::*;

	/// Get the voters for the current proposal.
	pub fn voters() -> Vec<AccountId> {
		storage::get_or_default(VOTERS)
	}

	/// Get the vote, if Some, of `who`.
	pub fn vote_of(who: &AccountId) -> Option<bool> {
		storage::get(&who.to_keyed_vec(VOTE_OF))
	}

	/// Get the voters for the current proposal.
	pub fn tally() -> (staking::Balance, staking::Balance) {
		voters().iter()
			.map(|a| (staking::balance(a), vote_of(a).expect("all items come from `voters`; for an item to be in `voters` there must be a vote registered; qed")))
			.map(|(bal, vote)| if vote { (bal, 0) } else { (0, bal) })
			.fold((0, 0), |(a, b), (c, d)| (a + c, b + d))
	}

	/// Propose a sensitive action to be taken. Any action that is enactable by `Proposal` is valid.
	/// Proposal is by the `transactor` and will automatically count as an approval. Transactor must
	/// be a current validator. It is illegal to propose when there is already a proposal in effect.
	pub fn propose(validator: &AccountId, proposal: &Proposal) {
		if storage::exists(CURRENT_PROPOSAL) {
			panic!("there may only be one proposal per era.");
		}
		storage::put(CURRENT_PROPOSAL, proposal);
	}

	/// Approve the current era's proposal. Transactor must be a validator. This may not be done more
	/// than once for any validator in an era.
	pub fn vote(who: &AccountId, era_index: BlockNumber, way: bool) {
		if era_index != staking::current_era() {
			panic!("approval vote applied on non-current era.")
		}
		if !storage::exists(CURRENT_PROPOSAL) {
			panic!("there must be a proposal in order to approve.");
		}
		if staking::balance(who) == 0 {
			panic!("transactor must have balance to signal approval.");
		}
		let key = who.to_keyed_vec(VOTE_OF);
		if !storage::exists(&key) {
			let mut voters = voters();
			voters.push(who.clone());
			storage::put(VOTERS, &voters);
		}
		storage::put(&key, &way);
	}
}

pub mod privileged {
	use super::*;

	pub fn clear_proposal() {
		for v in public::voters() {
			storage::kill(&v.to_keyed_vec(VOTE_OF));
		}
		storage::kill(VOTERS);
	}
}

pub mod internal {
	use super::*;
	use demo_primitives::Proposal;
	use dispatch::enact_proposal;

	/// Current era is ending; we should finish up any proposals.
	pub fn end_of_an_era() {
		// tally up votes for the current proposal, if any. enact if there are sufficient approvals.
		if let Some(proposal) = storage::take::<Proposal>(CURRENT_PROPOSAL) {
			let tally = public::tally();
			let total_stake = staking::total_stake();
			privileged::clear_proposal();

			// TODO: protect against overflows.
			let threshold = (tally.0 + tally.1).integer_sqrt() * tally.0 / total_stake.integer_sqrt();

			if tally.1 < threshold {
				enact_proposal(proposal);
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use codec::{KeyedVec, Joiner};
	use keyring::Keyring;
	use environment::with_env;
	use demo_primitives::{AccountId, Proposal};
	use runtime::{staking, session, democracy};

	fn new_test_ext() -> TestExternalities {
		let alice = Keyring::Alice.to_raw_public();
		let bob = Keyring::Bob.to_raw_public();
		let charlie = Keyring::Charlie.to_raw_public();
		let dave = Keyring::Dave.to_raw_public();
		let eve = Keyring::Eve.to_raw_public();
		let ferdie = Keyring::Ferdie.to_raw_public();

		map![
			twox_128(b"ses:len").to_vec() => vec![].and(&1u64),
			twox_128(b"ses:val:len").to_vec() => vec![].and(&3u32),
			twox_128(&0u32.to_keyed_vec(b"ses:val:")).to_vec() => alice.to_vec(),
			twox_128(&1u32.to_keyed_vec(b"ses:val:")).to_vec() => bob.to_vec(),
			twox_128(&2u32.to_keyed_vec(b"ses:val:")).to_vec() => charlie.to_vec(),
			twox_128(b"sta:wil:len").to_vec() => vec![].and(&3u32),
			twox_128(&0u32.to_keyed_vec(b"sta:wil:")).to_vec() => alice.to_vec(),
			twox_128(&1u32.to_keyed_vec(b"sta:wil:")).to_vec() => bob.to_vec(),
			twox_128(&2u32.to_keyed_vec(b"sta:wil:")).to_vec() => charlie.to_vec(),
			twox_128(&alice.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].and(&10u64),
			twox_128(&bob.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].and(&20u64),
			twox_128(&charlie.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].and(&30u64),
			twox_128(&dave.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].and(&40u64),
			twox_128(&eve.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].and(&50u64),
			twox_128(&ferdie.to_keyed_vec(b"sta:bal:")).to_vec() => vec![].and(&60u64),
			twox_128(b"sta:tot").to_vec() => vec![].and(&210u64),
			twox_128(b"sta:spe").to_vec() => vec![].and(&1u64),
			twox_128(b"sta:vac").to_vec() => vec![].and(&3u64),
			twox_128(b"sta:era").to_vec() => vec![].and(&1u64)
		]
	}

	#[test]
	fn majority_voting_should_work() {
		let alice = Keyring::Alice.to_raw_public();
		let bob = Keyring::Bob.to_raw_public();
		let charlie = Keyring::Charlie.to_raw_public();
		let dave = Keyring::Dave.to_raw_public();
		let eve = Keyring::Eve.to_raw_public();
		let ferdie = Keyring::Ferdie.to_raw_public();
		let mut t = new_test_ext();

		with_externalities(&mut t, || {
			assert_eq!(staking::era_length(), 1u64);
			assert_eq!(staking::total_stake(), 210u64);

			// Block 1: Make proposal. Approve it. Era length changes.
			with_env(|e| e.block_number = 1);
			public::propose(&alice, &Proposal::StakingSetSessionsPerEra(2));
			public::vote(&ferdie, 1, true);

			assert_eq!(public::tally(), (60, 0));

			democracy::internal::end_of_an_era();
			staking::internal::check_new_era();

			assert_eq!(staking::era_length(), 2u64);
		});
	}
}
