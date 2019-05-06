// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Council voting system.

use rstd::prelude::*;
use rstd::result;
use substrate_primitives::u32_trait::Value as U32;
use primitives::traits::{Hash, EnsureOrigin};
use srml_support::dispatch::{Dispatchable, Parameter};
use srml_support::{StorageValue, StorageMap, decl_module, decl_event, decl_storage, ensure};
use super::{Trait as CouncilTrait, Module as Council};
use system::{self, ensure_signed};

/// Simple index type for proposal counting.
pub type ProposalIndex = u32;

pub trait Trait: CouncilTrait {
	/// The outer origin type.
	type Origin: From<Origin>;

	/// The outer call dispatch type.
	type Proposal: Parameter + Dispatchable<Origin=<Self as Trait>::Origin>;

	/// The outer event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;
}

/// Origin for the council module.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum Origin {
	/// It has been condoned by a given number of council members.
	Members(u32),
}

decl_event!(
	pub enum Event<T> where <T as system::Trait>::Hash, <T as system::Trait>::AccountId {
		/// A motion (given hash) has been proposed (by given account) with a threshold (given u32).
		Proposed(AccountId, ProposalIndex, Hash, u32),
		/// A motion (given hash) has been voted on by given account, leaving
		/// a tally (yes votes and no votes given as u32s respectively).
		Voted(AccountId, Hash, bool, u32, u32),
		/// A motion was approved by the required threshold.
		Approved(Hash),
		/// A motion was not approved by the required threshold.
		Disapproved(Hash),
		/// A motion was executed; `bool` is true if returned without error.
		Executed(Hash, bool),
	}
);

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: <T as system::Trait>::Origin {
		fn deposit_event<T>() = default;
		fn propose(origin, #[compact] threshold: u32, proposal: Box<<T as Trait>::Proposal>) {
			let who = ensure_signed(origin)?;

			ensure!(Self::is_councillor(&who), "proposer not on council");

			let proposal_hash = T::Hashing::hash_of(&proposal);

			ensure!(!<ProposalOf<T>>::exists(proposal_hash), "duplicate proposals not allowed");

			if threshold < 2 {
				let ok = proposal.dispatch(Origin::Members(1).into()).is_ok();
				Self::deposit_event(RawEvent::Executed(proposal_hash, ok));
			} else {
				let index = Self::proposal_count();
				<ProposalCount<T>>::mutate(|i| *i += 1);
				<Proposals<T>>::mutate(|proposals| proposals.push(proposal_hash));
				<ProposalOf<T>>::insert(proposal_hash, *proposal);
				<Voting<T>>::insert(proposal_hash, (index, threshold, vec![who.clone()], vec![]));

				Self::deposit_event(RawEvent::Proposed(who, index, proposal_hash, threshold));
			}
		}

		fn vote(origin, proposal: T::Hash, #[compact] index: ProposalIndex, approve: bool) {
			let who = ensure_signed(origin)?;

			ensure!(Self::is_councillor(&who), "voter not on council");

			let mut voting = Self::voting(&proposal).ok_or("proposal must exist")?;
			ensure!(voting.0 == index, "mismatched index");

			let position_yes = voting.2.iter().position(|a| a == &who);
			let position_no = voting.3.iter().position(|a| a == &who);

			if approve {
				if position_yes.is_none() {
					voting.2.push(who.clone());
				} else {
					return Err("duplicate vote ignored")
				}
				if let Some(pos) = position_no {
					voting.3.swap_remove(pos);
				}
			} else {
				if position_no.is_none() {
					voting.3.push(who.clone());
				} else {
					return Err("duplicate vote ignored")
				}
				if let Some(pos) = position_yes {
					voting.2.swap_remove(pos);
				}
			}

			let yes_votes = voting.2.len() as u32;
			let no_votes = voting.3.len() as u32;
			Self::deposit_event(RawEvent::Voted(who, proposal, approve, yes_votes, no_votes));

			let threshold = voting.1;
			let potential_votes = <Council<T>>::active_council().len() as u32;
			let approved = yes_votes >= threshold;
			let disapproved = potential_votes.saturating_sub(no_votes) < threshold;
			if approved || disapproved {
				if approved {
					Self::deposit_event(RawEvent::Approved(proposal));

					// execute motion, assuming it exists.
					if let Some(p) = <ProposalOf<T>>::take(&proposal) {
						let ok = p.dispatch(Origin::Members(threshold).into()).is_ok();
						Self::deposit_event(RawEvent::Executed(proposal, ok));
					}
				} else {
					// disapproved
					Self::deposit_event(RawEvent::Disapproved(proposal));
				}

				// remove vote
				<Voting<T>>::remove(&proposal);
				<Proposals<T>>::mutate(|proposals| proposals.retain(|h| h != &proposal));
			} else {
				// update voting
				<Voting<T>>::insert(&proposal, voting);
			}
		}
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as CouncilMotions {
		/// The (hashes of) the active proposals.
		pub Proposals get(proposals): Vec<T::Hash>;
		/// Actual proposal for a given hash, if it's current.
		pub ProposalOf get(proposal_of): map T::Hash => Option< <T as Trait>::Proposal >;
		/// Votes for a given proposal: (required_yes_votes, yes_voters, no_voters).
		pub Voting get(voting): map T::Hash => Option<(ProposalIndex, u32, Vec<T::AccountId>, Vec<T::AccountId>)>;
		/// Proposals so far.
		pub ProposalCount get(proposal_count): u32;
	}
	add_extra_genesis {
		build(|_, _, _| {});
	}
}

impl<T: Trait> Module<T> {
	pub fn is_councillor(who: &T::AccountId) -> bool {
		<Council<T>>::active_council().iter()
			.any(|&(ref a, _)| a == who)
	}
}

/// Ensure that the origin `o` represents at least `n` council members. Returns
/// `Ok` or an `Err` otherwise.
pub fn ensure_council_members<OuterOrigin>(o: OuterOrigin, n: u32) -> result::Result<u32, &'static str>
	where OuterOrigin: Into<Option<Origin>>
{
	match o.into() {
		Some(Origin::Members(x)) if x >= n => Ok(n),
		_ => Err("bad origin: expected to be a threshold number of council members"),
	}
}

pub struct EnsureMembers<N: U32>(::rstd::marker::PhantomData<N>);
impl<O, N: U32> EnsureOrigin<O> for EnsureMembers<N>
	where O: Into<Option<Origin>>
{
	type Success = u32;
	fn ensure_origin(o: O) -> result::Result<Self::Success, &'static str> {
		ensure_council_members(o, N::VALUE)
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use super::RawEvent;
	use crate::tests::*;
	use crate::tests::{Call, Origin, Event as OuterEvent};
	use srml_support::{Hashable, assert_ok, assert_noop};
	use system::{EventRecord, Phase};
	use hex_literal::hex;

	#[test]
	fn motions_basic_environment_works() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			assert_eq!(Balances::free_balance(&42), 0);
			assert_eq!(CouncilMotions::proposals(), Vec::<H256>::new());
		});
	}

	fn set_balance_proposal(value: u64) -> Call {
		Call::Balances(balances::Call::set_balance(42, value.into(), 0))
	}

	#[test]
	fn motions_propose_works() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			let hash = proposal.blake2_256().into();
			assert_ok!(CouncilMotions::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_eq!(CouncilMotions::proposals(), vec![hash]);
			assert_eq!(CouncilMotions::proposal_of(&hash), Some(proposal));
			assert_eq!(CouncilMotions::voting(&hash), Some((0, 3, vec![1], Vec::<u64>::new())));

			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: OuterEvent::motions(RawEvent::Proposed(1, 0, hex!["cd0b662a49f004093b80600415cf4126399af0d27ed6c185abeb1469c17eb5bf"].into(), 3))
				}
			]);
		});
	}

	#[test]
	fn motions_ignoring_non_council_proposals_works() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			assert_noop!(CouncilMotions::propose(Origin::signed(42), 3, Box::new(proposal.clone())), "proposer not on council");
		});
	}

	#[test]
	fn motions_ignoring_non_council_votes_works() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			let hash: H256 = proposal.blake2_256().into();
			assert_ok!(CouncilMotions::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_noop!(CouncilMotions::vote(Origin::signed(42), hash.clone(), 0, true), "voter not on council");
		});
	}

	#[test]
	fn motions_ignoring_bad_index_council_vote_works() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(3);
			let proposal = set_balance_proposal(42);
			let hash: H256 = proposal.blake2_256().into();
			assert_ok!(CouncilMotions::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_noop!(CouncilMotions::vote(Origin::signed(2), hash.clone(), 1, true), "mismatched index");
		});
	}

	#[test]
	fn motions_revoting_works() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			let hash: H256 = proposal.blake2_256().into();
			assert_ok!(CouncilMotions::propose(Origin::signed(1), 2, Box::new(proposal.clone())));
			assert_eq!(CouncilMotions::voting(&hash), Some((0, 2, vec![1], Vec::<u64>::new())));
			assert_noop!(CouncilMotions::vote(Origin::signed(1), hash.clone(), 0, true), "duplicate vote ignored");
			assert_ok!(CouncilMotions::vote(Origin::signed(1), hash.clone(), 0, false));
			assert_eq!(CouncilMotions::voting(&hash), Some((0, 2, Vec::<u64>::new(), vec![1])));
			assert_noop!(CouncilMotions::vote(Origin::signed(1), hash.clone(), 0, false), "duplicate vote ignored");

			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: OuterEvent::motions(RawEvent::Proposed(1, 0, hex!["cd0b662a49f004093b80600415cf4126399af0d27ed6c185abeb1469c17eb5bf"].into(), 2))
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: OuterEvent::motions(RawEvent::Voted(1, hex!["cd0b662a49f004093b80600415cf4126399af0d27ed6c185abeb1469c17eb5bf"].into(), false, 0, 1))
				}
			]);
		});
	}

	#[test]
	fn motions_disapproval_works() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			let hash: H256 = proposal.blake2_256().into();
			assert_ok!(CouncilMotions::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_ok!(CouncilMotions::vote(Origin::signed(2), hash.clone(), 0, false));

			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: OuterEvent::motions(RawEvent::Proposed(1, 0, hex!["cd0b662a49f004093b80600415cf4126399af0d27ed6c185abeb1469c17eb5bf"].into(), 3))
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: OuterEvent::motions(RawEvent::Voted(2, hex!["cd0b662a49f004093b80600415cf4126399af0d27ed6c185abeb1469c17eb5bf"].into(), false, 1, 1))
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: OuterEvent::motions(RawEvent::Disapproved(hex!["cd0b662a49f004093b80600415cf4126399af0d27ed6c185abeb1469c17eb5bf"].into()))
				}
			]);
		});
	}

	#[test]
	fn motions_approval_works() {
		with_externalities(&mut new_test_ext(true), || {
			System::set_block_number(1);
			let proposal = set_balance_proposal(42);
			let hash: H256 = proposal.blake2_256().into();
			assert_ok!(CouncilMotions::propose(Origin::signed(1), 2, Box::new(proposal.clone())));
			assert_ok!(CouncilMotions::vote(Origin::signed(2), hash.clone(), 0, true));

			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: OuterEvent::motions(RawEvent::Proposed(1, 0, hex!["cd0b662a49f004093b80600415cf4126399af0d27ed6c185abeb1469c17eb5bf"].into(), 2))
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: OuterEvent::motions(RawEvent::Voted(2, hex!["cd0b662a49f004093b80600415cf4126399af0d27ed6c185abeb1469c17eb5bf"].into(), true, 2, 0))
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: OuterEvent::motions(RawEvent::Approved(hex!["cd0b662a49f004093b80600415cf4126399af0d27ed6c185abeb1469c17eb5bf"].into()))
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: OuterEvent::motions(RawEvent::Executed(hex!["cd0b662a49f004093b80600415cf4126399af0d27ed6c185abeb1469c17eb5bf"].into(), false))
				}
			]);
		});
	}
}
