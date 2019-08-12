// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! An election module based on sequential phragmen.
//!
//! The election happens in _rounds_: every `N` blocks, the all previous members are retired and a
//! new set is elected (which may or may not have some of the same members). Each round lasts for
//! some number of blocks defined by `TermDuration` storage item. Each cycle of election is a term.
//!
//! `TermDuration` might change during a round. This can shorten or extend the length of the round.
//! The next election round's block number is never stored but rather always checked on the fly.
//! Based on the current block number and `TermDuration`, `BlockNumber % TermDuration == 0` will
//! always trigger a new election round.
//!
//! Voters can vote for as many of the candidates by providing a list of account ids. Invalid votes
//! (voting for non-candidates) are ignored during election. Voters reserve a bond as they vote.
//! The entire free balance of a voter is locked upon voting and can only be used to pay for fees.
//! Voters can update their votes by calling `vote()` again during the same round. This does not
//! effect the reserved bond or lock. After a term, voters _must_ call `remove_voter` to get their
//! bond back and remove the lock. Otherwise the bond amount will stay reserved and the lock will
//! persist. Furthermore, voters of an old round cannot vote for the current round until they remove
//! their previous data via `remove_voter`.
//!
//! Candidates also reserve a bond as they submit candidacy. A candidate cannot take their candidacy
//! back. Winner candidates will be moved to the members list and will get their bond back at end of
//! their term. Loser candidates will immediately get their bond back. Note that unlike phragmen in
//! staking, candidates do NOT automatically vote for themselves (though they _could_ via a separate
//! transaction). Furthermore, the amount of tokens (stake) held by the candidate does not matter.

#![cfg_attr(not(feature = "std"), no_std)]

use sr_primitives::traits::{Zero, StaticLookup, Bounded, Convert};
use sr_primitives::weights::SimpleDispatchInfo;
use srml_support::{StorageValue, StorageMap, EnumerableStorageMap, decl_storage, decl_event, ensure,
	decl_module, dispatch::Result,
	traits::{Currency, Get, LockableCurrency, LockIdentifier, ReservableCurrency, WithdrawReason,
		WithdrawReasons, ChangeMembers
	}
};
use system::{self, ensure_signed, ensure_root};

const MODULE_ID: LockIdentifier = *b"phrelect";

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;

pub const DEFAULT_CANDIDACY_BOND: u32 = 9;
pub const DEFAULT_VOTING_BOND: u32 = 2;

pub trait Trait: system::Trait {
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// The currency that people are electing with.
	type Currency:
		LockableCurrency<Self::AccountId, Moment=Self::BlockNumber> +
		ReservableCurrency<Self::AccountId>;

	/// What to do when the members change.
	type ChangeMembers: ChangeMembers<Self::AccountId>;

	/// Convert a balance into a number used for election calculation.
	/// This must fit into a `u64` but is allowed to be sensibly lossy.
	type CurrencyToVote: Convert<BalanceOf<Self>, u64> + Convert<u128, BalanceOf<Self>>;

	/// How much should be locked up in order to submit one's candidacy.
	type CandidacyBond: Get<BalanceOf<Self>>;

	/// How much should be locked up in order to be able to submit votes.
	type VotingBond: Get<BalanceOf<Self>>;
}

decl_storage! {
	trait Store for Module<T: Trait> as PhragmenElection {
		// ---- parameters
		/// Number of seats to elect.
		pub DesiredSeats get(desired_seats) config(): u32;
		/// The total number of vote rounds that have happened, exclusive of the upcoming one.
		pub ElectionRounds get(election_rounds): u32 = Zero::zero();
		/// How long each seat is kept. This defined the next block number at which an election
		/// round will happen.
		pub TermDuration get(term_duration) config(): T::BlockNumber;

		// ---- State
		/// The current elected membership.
		pub Members get(members) config(): Vec<T::AccountId>;

		/// Votes of a particular voter, with the round index of the votes.
		pub VotesOf get(votes_of): linked_map T::AccountId => (Vec<T::AccountId>, u32);
		/// Locked stake of a voter.
		pub StakeOf get(stake_of): map T::AccountId => BalanceOf<T>;

		/// The present candidate list.
		pub Candidates get(candidates): Vec<T::AccountId>;
		/// Current number of active candidates.
		pub CandidateCount get(candidate_count): u32;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;

		const CandidacyBond: BalanceOf<T> = T::CandidacyBond::get();
		const VotingBond: BalanceOf<T> = T::VotingBond::get();

		/// Vote for a set of candidates for the upcoming round of election.
		///
		/// The `votes` should:
		///   - not be empty.
		///   - not be less than the number of candidates.
		///
		/// `who` cannot be an old voter who has not yet called [`remove_voter`].
		///
		/// Upon voting, the entire balance of `who` is locked and a bond amount is reserved.
		#[weight = SimpleDispatchInfo::FixedNormal(750_000)]
		fn vote(origin, votes: Vec<T::AccountId>) -> Result {
			let who = ensure_signed(origin)?;

			// TODO: use decode_len #3071.
			let candidates = Self::candidates();
			ensure!(!candidates.is_empty(), "number of candidates cannot be zero");
			ensure!(candidates.len() >= votes.len(), "cannot vote more than candidates");

			ensure!(!votes.is_empty(), "must vote for at least one candidate.");
			ensure!(!Self::is_old_voter(&who), "must first remove self as voter and re-submit");

			if !Self::is_current_voter(&who) {
				// Amount to be locked up.
				let locked_balance = T::Currency::total_balance(&who);

				// lock and reserve
				T::Currency::reserve(&who, T::VotingBond::get())
					.map_err(|_| "voter can not pay voting bond")?;
				T::Currency::set_lock(
					MODULE_ID,
					&who,
					locked_balance,
					T::BlockNumber::max_value(),
					WithdrawReasons::except(WithdrawReason::TransactionPayment),
				);
				<StakeOf<T>>::insert(&who, locked_balance);
			}

			let now = Self::election_rounds();
			<VotesOf<T>>::insert(&who, (votes, now));
			Ok(())
		}

		/// Remove `origin` as a voter. One can use this to
		///   1. _undo_ their votes before the election has started.
		///   2. Remove their lock and unreserve the bond after an election round.
		#[weight = SimpleDispatchInfo::FixedNormal(500_000)]
		fn remove_voter(origin) {
			let who = ensure_signed(origin)?;

			ensure!(
				Self::is_current_voter(&who) || <StakeOf<T>>::exists(&who),
				"should be a current/old voter"
			);

			// remove storage.
			<VotesOf<T>>::remove(&who);
			<StakeOf<T>>::remove(&who);

			// unreserve the bond and remove.
			T::Currency::unreserve(&who, T::VotingBond::get());
			T::Currency::remove_lock(MODULE_ID, &who);
		}

		/// Submit oneself for candidacy.
		///
		/// A candidate will either:
		///   - Lose at the end of the term and gets their bond unreserved
		///   - Win and become a member. Members will get their bond back at the end ot their term.
		#[weight = SimpleDispatchInfo::FixedNormal(1_000_000)]
		fn submit_candidacy(origin) {
			let who = ensure_signed(origin)?;

			ensure!(!Self::is_candidate(&who), "duplicate candidate submission");

			T::Currency::reserve(&who, T::CandidacyBond::get())
				.map_err(|_| "candidate has not enough funds")?;

			<Candidates<T>>::append(&[who.clone()])
				.unwrap_or_else(|_| <Candidates<T>>::mutate(|c| c.push(who.clone())));
			CandidateCount::mutate(|c| *c += 1);
		}

		/// Set the desired member count; if lower than the current count, then seats will not be up
		/// election when they expire. If more, then a new vote will be started if one is not
		/// already in progress.
		#[weight = SimpleDispatchInfo::FixedOperational(10_000)]
		fn set_desired_seats(origin, #[compact] count: u32) {
			ensure_root(origin)?;
			DesiredSeats::put(count);
		}

		/// Remove a particular member from the set. This is effective immediately.
		///
		/// Note: A tally should happen instantly (if not already in a presentation
		/// period) to fill the seat if removal means that the desired members are not met.
		#[weight = SimpleDispatchInfo::FixedOperational(10_000)]
		fn remove_member(origin, who: <T::Lookup as StaticLookup>::Source) {
			ensure_root(origin)?;
			let who = T::Lookup::lookup(who)?;

			if Self::is_candidate(&who) {
				let members = Self::members();
				let new_members: Vec<T::AccountId> = members
					.into_iter()
					.filter(|i| *i != who)
					.collect();
				<Members<T>>::put(new_members.clone());
				T::Currency::unreserve(&who, T::CandidacyBond::get());
				T::ChangeMembers::change_members(&[], &[who], new_members);
			}
		}

		/// Set the presentation duration. If there is current a vote being presented for, will
		/// invoke `finalize_vote`.
		#[weight = SimpleDispatchInfo::FixedOperational(10_000)]
		fn set_term_duration(origin, #[compact] count: T::BlockNumber) {
			ensure_root(origin)?;
			<TermDuration<T>>::put(count);
		}

		fn on_initialize(n: T::BlockNumber) {
			if let Err(e) = Self::end_block(n) {
				runtime_io::print("Guru meditation");
				runtime_io::print(e);
			}
		}
	}
}

decl_event!(
	pub enum Event<T> where <T as system::Trait>::AccountId {
		/// A new term with new members.
		NewTerm(Vec<AccountId>),
		/// No candidates were elected for this round.
		EmptyCouncil(),
	}
);

impl<T: Trait> Module<T> {
	/// Check if `who` is a candidate.
	fn is_candidate(who: &T::AccountId) -> bool {
		Self::candidates().iter().find(|c| *c == who).is_some()
	}


	/// Check if `who` is a voter in the ongoing round.
	fn is_current_voter(who: &T::AccountId) -> bool {
		let now = Self::election_rounds();
		Self::votes_of(who).1 == now && <StakeOf<T>>::exists(who)
	}

	/// Check if `who` was a voter who has not yet called `remove_voter`.
	fn is_old_voter(who: &T::AccountId) -> bool {
		let now = Self::election_rounds();
		Self::votes_of(who).1 < now && <StakeOf<T>>::exists(who)
	}

	/// The locked stake of a voter.
	fn locked_stake_of(who: &T::AccountId) -> BalanceOf<T> {
		if Self::is_current_voter(who) {
			Self::stake_of(who)
		} else {
			Zero::zero()
		}
	}

	/// Check there's nothing to do this block.
	///
	/// Runs phragmen election and cleans all the previous candidate state. The voter state is NOT
	/// cleaned and voters must themselves submit a transaction to clean it.
	fn end_block(block_number: T::BlockNumber) -> Result {
		if (block_number % Self::term_duration()).is_zero() {
			use sr_primitives::phragmen;
			let seats = Self::desired_seats() as usize;
			let candidates = Self::candidates();
			let current_round = Self::election_rounds();
			let voters_and_votes = <VotesOf<T>>::enumerate()
				.filter_map(|(v, i)| if i.1 == current_round { Some((v, i.0)) } else { None } )
				.collect::<Vec<(T::AccountId, Vec<T::AccountId>)>>();

			let maybe_new_members = phragmen::elect::<_, _, _, T::CurrencyToVote>(
				seats,
				false,
				0,
				candidates.clone(),
				voters_and_votes,
				Self::locked_stake_of
			);

			let old_members = <Members<T>>::take();
			if let Some((new_members_with_approval, _)) = maybe_new_members {
				let new_members = new_members_with_approval
					.into_iter()
					.filter_map(|(m, a)| if !a.is_zero() { Some(m) } else { None } )
					.collect::<Vec<T::AccountId>>();
				<Members<T>>::put(new_members.clone());

				// return bond to losers.
				let losers = candidates.into_iter()
					.filter(|c| new_members.iter().find(|v| *v == c).is_none())
					.collect::<Vec<T::AccountId>>();
				losers.iter().for_each(|c| { T::Currency::unreserve(&c, T::CandidacyBond::get()); });

				T::ChangeMembers::change_members(
					&new_members,
					&old_members,
					new_members.clone(),
				);
				Self::deposit_event(RawEvent::NewTerm(new_members));
			} else {
				Self::deposit_event(RawEvent::EmptyCouncil());
			}

			// clean candidates
			// unreserve the bond of all the outgoings.
			old_members.iter().for_each(|m| {
				T::Currency::unreserve(&m, T::CandidacyBond::get());
			});
			<Candidates<T>>::kill();
			CandidateCount::put(0);

			ElectionRounds::mutate(|v| *v += 1);
		}
		Ok(())
	}

}

#[cfg(test)]
mod tests {
	use super::*;
	use std::cell::RefCell;
	use srml_support::{assert_ok, assert_noop, parameter_types, assert_eq_uvec};
	use runtime_io::with_externalities;
	use primitives::{H256, Blake2Hasher};
	use sr_primitives::{Perbill, testing::Header, BuildStorage,
		traits::{BlakeTwo256, IdentityLookup, Block as BlockT}
	};
	use crate as elections;

	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: u32 = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Call = ();
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = Event;
		type WeightMultiplierUpdate = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
	}
	parameter_types! {
		pub const ExistentialDeposit: u64 = 0;
		pub const TransferFee: u64 = 0;
		pub const CreationFee: u64 = 0;
		pub const TransactionBaseFee: u64 = 0;
		pub const TransactionByteFee: u64 = 0;
	}
	impl balances::Trait for Test {
		type Balance = u64;
		type OnNewAccount = ();
		type OnFreeBalanceZero = ();
		type Event = Event;
		type TransactionPayment = ();
		type TransferPayment = ();
		type DustRemoval = ();
		type ExistentialDeposit = ExistentialDeposit;
		type TransferFee = TransferFee;
		type CreationFee = CreationFee;
		type TransactionBaseFee = TransactionBaseFee;
		type TransactionByteFee = TransactionByteFee;
		type WeightToFee = ();
	}
	parameter_types! {
		pub const CandidacyBond: u64 = 3;
	}

	thread_local! {
		static VOTER_BOND: RefCell<u64> = RefCell::new(2);
		static MEMBERS: RefCell<Vec<u64>> = RefCell::new(vec![]);
	}

	pub struct VotingBond;
	impl Get<u64> for VotingBond {
		fn get() -> u64 { VOTER_BOND.with(|v| *v.borrow()) }
	}

	pub struct TestChangeMembers;
	impl ChangeMembers<u64> for TestChangeMembers {
		fn change_members_sorted(_: &[u64], _: &[u64], _: &[u64]) {}
	}

	/// Simple structure that exposes how u64 currency can be represented as... u64.
	pub struct CurrencyToVoteHandler;
	impl Convert<u64, u64> for CurrencyToVoteHandler {
		fn convert(x: u64) -> u64 { x }
	}
	impl Convert<u128, u64> for CurrencyToVoteHandler {
		fn convert(x: u128) -> u64 {
			x as u64
		}
	}

	impl Trait for Test {
		type Event = Event;
		type Currency = Balances;
		type CurrencyToVote = CurrencyToVoteHandler;
		type ChangeMembers = TestChangeMembers;
		type CandidacyBond = CandidacyBond;
		type VotingBond = VotingBond;
	}

	pub type Block = sr_primitives::generic::Block<Header, UncheckedExtrinsic>;
	pub type UncheckedExtrinsic = sr_primitives::generic::UncheckedExtrinsic<u32, u64, Call, ()>;

	srml_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic
		{
			System: system::{Module, Call, Event},
			Balances: balances::{Module, Call, Event<T>, Config<T>},
			Elections: elections::{Module, Call, Event<T>, Config<T>},
		}
	);

	pub struct ExtBuilder {
		balance_factor: u64,
		voter_bond: u64,
	}

	impl Default for ExtBuilder {
		fn default() -> Self {
			Self {
				balance_factor: 1,
				voter_bond: 2,
			}
		}
	}

	impl ExtBuilder {
		pub fn voter_bond(mut self, fee: u64) -> Self {
			self.voter_bond = fee;
			self
		}
		pub fn build(self) -> runtime_io::TestExternalities<Blake2Hasher> {
			VOTER_BOND.with(|v| *v.borrow_mut() = self.voter_bond);
			GenesisConfig {
				balances: Some(balances::GenesisConfig::<Test>{
					balances: vec![
						(1, 10 * self.balance_factor),
						(2, 20 * self.balance_factor),
						(3, 30 * self.balance_factor),
						(4, 40 * self.balance_factor),
						(5, 50 * self.balance_factor),
						(6, 60 * self.balance_factor)
					],
					vesting: vec![],
				}),
				elections: Some(elections::GenesisConfig::<Test>{
					members: vec![],
					desired_seats: 2,
					term_duration: 5,
				}),
			}.build_storage().unwrap().into()
		}
	}

	fn current_voters() -> Vec<u64> {
		<VotesOf<Test>>::enumerate()
			.filter(|(v, _)| Elections::is_current_voter(v))
			.map(|(v, _)| v).collect::<Vec<u64>>()
	}

	fn all_voters() -> Vec<u64> {
		<VotesOf<Test>>::enumerate().map(|(v, _)| v).collect::<Vec<u64>>()
	}

	#[test]
	fn params_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);
			assert_eq!(Elections::election_rounds(), 0);
			assert_eq!(Elections::term_duration(), 5);
			assert_eq!(Elections::desired_seats(), 2);

			assert_eq!(Elections::members(), vec![]);

			assert_eq!(Elections::candidates(), vec![]);
			assert_eq!(Elections::candidate_count(), 0);
			assert_eq!(Elections::is_candidate(&1), false);

			assert_eq!(current_voters(), vec![]);
			assert_eq!(all_voters(), vec![]);
			assert_eq!(Elections::votes_of(&1).0, vec![]);
		});
	}

	#[test]
	fn simple_candidate_submission_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_eq!(Elections::candidates(), Vec::<u64>::new());
			assert_eq!(Elections::is_candidate(&1), false);
			assert_eq!(Elections::is_candidate(&2), false);

			assert_eq!(Balances::free_balance(&1), 10);
			assert_ok!(Elections::submit_candidacy(Origin::signed(1)));
			assert_eq!(Balances::free_balance(&1), 10 - 3);
			assert_eq!(Balances::reserved_balance(&1), 3);
			assert_eq!(Elections::candidates(), vec![1]);
			assert_eq!(Elections::is_candidate(&1), true);
			assert_eq!(Elections::is_candidate(&2), false);

			assert_eq!(Balances::free_balance(&2), 20);
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));
			assert_eq!(Balances::free_balance(&2), 20 - 3);
			assert_eq!(Elections::candidates(), vec![1, 2]);
			assert_eq!(Elections::is_candidate(&1), true);
			assert_eq!(Elections::is_candidate(&2), true);
		});
	}

	#[test]
	fn dupe_candidate_submission_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_eq!(Elections::candidates(), Vec::<u64>::new());
			assert_ok!(Elections::submit_candidacy(Origin::signed(1)));
			assert_eq!(Elections::candidates(), vec![1]);
			assert_noop!(
				Elections::submit_candidacy(Origin::signed(1)),
				"duplicate candidate submission"
			);
		});
	}

	#[test]
	fn poor_candidate_submission_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_eq!(Elections::candidates(), Vec::<u64>::new());
			assert_noop!(
				Elections::submit_candidacy(Origin::signed(7)),
				"candidate has not enough funds"
			);
		});
	}

	#[test]
	fn vote_locks_entire_balance() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_eq!(Elections::candidates(), Vec::<u64>::new());
			assert_eq!(Balances::free_balance(&2), 20);

			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::vote(Origin::signed(2), vec![5]));

			assert_eq!(Balances::free_balance(&2), 20 - 2);
			assert_noop!(
				Balances::reserve(&2, 1),
				"account liquidity restrictions prevent withdrawal"
			); // locked.
		});
	}

	#[test]
	fn can_update_votes_in_current_round() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_eq!(Balances::free_balance(&2), 20);
			assert_eq!(Balances::reserved_balance(&2), 0);

			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::vote(Origin::signed(2), vec![5]));

			assert_eq!(Balances::free_balance(&2), 20 - 2);
			assert_eq!(Balances::reserved_balance(&2), 2);
			assert_eq!(Elections::stake_of(2), 20);

			// can update; same stake; same lock and reserve.
			assert_ok!(Elections::vote(Origin::signed(2), vec![5, 4]));
			assert_eq!(Balances::reserved_balance(&2), 2);
			assert_eq!(Elections::stake_of(2), 20);
		});
	}

	#[test]
	fn cannot_vote_for_no_candidate() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_noop!(
				Elections::vote(Origin::signed(2), vec![]),
				"number of candidates cannot be zero"
			);
		});
	}

	#[test]
	fn cannot_vote_for_more_than_candidates() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			assert_noop!(
				Elections::vote(Origin::signed(2), vec![10, 20, 30]),
				"cannot vote more than candidates"
			);
		});
	}

	#[test]
	fn remove_voter_should_work() {
		with_externalities(&mut ExtBuilder::default().voter_bond(8).build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![5]));
			assert_ok!(Elections::vote(Origin::signed(3), vec![5]));

			assert_eq_uvec!(all_voters(), vec![2, 3]);
			assert_eq_uvec!(all_voters(), current_voters());
			assert_eq!(Elections::stake_of(2), 20);
			assert_eq!(Elections::stake_of(3), 30);
			assert_eq!(Elections::votes_of(2), (vec![5], 0));
			assert_eq!(Elections::votes_of(3), (vec![5], 0));

			assert_ok!(Elections::remove_voter(Origin::signed(2)));

			assert_eq!(all_voters(), vec![3]);
			assert_eq!(current_voters(), vec![3]);
			assert_eq!(Elections::votes_of(2), (vec![], 0));
			assert_eq!(Elections::stake_of(2), 0);

			assert_eq!(Balances::free_balance(&2), 20);
			assert_eq!(Balances::reserved_balance(&2), 0);
			assert_ok!(Balances::reserve(&2, 10)); // no locks
		});
	}

	#[test]
	fn non_voter_remove_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_noop!(
				Elections::remove_voter(Origin::signed(3)),
				"should be a current/old voter"
			);
		});
	}

	#[test]
	fn dupe_remove_should_fail() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::vote(Origin::signed(2), vec![5]));

			assert_ok!(Elections::remove_voter(Origin::signed(2)));
			assert_eq!(all_voters(), vec![]);
			assert_eq!(current_voters(), vec![]);

			assert_noop!(
				Elections::remove_voter(Origin::signed(2)),
				"should be a current/old voter"
			);
		});
	}

	#[test]
	fn removed_voter_should_not_be_counted() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(5), vec![5]));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4]));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3]));

			assert_ok!(Elections::remove_voter(Origin::signed(4)));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq_uvec!(Elections::members(), vec![3, 5]);
		});
	}


	#[test]
	fn old_voter_should_not_be_counted() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(3), vec![3]));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4]));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5]));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![5, 4]);
			assert_eq!(Elections::election_rounds(), 1);

			// meanwhile, no one cares to become a candidate again.
			System::set_block_number(10);
			assert_ok!(Elections::end_block(System::block_number()));
			// none of the votes matter anymore
			assert_eq!(Elections::members(), vec![]);
			assert_eq!(Elections::election_rounds(), 2);
			assert_eq!(current_voters(), vec![]);
			assert_eq_uvec!(all_voters(), vec![5, 4, 3]);
		});
	}

	#[test]
	fn voting_rounds_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![5]));
			assert_ok!(Elections::vote(Origin::signed(3), vec![5]));

			assert_eq_uvec!(current_voters(), vec![2, 3]);
			assert_eq!(Elections::votes_of(2).0, vec![5]);
			assert_eq!(Elections::votes_of(3).0, vec![5]);

			assert_eq!(Elections::candidates(), vec![5]);
			assert_eq!(Elections::candidate_count(), 1);

			assert_eq!(Elections::election_rounds(), 0);

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(current_voters(), vec![]);
			assert_eq_uvec!(all_voters(), vec![2, 3]);

			assert_eq!(Elections::candidates(), vec![]);
			assert_eq!(Elections::candidate_count(), 0);

			assert_eq!(Elections::election_rounds(), 1);

			assert_eq!(Elections::members(), vec![5]);
		});
	}

	#[test]
	fn only_desired_seats_are_chosen() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![2]));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3]));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4]));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5]));
;
			assert_eq!(Elections::candidate_count(), 4);

			assert_eq!(Elections::election_rounds(), 0);

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::candidates(), vec![]);
			assert_eq!(Elections::candidate_count(), 0);

			assert_eq!(Elections::election_rounds(), 1);

			assert_eq!(Elections::members(), vec![5, 4]);
		});
	}

	#[test]
	fn seats_should_be_released() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![3]));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3]));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4]));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5]));
;
			assert_eq!(Elections::candidate_count(), 3);

			assert_eq!(Elections::election_rounds(), 0);

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members(), vec![5, 3]);
			assert_eq!(Elections::election_rounds(), 1);

			// meanwhile, no one cares to become a candidate again.
			System::set_block_number(10);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members(), vec![]);
			assert_eq!(Elections::election_rounds(), 2);
		});
	}

	#[test]
	fn outgoing_will_get_the_bond_back() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(3), vec![3]));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4]));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5]));

			assert_eq!(Balances::reserved_balance(&5), 3 + 2);

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![5, 4]);
			assert_eq!(Elections::election_rounds(), 1);
			assert_eq!(Balances::reserved_balance(&5), 3 + 2);

			// meanwhile, no one cares to become a candidate again.
			System::set_block_number(10);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members(), vec![]);
			assert_eq!(Elections::election_rounds(), 2);
			assert_eq!(Balances::reserved_balance(&5), 2);
			assert_eq!(Balances::reserved_balance(&4), 2);
		});
	}

	#[test]
	fn losers_will_get_the_bond_back_after_remove() {
		with_externalities(&mut ExtBuilder::default().voter_bond(2).build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(4), vec![5]));

			assert_eq!(Balances::reserved_balance(&5), 3);
			assert_eq!(Balances::reserved_balance(&3), 3);

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![5]);

			assert_eq!(Balances::reserved_balance(&5), 3); // winner
			assert_eq!(Balances::reserved_balance(&3), 0); // loser
		});
	}

	#[test]
	fn invalid_votes_are_moot() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(3), vec![3]));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4]));
			assert_ok!(Elections::vote(Origin::signed(5), vec![10]));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq_uvec!(Elections::members(), vec![3, 4]);
			assert_eq!(Elections::election_rounds(), 1);
		});
	}

	#[test]
	fn consequent_vote_without_remove_should_fail() {
		with_externalities(&mut ExtBuilder::default().voter_bond(2).build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::vote(Origin::signed(3), vec![5]));

			assert_eq!(Balances::reserved_balance(&5), 3);
			assert_eq!(Balances::reserved_balance(&3), 2);

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![5]);
			assert_eq!(Elections::election_rounds(), 1);
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));

			assert_eq!(Balances::reserved_balance(&5), 3);
			assert_eq!(Balances::reserved_balance(&2), 3);
			assert_eq!(Balances::reserved_balance(&3), 2);

			assert_noop!(
				Elections::vote(Origin::signed(3), vec![2]),
				"must first remove self as voter and re-submit"
			);
			assert_ok!(Elections::remove_voter(Origin::signed(3)));
			assert_eq!(Balances::reserved_balance(&3), 0);

			assert_ok!(Elections::vote(Origin::signed(3), vec![2]));

			System::set_block_number(10);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members(), vec![2]);
			assert_eq!(Balances::reserved_balance(&5), 0);
		})
	}

	#[test]
	fn candidate_stake_does_not_matter() {
		with_externalities(&mut ExtBuilder::default().voter_bond(2).build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![]);
		})
	}
}
