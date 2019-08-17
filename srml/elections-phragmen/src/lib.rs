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

//! # Phragmen Election Module.
//!
//! An election module based on sequential phragmen.
//!
//! ### Term and Round
//!
//! The election happens in _rounds_: every `N` blocks, all previous members are retired and a new
//! set is elected (which may or may not have an intersection with the previous set). Each round
//! lasts for some number of blocks defined by `TermDuration` storage item. The works _term_ and
//! _round_ can be used interchangeably in this context.
//!
//! `TermDuration` might change during a round. This can shorten or extend the length of the round.
//! The next election round's block number is never stored but rather always checked on the fly.
//! Based on the current block height and `TermDuration`, `BlockNumber % TermDuration == 0` will
//! always trigger a new election round.
//!
//! ### Voting
//!
//! Voters can vote for as many of the candidates by providing a list of account ids. Invalid votes
//! (voting for non-candidates) are ignored during election. Yet, a voter _might_ vote for a
//! future candidate. Voters reserve a bond as they vote. Each vote defines a `value`. This amount
//! is locked from the account of the voter and indicated the weight of the vote. Voters can update
//! their votes at any time by calling `vote()` again. This keeps the bond untouched but can
//! optionally change the locked `value`. After a round, votes are kept and might still be valid
//! for further rounds. A voter is responsible to call `remove_voter` upon once they are done to
//! have their bond back and remove the lock.
//!
//! ### Candidacy and Members
//!
//! Candidates also reserve a bond as they submit candidacy. A candidate cannot take their candidacy
//! back. A candidate can end up in one of the below situations:
//!   - **Winner**: A winner is kept as a _member_. They must still have a bond in reserve
//!		and they are automatically counted as a candidate for the next election.
//!   - **Runner-up**: Runner ups are the best candidates immediately after the winners. The number
//!		of runner-ups to keep is configurable. Runner-ups serve one major role: if a member is
//!		forcefully removed, the next best runner-up is chosen as a replacement. If not, a new
//! 	election is triggered.
//!   - **Loser**: Any of the candidate who are not a winner are left as losers. A loser might be an
//! 	_outgoing member_, meaning that they are an active member who failed to keep their spot. In
//! 	this case, the outgoing member will get their bond back. Otherwise, the bond is slashed from
//! 	the loser candidate.
//!
//! Note that with the members being the default candidates for the next round and votes
//! persisting in storage, the election system is entirely stable given no further input. This means
//! that if the system has a particular set of candidates `C` and voters `V` that lead to a
//! set of members `M` being elected, as long as `V` and `C` don't remove their candidacy and votes,
//! `M` will keep being re-elected at the end of each round.
//!
//! ### Module Information
//!
//! - [`election_phragmen::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)

#![cfg_attr(not(feature = "std"), no_std)]

use sr_primitives::traits::{Zero, StaticLookup, Bounded, Convert};
use sr_primitives::weights::SimpleDispatchInfo;
use sr_primitives::phragmen;
use srml_support::{StorageValue, StorageMap, EnumerableStorageMap, decl_storage, decl_event, ensure,
	decl_module, dispatch,
	traits::{Currency, Get, LockableCurrency, LockIdentifier, ReservableCurrency, WithdrawReasons,
		ChangeMembers, OnUnbalanced,
	}
};
use system::{self, ensure_signed, ensure_root};

const MODULE_ID: LockIdentifier = *b"phrelect";

/// The maximum votes allowed per voter.
pub const MAXIMUM_VOTE: usize = 16;

type BalanceOf<T> = <<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;
type NegativeImbalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::NegativeImbalance;

pub trait Trait: system::Trait {
	/// The overarching event type.c
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

	/// Handler for the unbalanced reduction when a candidate has lost (and is not a runner-up)
	type LoserCandidate: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// Handler for the unbalanced reduction when a member has been kicked.
	type KickedMember: OnUnbalanced<NegativeImbalanceOf<Self>>;
}

decl_storage! {
	trait Store for Module<T: Trait> as PhragmenElection {
		// ---- parameters
		/// Number of members to elect.
		pub DesiredMembers get(desired_members) config(): u32;
		/// Number of runner-ups to store.
		pub DesiredRunnerUps get(desired_runner_ups) config(): u32;
		/// How long each seat is kept. This defined the next block number at which an election
		/// round will happen.
		pub TermDuration get(term_duration) config(): T::BlockNumber;

		// ---- State
		/// The current elected membership. Sorted based on account id (low to high).
		pub Members get(members) config(): Vec<T::AccountId>;
		/// The current runner-ups. Sorted based on **stake** (low to high).
		pub RunnerUps get(runner_ups): Vec<T::AccountId>;
		/// The total number of vote rounds that have happened, exclusive of the upcoming one.
		pub ElectionRounds get(election_rounds): u32 = Zero::zero();

		/// Votes of a particular voter, with the round index of the votes.
		pub VotesOf get(votes_of): linked_map T::AccountId => (Vec<T::AccountId>, u32);
		/// Locked stake of a voter.
		pub StakeOf get(stake_of): map T::AccountId => BalanceOf<T>;

		/// The present candidate list. Sorted based on account id.
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
		///   - be less than the number of candidates.
		///
		/// Upon voting, `value` units of `who`'s balance is locked and a bond amount is reserved.
		/// It is the responsibility of the caller to not place all of their balance into the lock
		/// and keep some for further transactions.
		#[weight = SimpleDispatchInfo::FixedNormal(500_000)]
		fn vote(origin, votes: Vec<T::AccountId>, value: BalanceOf<T>) {
			let who = ensure_signed(origin)?;

			// TODO: use decode_len #3071 and remove candidate_count.
			let candidates_count = Self::candidate_count();
			let allowed_votes = candidates_count as usize + Self::members().len();
			ensure!(!allowed_votes.is_zero(), "number of candidates cannot be zero");
			ensure!(votes.len() <= allowed_votes, "cannot vote more than candidates");
			ensure!(votes.len() <= MAXIMUM_VOTE, "cannot vote more than maximum allowed");

			ensure!(!votes.is_empty(), "must vote for at least one candidate.");
			ensure!(value > T::Currency::minimum_balance(), "cannot vote with stake less than min balance");

			if !Self::is_voter(&who) {
				// first time voter. Reserve bond.
				T::Currency::reserve(&who, T::VotingBond::get())
					.map_err(|_| "voter can not pay voting bond")?;
			}
			// Amount to be locked up.
			let locked_balance = value.min(T::Currency::total_balance(&who));

			// lock
			T::Currency::set_lock(
				MODULE_ID,
				&who,
				locked_balance,
				T::BlockNumber::max_value(),
				WithdrawReasons::all(),
			);
			<StakeOf<T>>::insert(&who, locked_balance);

			let now = Self::election_rounds();
			<VotesOf<T>>::insert(&who, (votes, now));
		}

		/// Remove `origin` as a voter. This removes the lock and returns the bond.
		#[weight = SimpleDispatchInfo::FixedNormal(500_000)]
		fn remove_voter(origin) {
			let who = ensure_signed(origin)?;

			ensure!(Self::is_voter(&who), "must be a voter");

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
		///   - Lose at the end of the term and get slashed.
		///   - Win and become a member. Members will eventually get their stash back.
		///   - Become a runner-up. Runner-ups are reserved members in case one gets forcefully
		///     removed.
		#[weight = SimpleDispatchInfo::FixedNormal(500_000)]
		fn submit_candidacy(origin) {
			let who = ensure_signed(origin)?;

			let is_candidate = Self::is_candidate(&who);
			ensure!(!is_candidate.is_ok(), "duplicate candidate submission");
			ensure!(
				Self::members().binary_search(&who).is_err(),
				"member cannot re-submit candidacy"
			);
			// assured to be an error, error always contains the index.
			let index = is_candidate.unwrap_err();

			T::Currency::reserve(&who, T::CandidacyBond::get())
				.map_err(|_| "candidate has not enough funds")?;

			<Candidates<T>>::mutate(|c| c.insert(index, who));
			CandidateCount::mutate(|c| *c += 1);
		}

		/// Set the desired member count. Changes will be effective at the beginning of next round.
		#[weight = SimpleDispatchInfo::FixedOperational(10_000)]
		fn set_desired_member_count(origin, #[compact] count: u32) {
			ensure_root(origin)?;
			DesiredMembers::put(count);
		}

		/// Remove a particular member from the set. This is effective immediately.
		///
		/// If a runner-up si available, then the best runner-up will be removed and replaces the
		/// outgoing member. Otherwise, a new phragmen round is started.
		///
		/// Note that this does not affect the designated block number of the next election.
		#[weight = SimpleDispatchInfo::FixedOperational(2_000_000)]
		fn remove_member(origin, who: <T::Lookup as StaticLookup>::Source) {
			ensure_root(origin)?;
			let who = T::Lookup::lookup(who)?;

			let mut members = Self::members();
			if let Ok(index) = members.binary_search(&who) {
				// remove, slash, emit event.
				members.remove(index);
				let (imbalance, _) = T::Currency::slash_reserved(&who, T::CandidacyBond::get());
				T::KickedMember::on_unbalanced(imbalance);
				Self::deposit_event(RawEvent::MemberKicked(who.clone()));

				let mut runner_ups = Self::runner_ups();
				if let Some(replacement) = runner_ups.pop() {
					// replace the outgoing with the best runner up.
					if let Err(index) = members.binary_search(&replacement) {
						members.insert(index, replacement.clone());
						ElectionRounds::mutate(|v| *v += 1);
						T::ChangeMembers::change_members_sorted(&[replacement], &[who], &members);
					}
					// else it would mean that the runner up was already a candidate. This cannot
					// happen. If it does, not much that we can do about it.

					<Members<T>>::put(members);
					<RunnerUps<T>>::put(runner_ups);
				} else {
					// trigger a new phragmen. grab a cup of coffee. This might take a while.
					<Members<T>>::put(members);
					Self::do_phragmen();
				}
			}
		}

		/// Set the duration of each term. This will affect the next election's block number.
		#[weight = SimpleDispatchInfo::FixedOperational(10_000)]
		fn set_term_duration(origin, #[compact] count: T::BlockNumber) {
			ensure_root(origin)?;
			<TermDuration<T>>::put(count);
		}

		/// What to do at the end of each block. Checks if an election needs to happen or not.
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
		/// A new term with new members. This indicates that enough candidates existed, not that
		/// enough have has been elected. The inner value must be examined for this purpose.
		NewTerm(Vec<AccountId>),
		/// No (or not enough) candidates existed for this round.
		EmptyTerm,
		/// A member has been removed. This should always be followed by either `NewTerm` ot
		/// `EmptyTerm`.
		MemberKicked(AccountId),
	}
);

impl<T: Trait> Module<T> {
	/// Check if `who` is a candidate. It returns the insert index if the element does not exists as
	/// an error.
	fn is_candidate(who: &T::AccountId) -> Result<(), usize> {
		Self::candidates().binary_search(who).map(|_| ())
	}

	/// Check if `who` is a voter. It may or may not be a _current_ one.
	fn is_voter(who: &T::AccountId) -> bool {
		<StakeOf<T>>::exists(who)
	}

	/// The locked stake of a voter.
	fn locked_stake_of(who: &T::AccountId) -> BalanceOf<T> {
		Self::stake_of(who)
	}

	/// Check there's nothing to do this block.
	///
	/// Runs phragmen election and cleans all the previous candidate state. The voter state is NOT
	/// cleaned and voters must themselves submit a transaction to retract.
	fn end_block(block_number: T::BlockNumber) -> dispatch::Result {
		if (block_number % Self::term_duration()).is_zero() {
			Self::do_phragmen();
		}
		Ok(())
	}

	/// Run the phragmen election with all required side processes and state updates.
	///
	/// Calls the appropriate `ChangeMembers` function variant internally.
	fn do_phragmen() {
		let desired_seats = Self::desired_members() as usize;
		let desired_runner_ups = Self::desired_runner_ups() as usize;
		let num_to_elect = desired_runner_ups + desired_seats;

		// current members are always a candidate for the next round as well.
		// this is guaranteed to not create any duplicates.
		let mut candidates = Self::candidates();
		candidates.append(&mut Self::members());
		let voters_and_votes = <VotesOf<T>>::enumerate()
			.map(|(v, i)| (v, i.0))
			.collect::<Vec<(T::AccountId, Vec<T::AccountId>)>>();
		let maybe_new_members = phragmen::elect::<_, _, _, T::CurrencyToVote>(
			num_to_elect,
			false,
			0,
			candidates.clone(),
			voters_and_votes,
			Self::locked_stake_of
		);

		let mut to_release_bond: Vec<T::AccountId> = Vec::with_capacity(desired_seats);
		let old_members = <Members<T>>::take();
		if let Some((mut new_members_with_approval, _)) = maybe_new_members {
			// sort based on stake to to split winner and runner ups.
			new_members_with_approval.sort_by_key(|x| x.1.clone());

			// filter out those who had literally no votes at all.
			let new_members_filtered = new_members_with_approval
				.into_iter()
				.filter_map(|(m, a)| if !a.is_zero() { Some(m) } else { None } )
				.collect::<Vec<T::AccountId>>();

			let mut new_members = new_members_filtered.iter()
				.rev()
				.take(desired_seats)
				.map(|m| m.clone())
				.collect::<Vec<T::AccountId>>();
			new_members.sort();
			<Members<T>>::put(new_members.clone());

			let mut allowed_runner_ups = new_members_filtered.len() - new_members.len();
			// defensive only. We should never have more leftover than desired runner ups.
			allowed_runner_ups = allowed_runner_ups.min(desired_runner_ups);
			let runner_ups = new_members_filtered.into_iter()
				.take(allowed_runner_ups)
				.collect::<Vec<T::AccountId>>();
			// should still be sorted by stake. Low to high.
			<RunnerUps<T>>::put(runner_ups.clone());

			// report. We don't know/compute the diff here, therefore we call `set_member`.
			let (incoming, outgoing) = T::ChangeMembers::compute_members_diff(&new_members, &old_members);
			T::ChangeMembers::change_members_sorted(
				&incoming,
				&outgoing.clone(),
				&new_members
			);

			to_release_bond = outgoing.to_vec();

			// NOTE: it is unfortunate that we have to re-sort new_members and runner ups
			// above, but their length is relatively small (few dozens at most) while it helps the
			// below search of `O(candidates)` quite faster.

			// Burn loser bond. All three lists are sorted. O(3LogN) ~ O(LogN)
			candidates.into_iter().for_each(|c| {
				// a candidate who's
				if new_members.binary_search(&c).is_err()  // now a member
					&& outgoing.binary_search(&c).is_err() // or was a member
					&& runner_ups.binary_search(&c).is_err() // or a runner-up
				{
					// should ge their bond slashed.
					let (imbalance, _) = T::Currency::slash_reserved(&c, T::CandidacyBond::get());
					T::LoserCandidate::on_unbalanced(imbalance);
				}
			});
			Self::deposit_event(RawEvent::NewTerm(new_members));
		} else {
			Self::deposit_event(RawEvent::EmptyTerm);
		}

		// unreserve the bond of all the outgoings.
		to_release_bond.iter().for_each(|m| {
			T::Currency::unreserve(&m, T::CandidacyBond::get());
		});

		// clean candidates.
		<Candidates<T>>::kill();
		CandidateCount::put(0);

		ElectionRounds::mutate(|v| *v += 1);
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
		pub const ExistentialDeposit: u64 = 1;
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
		static VOTING_BOND: RefCell<u64> = RefCell::new(2);
		static MEMBERS: RefCell<Vec<u64>> = RefCell::new(vec![]);
	}

	pub struct VotingBond;
	impl Get<u64> for VotingBond {
		fn get() -> u64 { VOTING_BOND.with(|v| *v.borrow()) }
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
		type LoserCandidate = ();
		type KickedMember = ();
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
		desired_runner_ups: u32,
	}

	impl Default for ExtBuilder {
		fn default() -> Self {
			Self {
				balance_factor: 1,
				voter_bond: 2,
				desired_runner_ups: 0,
			}
		}
	}

	impl ExtBuilder {
		pub fn voter_bond(mut self, fee: u64) -> Self {
			self.voter_bond = fee;
			self
		}
		pub fn desired_runner_ups(mut self, count: u32) -> Self {
			self.desired_runner_ups = count;
			self
		}
		pub fn build(self) -> runtime_io::TestExternalities<Blake2Hasher> {
			VOTING_BOND.with(|v| *v.borrow_mut() = self.voter_bond);
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
					desired_members: 2,
					desired_runner_ups: self.desired_runner_ups,
					term_duration: 5,
				}),
			}.build_storage().unwrap().into()
		}
	}

	fn all_voters() -> Vec<u64> {
		<VotesOf<Test>>::enumerate().map(|(v, _)| v).collect::<Vec<u64>>()
	}

	fn balances(who: &u64) -> (u64, u64) {
		(Balances::free_balance(who), Balances::reserved_balance(who))
	}

	#[test]
	fn params_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			System::set_block_number(1);
			assert_eq!(Elections::election_rounds(), 0);
			assert_eq!(Elections::term_duration(), 5);
			assert_eq!(Elections::desired_members(), 2);

			assert_eq!(Elections::members(), vec![]);
			assert_eq!(Elections::runner_ups(), vec![]);

			assert_eq!(Elections::candidates(), vec![]);
			assert_eq!(Elections::candidate_count(), 0);
			assert!(Elections::is_candidate(&1).is_err());

			assert_eq!(all_voters(), vec![]);
			assert_eq!(Elections::votes_of(&1).0, vec![]);
		});
	}

	#[test]
	fn simple_candidate_submission_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_eq!(Elections::candidates(), Vec::<u64>::new());
			assert!(Elections::is_candidate(&1).is_err());
			assert!(Elections::is_candidate(&2).is_err());

			assert_eq!(Balances::free_balance(&1), 10);
			assert_ok!(Elections::submit_candidacy(Origin::signed(1)));
			assert_eq!(Balances::free_balance(&1), 10 - 3);
			assert_eq!(Balances::reserved_balance(&1), 3);
			assert_eq!(Elections::candidates(), vec![1]);
			assert!(Elections::is_candidate(&1).is_ok());
			assert!(Elections::is_candidate(&2).is_err());

			assert_eq!(Balances::free_balance(&2), 20);
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));
			assert_eq!(Balances::free_balance(&2), 20 - 3);
			assert_eq!(Elections::candidates(), vec![1, 2]);
			assert!(Elections::is_candidate(&1).is_ok());
			assert!(Elections::is_candidate(&2).is_ok());
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
	fn member_candidacy_submission_should_not_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::vote(Origin::signed(2), vec![5], 20));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![5]);
			assert_eq!(Elections::runner_ups(), vec![]);
			assert_eq!(Elections::candidates(), vec![]);

			assert_noop!(
				Elections::submit_candidacy(Origin::signed(5)),
				"member cannot re-submit candidacy"
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
	fn vote_locks_balance() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_eq!(Elections::candidates(), Vec::<u64>::new());
			assert_eq!(Balances::free_balance(&2), 20);

			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::vote(Origin::signed(2), vec![5], 20));

			assert_eq!(Balances::free_balance(&2), 20 - 2);
			assert_noop!(
				Balances::reserve(&2, 1),
				"account liquidity restrictions prevent withdrawal"
			); // locked.
		});
	}

	#[test]
	fn can_update_votes() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_eq!(Balances::free_balance(&2), 20);
			assert_eq!(Balances::reserved_balance(&2), 0);

			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::vote(Origin::signed(2), vec![5], 20));

			assert_eq!(Balances::free_balance(&2), 20 - 2);
			assert_eq!(Balances::reserved_balance(&2), 2);
			assert_eq!(Elections::stake_of(2), 20);

			// can update; different stake; different lock and reserve.
			assert_ok!(Elections::vote(Origin::signed(2), vec![5, 4], 15));
			assert_eq!(Balances::reserved_balance(&2), 2);
			assert_eq!(Elections::stake_of(2), 15);
		});
	}

	#[test]
	fn cannot_vote_for_no_candidate() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_noop!(
				Elections::vote(Origin::signed(2), vec![], 20),
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
				Elections::vote(Origin::signed(2), vec![10, 20, 30], 20),
				"cannot vote more than candidates"
			);
		});
	}

	#[test]
	fn cannot_vote_for_less_than_ed() {
		with_externalities(&mut ExtBuilder::default().voter_bond(8).build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			assert_noop!(
				Elections::vote(Origin::signed(2), vec![4], 1),
				"cannot vote with stake less than min balance"
			);
		})
	}

	#[test]
	fn can_vote_for_more_than_total_balance_but_moot() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![4, 5], 30));
			// you can lie but won't get away with it.
			assert_eq!(Elections::stake_of(2), 20);
		});
	}

	#[test]
	fn remove_voter_should_work() {
		with_externalities(&mut ExtBuilder::default().voter_bond(8).build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![5], 20));
			assert_ok!(Elections::vote(Origin::signed(3), vec![5], 30));

			assert_eq_uvec!(all_voters(), vec![2, 3]);
			assert_eq!(Elections::stake_of(2), 20);
			assert_eq!(Elections::stake_of(3), 30);
			assert_eq!(Elections::votes_of(2), (vec![5], 0));
			assert_eq!(Elections::votes_of(3), (vec![5], 0));

			assert_ok!(Elections::remove_voter(Origin::signed(2)));

			assert_eq!(all_voters(), vec![3]);
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
			assert_noop!(Elections::remove_voter(Origin::signed(3)), "must be a voter");
		});
	}

	#[test]
	fn dupe_remove_should_fail() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::vote(Origin::signed(2), vec![5], 20));

			assert_ok!(Elections::remove_voter(Origin::signed(2)));
			assert_eq!(all_voters(), vec![]);

			assert_noop!(Elections::remove_voter(Origin::signed(2)), "must be a voter");
		});
	}

	#[test]
	fn removed_voter_should_not_be_counted() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));

			assert_ok!(Elections::remove_voter(Origin::signed(4)));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![3, 5]);
		});
	}

	#[test]
	fn simple_voting_rounds_should_work() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![5], 20));
			assert_ok!(Elections::vote(Origin::signed(3), vec![5], 30));

			assert_eq_uvec!(all_voters(), vec![2, 3]);

			assert_eq!(Elections::votes_of(2).0, vec![5]);
			assert_eq!(Elections::votes_of(3).0, vec![5]);

			assert_eq!(Elections::candidates(), vec![5]);
			assert_eq!(Elections::candidate_count(), 1);

			assert_eq!(Elections::election_rounds(), 0);

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![5]);
			assert_eq!(Elections::runner_ups(), vec![]);
			assert_eq_uvec!(all_voters(), vec![2, 3]);
			assert_eq!(Elections::candidates(), vec![]);
			assert_eq!(Elections::candidate_count(), 0);
			assert_eq!(Elections::election_rounds(), 1);
		});
	}

	#[test]
	fn old_voter_will_be_counted() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			// TODO: add to mopdule doc the tip that: one can always submit a candidacy and vote but not the other way around.
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));

			// This guys vote is pointless for this round.
			assert_ok!(Elections::vote(Origin::signed(3), vec![4], 30));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![5]);
			assert_eq!(Elections::election_rounds(), 1);

			// but now it has a valid target.
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			// meanwhile, no one cares to become a candidate again.
			System::set_block_number(10);
			assert_ok!(Elections::end_block(System::block_number()));
			// none of the votes matter anymore
			assert_eq!(Elections::members(), vec![4, 5]);
			assert_eq!(Elections::election_rounds(), 2);
			assert_eq_uvec!(all_voters(), vec![3, 5]);
		});
	}

	#[test]
	fn only_desired_seats_are_chosen() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![2], 20));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::election_rounds(), 1);
			assert_eq!(Elections::members(), vec![4, 5]);
		});
	}

	#[test]
	fn phragmen_should_not_self_vote() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::candidates(), vec![]);
			assert_eq!(Elections::election_rounds(), 1);
			assert_eq!(Elections::members(), vec![]);
			assert_eq!(Elections::runner_ups(), vec![]);
		});
	}

	#[test]
	fn runner_ups_should_be_kept() {
		with_externalities(&mut ExtBuilder::default().desired_runner_ups(1).build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![3], 20));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members(), vec![3, 5]);
			assert_eq!(Elections::runner_ups(), vec![4]);
			assert_eq!(Balances::reserved_balance(&4), 3 + 2);
			assert_eq!(Balances::free_balance(&4), 35);
		});
	}

	#[test]
	fn current_members_are_always_implicitly_next_candidate() {
		with_externalities(&mut ExtBuilder::default().desired_runner_ups(1).build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![2], 20));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![4, 5]);
			assert_eq!(Elections::runner_ups(), vec![3]);
			assert_eq!(Elections::election_rounds(), 1);

			// 4, 5 will persist as candidates despite not being in the list.
			assert_eq!(Elections::candidates(), vec![]);
			System::set_block_number(10);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![4, 5]);
			assert_eq!(Elections::runner_ups(), vec![]);
		});
	}

	#[test]
	fn election_state_is_uninterrupted() {
		with_externalities(&mut ExtBuilder::default().desired_runner_ups(1).build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));

			let check_at_block = |b: u32| {
				System::set_block_number(b.into());
				assert_ok!(Elections::end_block(System::block_number()));
				// we keep re-electing the same folks.
				assert_eq!(Elections::members(), vec![4, 5]);
				assert_eq!(Elections::election_rounds(), b / 5);
				assert_eq_uvec!(all_voters(), vec![5, 4]);
			};

			// this state will always persist when no further input is given.
			check_at_block(5);
			check_at_block(10);
			check_at_block(15);
			check_at_block(20);
		});
	}

	#[test]
	fn remove_members_triggers_election_if_no_runner_up() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));

			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members(), vec![4, 5]);
			assert_eq!(Elections::election_rounds(), 1);

			// a new candidate is also there waiting.
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));

			assert_ok!(Elections::remove_member(Origin::ROOT, 4));

			assert_eq!(balances(&4), (35, 2)); // slashed
			assert_eq!(Elections::election_rounds(), 2); // new election round
			assert_eq!(Elections::members(), vec![3, 5]); // new members
		});
	}

	#[test]
	fn unexpected_election_will_use_runner_ups_if_exists() {
		with_externalities(&mut ExtBuilder::default().desired_runner_ups(1).build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members(), vec![4, 5]);
			assert_eq!(Elections::runner_ups(), vec![3]);
			assert_eq!(Elections::election_rounds(), 1);

			assert_ok!(Elections::remove_member(Origin::ROOT, 4));

			assert_eq!(balances(&4), (35, 2)); // slashed
			assert_eq!(Elections::election_rounds(), 2); // new election round
			assert_eq!(Elections::members(), vec![3, 5]); // new members
			assert_eq!(Elections::runner_ups(), vec![]);
		});
	}

	#[test]
	fn runner_ups_are_sorted_by_stake() {
		with_externalities(&mut ExtBuilder::default().desired_runner_ups(3).build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(1)));

			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 9));
			assert_ok!(Elections::vote(Origin::signed(2), vec![2], 8));
			assert_ok!(Elections::vote(Origin::signed(1), vec![1], 10));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members(), vec![4, 5]);
			assert_eq!(Elections::runner_ups(), vec![2, 3, 1]);
			assert_eq!(Elections::election_rounds(), 1);
		});
	}

	#[test]
	fn seats_should_be_released_when_no_vote() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(2), vec![3], 20));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));

			assert_eq!(Elections::candidate_count(), 3);

			assert_eq!(Elections::election_rounds(), 0);

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members(), vec![3, 5]);
			assert_eq!(Elections::election_rounds(), 1);

			assert_ok!(Elections::remove_voter(Origin::signed(2)));
			assert_ok!(Elections::remove_voter(Origin::signed(3)));
			assert_ok!(Elections::remove_voter(Origin::signed(4)));
			assert_ok!(Elections::remove_voter(Origin::signed(5)));

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
			assert_eq!(Balances::total_balance(&5), 50);

			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_eq!(Balances::reserved_balance(&5), 3);

			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));
			assert_eq!(Balances::reserved_balance(&5), 3 + 2);

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members(), vec![5]);

			assert_ok!(Elections::remove_voter(Origin::signed(5)));
			assert_eq!(Balances::reserved_balance(&5), 3);
			// meanwhile, no one cares to become a candidate again.
			System::set_block_number(10);
			assert_ok!(Elections::end_block(System::block_number()));
			assert_eq!(Elections::members(), vec![]);

			assert_eq!(Balances::reserved_balance(&5), 0);
			assert_eq!(Balances::total_balance(&5), 50);
		});
	}

	#[test]
	fn losers_will_lose_the_bond() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(4), vec![5], 40));

			assert_eq!(Balances::reserved_balance(&5), 3);
			assert_eq!(Balances::reserved_balance(&3), 3);

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq!(Elections::members(), vec![5]);

			assert_eq!(Balances::reserved_balance(&5), 3); // winner

			assert_eq!(Balances::reserved_balance(&3), 0); // loser
			assert_eq!(Balances::free_balance(&3), 27); // loser
		});
	}

	#[test]
	fn incoming_outgoing_are_reported() {
		with_externalities(&mut ExtBuilder::default().desired_runner_ups(1).build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(5)));

			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![5], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_ok!(Elections::submit_candidacy(Origin::signed(1)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(2)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(5), vec![4], 8));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			assert_ok!(Elections::vote(Origin::signed(2), vec![2], 20));
			assert_ok!(Elections::vote(Origin::signed(1), vec![1], 10));

			System::set_block_number(10);
			assert_ok!(Elections::end_block(System::block_number()));

			// 3, 4 are new members, must still be bonded
			assert_eq!(Elections::members(), vec![3, 4]);
			assert_eq!(balances(&3), (25, 5));
			assert_eq!(balances(&4), (35, 5));

			// 2 is the runner up, must still be bonded
			assert_eq!(Elections::runner_ups(), vec![2]);
			assert_eq!(balances(&2), (15, 5));

			// 1 is a loser, will get slashed.
			assert_eq!(Balances::reserved_balance(&1), 2);
			assert_eq!(balances(&1), (5, 2));

			// 5 is an outgoing loser, it will get their bond back.
			assert_eq!(balances(&5), (48, 2));

			assert_eq!(System::events()[0].event, Event::elections(RawEvent::NewTerm(vec![4, 5])));
		})
	}

	#[test]
	fn invalid_votes_are_moot() {
		with_externalities(&mut ExtBuilder::default().build(), || {
			assert_ok!(Elections::submit_candidacy(Origin::signed(4)));
			assert_ok!(Elections::submit_candidacy(Origin::signed(3)));

			assert_ok!(Elections::vote(Origin::signed(3), vec![3], 30));
			assert_ok!(Elections::vote(Origin::signed(4), vec![4], 40));
			assert_ok!(Elections::vote(Origin::signed(5), vec![10], 50));

			System::set_block_number(5);
			assert_ok!(Elections::end_block(System::block_number()));

			assert_eq_uvec!(Elections::members(), vec![3, 4]);
			assert_eq!(Elections::election_rounds(), 1);
		});
	}
}
