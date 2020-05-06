// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Collective system: Members of a set of account IDs can make their collective feelings known
//! through dispatched calls from one of two specialized origins.
//!
//! The membership can be provided in one of two ways: either directly, using the Root-dispatchable
//! function `set_members`, or indirectly, through implementing the `ChangeMembers`.
//!
//! A "prime" member may be set allowing their vote to act as the default vote in case of any
//! abstentions after the voting period.
//!
//! Voting happens through motions comprising a proposal (i.e. a curried dispatchable) plus a
//! number of approvals required for it to pass and be called. Motions are open for members to
//! vote on for a minimum period given by `MotionDuration`. As soon as the needed number of
//! approvals is given, the motion is closed and executed. If the number of approvals is not reached
//! during the voting period, then `close` may be called by any account in order to force the end
//! the motion explicitly. If a prime member is defined then their vote is used in place of any
//! abstentions and the proposal is executed if there are enough approvals counting the new votes.
//!
//! If there are not, or if no prime is set, then the motion is dropped without being executed.

#![cfg_attr(not(feature = "std"), no_std)]
#![recursion_limit="128"]

use sp_std::{prelude::*, result};
use sp_core::u32_trait::Value as U32;
use sp_runtime::RuntimeDebug;
use sp_runtime::traits::Hash;
use frame_support::{
	dispatch::{Dispatchable, Parameter, DispatchError, DispatchResultWithPostInfo, PostDispatchInfo},
	codec::{Encode, Decode},
	traits::{Get, ChangeMembers, InitializeMembers, EnsureOrigin}, decl_module, decl_event,
	decl_storage, decl_error, ensure,
	weights::{DispatchClass, Weight, GetDispatchInfo},
};
use frame_system::{self as system, ensure_signed, ensure_root};

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;

/// Simple index type for proposal counting.
pub type ProposalIndex = u32;

/// A number of members.
///
/// This also serves as a number of voting members, and since for motions, each member may
/// vote exactly once, therefore also the number of votes for any given motion.
pub type MemberCount = u32;

pub trait Trait<I: Instance=DefaultInstance>: frame_system::Trait {
	/// The outer origin type.
	type Origin: From<RawOrigin<Self::AccountId, I>>;

	/// The outer call dispatch type.
	type Proposal: Parameter + Dispatchable<Origin=<Self as Trait<I>>::Origin, PostInfo=PostDispatchInfo> + From<frame_system::Call<Self>> + GetDispatchInfo;

	/// The outer event type.
	type Event: From<Event<Self, I>> + Into<<Self as frame_system::Trait>::Event>;

	/// The time-out for council motions.
	type MotionDuration: Get<Self::BlockNumber>;

	/// Maxmimum number of members allowed as part of the collective.
	type MaxMembers: Get<MemberCount>;

	/// Maximum number of proposals allowed to be active in parallel.
	type MaxProposals: Get<u32>;
}

/// Origin for the collective module.
#[derive(PartialEq, Eq, Clone, RuntimeDebug)]
pub enum RawOrigin<AccountId, I> {
	/// It has been condoned by a given number of members of the collective from a given total.
	Members(MemberCount, MemberCount),
	/// It has been condoned by a single member of the collective.
	Member(AccountId),
	/// Dummy to manage the fact we have instancing.
	_Phantom(sp_std::marker::PhantomData<I>),
}

/// Origin for the collective module.
pub type Origin<T, I=DefaultInstance> = RawOrigin<<T as frame_system::Trait>::AccountId, I>;

#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug)]
/// Info for keeping track of a motion being voted on.
pub struct Votes<AccountId, BlockNumber> {
	/// The proposal's unique index.
	index: ProposalIndex,
	/// The number of approval votes that are needed to pass the motion.
	threshold: MemberCount,
	/// The current set of voters that approved it.
	ayes: Vec<AccountId>,
	/// The current set of voters that rejected it.
	nays: Vec<AccountId>,
	/// The hard end time of this vote.
	end: BlockNumber,
}

decl_storage! {
	trait Store for Module<T: Trait<I>, I: Instance=DefaultInstance> as Collective {
		/// The hashes of the active proposals.
		pub Proposals get(fn proposals): Vec<T::Hash>;
		/// Actual proposal for a given hash, if it's current.
		pub ProposalOf get(fn proposal_of):
			map hasher(identity) T::Hash => Option<<T as Trait<I>>::Proposal>;
		/// Votes on a given proposal, if it is ongoing.
		pub Voting get(fn voting):
			map hasher(identity) T::Hash => Option<Votes<T::AccountId, T::BlockNumber>>;
		/// Proposals so far.
		pub ProposalCount get(fn proposal_count): u32;
		/// The current members of the collective. This is stored sorted (just by value).
		pub Members get(fn members): Vec<T::AccountId>;
		/// The member who provides the default vote for any other members that do not vote before
		/// the timeout. If None, then no member has that privilege.
		pub Prime get(fn prime): Option<T::AccountId>;
	}
	add_extra_genesis {
		config(phantom): sp_std::marker::PhantomData<I>;
		config(members): Vec<T::AccountId>;
		build(|config| Module::<T, I>::initialize_members(&config.members))
	}
}

decl_event! {
	pub enum Event<T, I=DefaultInstance> where
		<T as frame_system::Trait>::Hash,
		<T as frame_system::Trait>::AccountId,
	{
		/// A motion (given hash) has been proposed (by given account) with a threshold (given
		/// `MemberCount`).
		Proposed(AccountId, ProposalIndex, Hash, MemberCount),
		/// A motion (given hash) has been voted on by given account, leaving
		/// a tally (yes votes and no votes given respectively as `MemberCount`).
		Voted(AccountId, Hash, bool, MemberCount, MemberCount),
		/// A motion was approved by the required threshold.
		Approved(Hash),
		/// A motion was not approved by the required threshold.
		Disapproved(Hash),
		/// A motion was executed; `bool` is true if returned without error.
		Executed(Hash, bool),
		/// A single member did some action; `bool` is true if returned without error.
		MemberExecuted(Hash, bool),
		/// A proposal was closed after its duration was up.
		Closed(Hash, MemberCount, MemberCount),
	}
}

decl_error! {
	pub enum Error for Module<T: Trait<I>, I: Instance> {
		/// Account is not a member
		NotMember,
		/// Duplicate proposals not allowed
		DuplicateProposal,
		/// Proposal must exist
		ProposalMissing,
		/// Mismatched index
		WrongIndex,
		/// Duplicate vote ignored
		DuplicateVote,
		/// Members are already initialized!
		AlreadyInitialized,
		/// The close call is made too early, before the end of the voting.
		TooEarly,
		/// There can only be a maximum of `MaxMembers`.
		TooManyMembers,
		/// There can only be a maximum of `MaxProposals` active proposals.
		TooManyProposals,
		/// The given weight bound for the proposal was too low.
		WrongProposalBound,
	}
}

/// Functions for calcuating the weight of dispatchables.
mod weight_for {
	use frame_support::weights::{RuntimeDbWeight, Weight};

	/// Calculate the weight for `set_members`.
	///
	/// Based on benchmark:
	/// 0 + M * 20.47 + N * 0.109 + P * 26.29 µs (min squares analysis)
	pub(crate) fn set_members(
		db: RuntimeDbWeight,
		old_count: impl Into<Weight>,
		new_count: impl Into<Weight>,
		proposals: impl Into<Weight> + Copy,
	) -> Weight {
		db.reads_writes(1, 1) // mutate `Members`
			.saturating_add(db.writes(1)) // set `Prime`
			.saturating_add(db.reads(1)) // read `Proposals`
			.saturating_add(db.reads_writes(proposals.into(), proposals.into())) // update votes (`Voting`)
			.saturating_add(old_count.into().saturating_mul(21_000_000)) // M
			.saturating_add(new_count.into().saturating_mul(110_000)) // N
			.saturating_add(proposals.into().saturating_mul(27_000_000)) // P
	}

	// The bytes are responsible for an insignificant amount of weight.
	// Length of proposals is limited by length fees.
	const MAX_ASSUMED_PROPOSAL_BYTES: Weight = 1_024;

	/// Calculate the weight for `execute`.
	///
	/// Based on benchmark:
	/// 22.62 + M * 0.115 + B * 0.003 µs (min squares analysis)
	pub(crate) fn execute(
		db: RuntimeDbWeight,
		members: impl Into<Weight>,
		proposal: impl Into<Weight>,
	) -> Weight {
		db.reads(1) // read members for `is_member`
			.saturating_add(23_000_000) // constant
			.saturating_add(3_000 * MAX_ASSUMED_PROPOSAL_BYTES) // B
			.saturating_add(120_000 * members.into()) // M
			.saturating_add(proposal.into()) // P
	}

	/// Calculate the weight for `propose` if the proposal is executed straight away (`threshold < 2`).
	///
	/// Based on benchmark:
	/// 28.12 + M * 0.218 + B * 0.003 µs (min squares analysis)
	pub(crate) fn propose_execute(
		db: RuntimeDbWeight,
		members: impl Into<Weight>,
		proposal: impl Into<Weight>,
	) -> Weight {
		db.reads(2) // `is_member` + `contains_key`
			.saturating_add(29_000_000) // constant
			.saturating_add(3_000 * MAX_ASSUMED_PROPOSAL_BYTES) // B
			.saturating_add(220_000 * members.into()) // M
			.saturating_add(proposal.into()) // P1
	}

	/// Calculate the weight for `propose` if the proposal is put up for a vote (`threshold >= 2`).
	///
	/// Based on benchmark:
	/// 49.75 + M * 0.105 + P2 0.502 + B * 0.006 µs (min squares analysis)
	pub(crate) fn propose_proposed(
		db: RuntimeDbWeight,
		members: impl Into<Weight>,
		proposals: impl Into<Weight>,
	) -> Weight {
		db.reads(2) // `is_member` + `contains_key`
			+ db.reads_writes(2, 4) // `proposal` insertion
			+ 50_000_000 // constant
			+ 6_000 * MAX_ASSUMED_PROPOSAL_BYTES // B
			+ 110_000 * members.into() // M
			+ 510_000 * proposals.into() // P2
	}

	/// Calculate the weight for `vote`.
	///
	/// Based on benchmark:
	/// 24.03 + M * 0.349 + P * 0.119 + B * 0.003 µs (min squares analysis)
	pub(crate) fn vote(
		db: RuntimeDbWeight,
		members: impl Into<Weight>,
	) -> Weight {
		db.reads(1) // read `Members`
			+ db.reads_writes(1, 1) // mutate `Voting`
			+ 30_000_000 // constant
			+ 500_000 * members.into() // M
	}

	/// Calculate the weight for `close`.
	///
	/// Based on benchmarks:
	/// - early disapproved: 37.21 + M * 0.239 + P2 * 0.466 + B * 0.002 µs (min squares analysis)
	/// - early approved:    50.82 + M * 0.211 + P2 * 0.478 + B * 0.008 µs (min squares analysis)
	/// - disapproved:       51.08 + M * 0.224 + P2 * 0.475 + B * 0.003 µs (min squares analysis)
	/// - approved:          65.95 + M * 0.226 + P2 * 0.487 + B * 0.005 µs (min squares analysis)
	pub(crate) fn close(
		db: RuntimeDbWeight,
		members: impl Into<Weight> + Copy,
		proposal_weight: impl Into<Weight>,
		proposals: impl Into<Weight>,
	) -> Weight {
		close_without_finalize(db, members)
			.saturating_add(db.reads(1)) // `Prime`
			.saturating_add(db.writes(1)) // `Proposals`
			.saturating_add(db.writes(1)) // `Voting`
			.saturating_add(proposal_weight.into()) // P1
			.saturating_add(490_000 * proposals.into()) // P2
	}

	/// Calculate the weight for `close` without the call to `finalize_proposal`.
	pub(crate) fn close_without_finalize(
		db: RuntimeDbWeight,
		members: impl Into<Weight>,
	) -> Weight {
		db.reads(3) // `Members`, `Voting`, `ProposalOf`
			+ 66_000_000 // constant
			+ 8_000 * MAX_ASSUMED_PROPOSAL_BYTES // B
			+ 250_000 * members.into() // M
	}
}

/// Return the weight of a dispatch call result as an `Option`.
///
/// Will return the weight regardless of what the state of the result is.
fn get_result_weight(result: DispatchResultWithPostInfo) -> Option<Weight> {
	match result {
		Ok(post_info) => post_info.actual_weight,
		Err(err) => err.post_info.actual_weight,
	}
}


// Note that councillor operations are assigned to the operational class.
decl_module! {
	pub struct Module<T: Trait<I>, I: Instance=DefaultInstance> for enum Call where origin: <T as frame_system::Trait>::Origin {
		type Error = Error<T, I>;

		fn deposit_event() = default;

		/// Set the collective's membership.
		///
		/// - `new_members`: The new member list. Be nice to the chain and provide it sorted.
		/// - `prime`: The prime member whose vote sets the default.
		///
		/// Requires root origin.
		///
		/// # <weight>
		/// ## Weight
		/// - `O(MP + N)` where:
		///   - `M` old-members-count (code- and governance-bounded)
		///   - `N` new-members-count (code- and governance-bounded)
		///   - `P` proposals-count (code-bounded)
		/// - DB:
		///   - 1 storage mutation (codec `O(M)` read, `O(N)` write) for reading and writing the members
		///   - 1 storage read (codec `O(P)`) for reading the proposals
		///   - `P` storage mutations (codec `O(M)`) for updating the votes for each proposal
		///   - 1 storage write (codec `O(1)`) for deleting the old `prime` and setting the new one
		/// # </weight>
		#[weight = (
			weight_for::set_members(
				T::DbWeight::get(),
				T::MaxMembers::get(), // M
				new_members.len() as Weight, // N
				T::MaxProposals::get(), // P
			),
			DispatchClass::Operational
		)]
		fn set_members(origin,
			new_members: Vec<T::AccountId>,
			prime: Option<T::AccountId>,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			ensure!(new_members.len() <= T::MaxMembers::get() as usize, Error::<T, I>::TooManyMembers);

			let old = Members::<T, I>::get();
			let mut new_members = new_members;
			new_members.sort();
			<Self as ChangeMembers<T::AccountId>>::set_members_sorted(&new_members[..], &old);
			Prime::<T, I>::set(prime);

			Ok(Some(weight_for::set_members(
				T::DbWeight::get(),
				old.len() as Weight, // M
				new_members.len() as Weight, // N
				T::MaxProposals::get(), // P
			)).into())
		}

		/// Dispatch a proposal from a member using the `Member` origin.
		///
		/// Origin must be a member of the collective.
		///
		/// # <weight>
		/// ## Weight
		/// - `O(M + P)` where `M` members-count (code-bounded) and `P` complexity of dispatching `proposal`
		/// - DB: 1 read (codec `O(M)`) + DB access of `proposal`
		/// - 1 event
		/// # </weight>
		#[weight = (
			weight_for::execute(T::DbWeight::get(), T::MaxMembers::get(), proposal.get_dispatch_info().weight),
			DispatchClass::Operational
		)]
		fn execute(origin, proposal: Box<<T as Trait<I>>::Proposal>) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let members = Self::members();
			ensure!(members.contains(&who), Error::<T, I>::NotMember);

			let proposal_hash = T::Hashing::hash_of(&proposal);
			let result = proposal.dispatch(RawOrigin::Member(who).into());
			Self::deposit_event(RawEvent::MemberExecuted(proposal_hash, result.is_ok()));

			Ok(get_result_weight(result).map(|w| weight_for::execute(
				T::DbWeight::get(),
				members.len() as Weight,
				w
			)).into())
		}

		/// Add a new proposal to either be voted on or executed directly.
		///
		/// Requires the sender to be member.
		///
		/// `threshold` determines whether `proposal` is executed directly (`threshold < 2`)
		/// or put up for voting.
		///
		/// # <weight>
		/// ## Weight
		/// - `O(B + M + P1)` or `O(B + M + P2)` where:
		///   - `B` is `proposal` size in bytes (length-fee-bounded)
		///   - `M` is members-count (code- and governance-bounded)
		///   - branching is influenced by `threshold` where:
		///     - `P1` is proposal execution complexity (`threshold < 2`)
		///     - `P2` is proposals-count (code-bounded) (`threshold >= 2`)
		/// - DB:
		///   - 1 storage read `is_member` (codec `O(M)`)
		///   - 1 storage read `ProposalOf::contains_key` (codec `O(1)`)
		///   - DB accesses influenced by `threshold`:
		///     - EITHER storage accesses done by `proposal` (`threshold < 2`)
		///     - OR proposal insertion (`threshold <= 2`)
		///       - 1 storage mutation `Proposals` (codec `O(P2)`)
		///       - 1 storage mutation `ProposalCount` (codec `O(1)`)
		///       - 1 storage write `ProposalOf` (codec `O(B)`)
		///       - 1 storage write `Voting` (codec `O(M)`)
		///   - 1 event
		/// # </weight>
		#[weight = (
			if *threshold < 2 {
				weight_for::propose_execute(
					T::DbWeight::get(),
					T::MaxMembers::get(), // M
					proposal.get_dispatch_info().weight, // P1
				)
			} else {
				weight_for::propose_proposed(
					T::DbWeight::get(),
					T::MaxMembers::get(), // M
					T::MaxProposals::get() // P2
				)
			},
			DispatchClass::Operational
		)]
		fn propose(origin,
			#[compact] threshold: MemberCount,
			proposal: Box<<T as Trait<I>>::Proposal>,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let members = Self::members();
			ensure!(members.contains(&who), Error::<T, I>::NotMember);

			let proposal_hash = T::Hashing::hash_of(&proposal);
			ensure!(!<ProposalOf<T, I>>::contains_key(proposal_hash), Error::<T, I>::DuplicateProposal);

			if threshold < 2 {
				let seats = Self::members().len() as MemberCount;
				let result = proposal.dispatch(RawOrigin::Members(1, seats).into());
				Self::deposit_event(RawEvent::Executed(proposal_hash, result.is_ok()));

				Ok(get_result_weight(result).map(|w| weight_for::propose_execute(
					T::DbWeight::get(),
					members.len() as Weight, // M
					w, // P1
				)).into())
			} else {
				let active_proposals =
					<Proposals<T, I>>::try_mutate(|proposals| -> Result<usize, DispatchError> {
						proposals.push(proposal_hash);
						ensure!(
							proposals.len() <= T::MaxProposals::get() as usize,
							Error::<T, I>::TooManyProposals
						);
						Ok(proposals.len())
					})?;
				let index = Self::proposal_count();
				<ProposalCount<I>>::mutate(|i| *i += 1);
				<ProposalOf<T, I>>::insert(proposal_hash, *proposal);
				let end = system::Module::<T>::block_number() + T::MotionDuration::get();
				let votes = Votes { index, threshold, ayes: vec![who.clone()], nays: vec![], end };
				<Voting<T, I>>::insert(proposal_hash, votes);

				Self::deposit_event(RawEvent::Proposed(who, index, proposal_hash, threshold));

				Ok(Some(weight_for::propose_proposed(
					T::DbWeight::get(),
					members.len() as Weight, // M
					active_proposals as Weight // P2
				)).into())
			}
		}

		/// Add an aye or nay vote for the sender to the given proposal.
		///
		/// Requires the sender to be a member.
		///
		/// # <weight>
		/// ## Weight
		/// - `O(M)` where `M` is members-count (code- and governance-bounded)
		/// - DB:
		///   - 1 storage read `Members` (codec `O(M)`)
		///   - 1 storage mutation `Voting` (codec `O(M)`)
		/// - 1 event
		/// # </weight>
		#[weight = (
			weight_for::vote(T::DbWeight::get(), T::MaxMembers::get()),
			DispatchClass::Operational
		)]
		fn vote(origin,
			proposal: T::Hash,
			#[compact] index: ProposalIndex,
			approve: bool,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let members = Self::members();
			ensure!(members.contains(&who), Error::<T, I>::NotMember);

			let mut voting = Self::voting(&proposal).ok_or(Error::<T, I>::ProposalMissing)?;
			ensure!(voting.index == index, Error::<T, I>::WrongIndex);

			let position_yes = voting.ayes.iter().position(|a| a == &who);
			let position_no = voting.nays.iter().position(|a| a == &who);

			if approve {
				if position_yes.is_none() {
					voting.ayes.push(who.clone());
				} else {
					Err(Error::<T, I>::DuplicateVote)?
				}
				if let Some(pos) = position_no {
					voting.nays.swap_remove(pos);
				}
			} else {
				if position_no.is_none() {
					voting.nays.push(who.clone());
				} else {
					Err(Error::<T, I>::DuplicateVote)?
				}
				if let Some(pos) = position_yes {
					voting.ayes.swap_remove(pos);
				}
			}

			let yes_votes = voting.ayes.len() as MemberCount;
			let no_votes = voting.nays.len() as MemberCount;
			Self::deposit_event(RawEvent::Voted(who, proposal, approve, yes_votes, no_votes));

			Voting::<T, I>::insert(&proposal, voting);

			Ok(Some(weight_for::vote(T::DbWeight::get(), members.len() as Weight)).into())
		}

		/// Close a vote that is either approved, disapproved or whose voting period has ended.
		///
		/// May be called by any signed account in order to finish voting and close the proposal.
		///
		/// If called before the end of the voting period it will only close the vote if it is
		/// has enough votes to be approved or disapproved.
		///
		/// If called after the end of the voting period abstentions are counted as rejections 
		/// unless there is a prime member set and the prime member cast an approval.
		///
		/// + `proposal_weight_bound`: The maximum amount of weight consumed by executing the closed proposal.
		///
		/// # <weight>
		/// ## Weight
		/// - `O(B + M + P1 + P2)` where:
		///   - `B` is `proposal` size in bytes (length-fee-bounded)
		///   - `M` is members-count (code- and governance-bounded)
		///   - `P1` is the complexity of `proposal` preimage.
		///   - `P2` is proposal-count (code-bounded)
		/// - DB:
		///  - 2 storage reads (`Members`: codec `O(M)`, `Prime`: codec `O(1)`)
		///  - 3 mutations (`Voting`: codec `O(M)`, `ProposalOf`: codec `O(B)`, `Proposals`: codec `O(P2)`)
		///  - any mutations done while executing `proposal` (`P1`)
		/// - up to 3 events
		/// # </weight>
		#[weight = (
			weight_for::close(
				T::DbWeight::get(),
				T::MaxMembers::get(), // `M`
				*proposal_weight_bound, // `P1`
				T::MaxProposals::get() // `P2`
			),
			DispatchClass::Operational
		)]
		fn close(origin,
			proposal: T::Hash,
			#[compact] index: ProposalIndex,
			proposal_weight_bound: Weight,
		) -> DispatchResultWithPostInfo {
			let _ = ensure_signed(origin)?;

			let voting = Self::voting(&proposal).ok_or(Error::<T, I>::ProposalMissing)?;
			ensure!(voting.index == index, Error::<T, I>::WrongIndex);

			let mut no_votes = voting.nays.len() as MemberCount;
			let mut yes_votes = voting.ayes.len() as MemberCount;
			let seats = Self::members().len() as MemberCount;
			let approved = yes_votes >= voting.threshold;
			let disapproved = seats.saturating_sub(no_votes) < voting.threshold;
			// Allow (dis-)approving the proposal as soon as there are enough votes.
			if approved || disapproved {
				let p = ProposalOf::<T, I>::get(proposal);
				let proposal_weight = p.as_ref().map(|p| p.get_dispatch_info().weight).unwrap_or(0);
				ensure!(proposal_weight <= proposal_weight_bound, Error::<T, I>::WrongProposalBound);
				return Ok(Some(
					weight_for::close_without_finalize(T::DbWeight::get(), seats)
						.saturating_add(Self::finalize_proposal(approved, seats, voting, proposal, p))
				).into());
			}

			// Only allow actual closing of the proposal after the voting period has ended.
			ensure!(system::Module::<T>::block_number() >= voting.end, Error::<T, I>::TooEarly);
		
			// default to true only if there's a prime and they voted in favour.
			let default = Self::prime().map_or(false, |who| voting.ayes.iter().any(|a| a == &who));
		
			let abstentions = seats - (yes_votes + no_votes);
			match default {
				true => yes_votes += abstentions,
				false => no_votes += abstentions,
			}
			let approved = yes_votes >= voting.threshold;

			let p = ProposalOf::<T, I>::get(proposal);
			let proposal_weight = p.as_ref().map(|p| p.get_dispatch_info().weight).unwrap_or(0);
			ensure!(proposal_weight <= proposal_weight_bound, Error::<T, I>::WrongProposalBound);
			Self::deposit_event(RawEvent::Closed(proposal, yes_votes, no_votes));
			Ok(Some(
				weight_for::close_without_finalize(T::DbWeight::get(), seats)
					.saturating_add(T::DbWeight::get().reads(1)) // read `Prime`
					.saturating_add(Self::finalize_proposal(approved, seats, voting, proposal, p))
			).into())
		}
	}
}

impl<T: Trait<I>, I: Instance> Module<T, I> {
	pub fn is_member(who: &T::AccountId) -> bool {
		Self::members().contains(who)
	}

	/// Weight:
	/// If `approved`:
	/// - the weight of `proposal` preimage.
	/// - two events deposited.
	/// - two removals, one mutation.
	/// - computation and i/o `O(P + L)` where:
	///   - `P` is number of active proposals,
	///   - `L` is the encoded length of `proposal` preimage.
	///
	/// If not `approved`:
	/// - one event deposited.
	/// Two removals, one mutation.
	/// Computation and i/o `O(P)` where:
	/// - `P` is number of active proposals
	fn finalize_proposal(
		approved: bool,
		seats: MemberCount,
		voting: Votes<T::AccountId, T::BlockNumber>,
		proposal_hash: T::Hash,
		proposal: Option<<T as Trait<I>>::Proposal>,
	) -> Weight {
		let db = T::DbWeight::get();
		let mut weight: Weight = 0;
		if approved {
			Self::deposit_event(RawEvent::Approved(proposal_hash));

			// execute motion, assuming it exists.
			if let Some(p) = proposal {
				let dispatch_weight = p.get_dispatch_info().weight;
				let origin = RawOrigin::Members(voting.threshold, seats).into();
				let result = p.dispatch(origin);
				Self::deposit_event(RawEvent::Executed(proposal_hash, result.is_ok()));
				weight = weight.saturating_add(
					get_result_weight(result).unwrap_or(dispatch_weight) // P1
				);
			}
		} else {
			// disapproved
			Self::deposit_event(RawEvent::Disapproved(proposal_hash));
		}

		// remove vote
		ProposalOf::<T, I>::remove(&proposal_hash);
		Voting::<T, I>::remove(&proposal_hash);
		let mut proposal_len = T::MaxProposals::get() as Weight;
		Proposals::<T, I>::mutate(|proposals| {
			proposal_len = proposals.len() as Weight;
			proposals.retain(|h| h != &proposal_hash)
		});
		weight.saturating_add(db.reads_writes(1, 3)) // `Voting`, `Proposals`, `ProposalOf`
			.saturating_add(490_000 * proposal_len) // P2
	}
}

impl<T: Trait<I>, I: Instance> ChangeMembers<T::AccountId> for Module<T, I> {
	/// Update the members of the collective. Votes are updated and the prime is reset.
	///
	/// # <weight>
	/// ## Weight
	/// - `O(MP + N)`
	///   - where `M` old-members-count (governance-bounded)
	///   - where `N` new-members-count (governance-bounded)
	///   - where `P` proposals-count
	/// - DB:
	///   - 1 storage read (codec `O(P)`) for reading the proposals
	///   - `P` storage mutations for updating the votes (codec `O(M)`)
	///   - 1 storage write (codec `O(N)`) for storing the new members
	///   - 1 storage write (codec `O(1)`) for deleting the old prime
	/// # </weight>
	fn change_members_sorted(
		_incoming: &[T::AccountId],
		outgoing: &[T::AccountId],
		new: &[T::AccountId],
	) {
		// remove accounts from all current voting in motions.
		let mut outgoing = outgoing.to_vec();
		outgoing.sort_unstable();
		for h in Self::proposals().into_iter() {
			<Voting<T, I>>::mutate(h, |v|
				if let Some(mut votes) = v.take() {
					votes.ayes = votes.ayes.into_iter()
						.filter(|i| outgoing.binary_search(i).is_err())
						.collect();
					votes.nays = votes.nays.into_iter()
						.filter(|i| outgoing.binary_search(i).is_err())
						.collect();
					*v = Some(votes);
				}
			);
		}
		Members::<T, I>::put(new);
		Prime::<T, I>::kill();
	}

	fn set_prime(prime: Option<T::AccountId>) {
		Prime::<T, I>::set(prime);
	}
}

impl<T: Trait<I>, I: Instance> InitializeMembers<T::AccountId> for Module<T, I> {
	fn initialize_members(members: &[T::AccountId]) {
		if !members.is_empty() {
			assert!(<Members<T, I>>::get().is_empty(), "Members are already initialized!");
			<Members<T, I>>::put(members);
		}
	}
}

/// Ensure that the origin `o` represents at least `n` members. Returns `Ok` or an `Err`
/// otherwise.
pub fn ensure_members<OuterOrigin, AccountId, I>(o: OuterOrigin, n: MemberCount)
	-> result::Result<MemberCount, &'static str>
where
	OuterOrigin: Into<result::Result<RawOrigin<AccountId, I>, OuterOrigin>>
{
	match o.into() {
		Ok(RawOrigin::Members(x, _)) if x >= n => Ok(n),
		_ => Err("bad origin: expected to be a threshold number of members"),
	}
}

pub struct EnsureMember<AccountId, I=DefaultInstance>(sp_std::marker::PhantomData<(AccountId, I)>);
impl<
	O: Into<Result<RawOrigin<AccountId, I>, O>> + From<RawOrigin<AccountId, I>>,
	AccountId: Default,
	I,
> EnsureOrigin<O> for EnsureMember<AccountId, I> {
	type Success = AccountId;
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Member(id) => Ok(id),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		O::from(RawOrigin::Member(Default::default()))
	}
}

pub struct EnsureMembers<N: U32, AccountId, I=DefaultInstance>(sp_std::marker::PhantomData<(N, AccountId, I)>);
impl<
	O: Into<Result<RawOrigin<AccountId, I>, O>> + From<RawOrigin<AccountId, I>>,
	N: U32,
	AccountId,
	I,
> EnsureOrigin<O> for EnsureMembers<N, AccountId, I> {
	type Success = (MemberCount, MemberCount);
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Members(n, m) if n >= N::VALUE => Ok((n, m)),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		O::from(RawOrigin::Members(N::VALUE, N::VALUE))
	}
}

pub struct EnsureProportionMoreThan<N: U32, D: U32, AccountId, I=DefaultInstance>(
	sp_std::marker::PhantomData<(N, D, AccountId, I)>
);
impl<
	O: Into<Result<RawOrigin<AccountId, I>, O>> + From<RawOrigin<AccountId, I>>,
	N: U32,
	D: U32,
	AccountId,
	I,
> EnsureOrigin<O> for EnsureProportionMoreThan<N, D, AccountId, I> {
	type Success = ();
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Members(n, m) if n * D::VALUE > N::VALUE * m => Ok(()),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		O::from(RawOrigin::Members(1u32, 0u32))
	}
}

pub struct EnsureProportionAtLeast<N: U32, D: U32, AccountId, I=DefaultInstance>(
	sp_std::marker::PhantomData<(N, D, AccountId, I)>
);
impl<
	O: Into<Result<RawOrigin<AccountId, I>, O>> + From<RawOrigin<AccountId, I>>,
	N: U32,
	D: U32,
	AccountId,
	I,
> EnsureOrigin<O> for EnsureProportionAtLeast<N, D, AccountId, I> {
	type Success = ();
	fn try_origin(o: O) -> Result<Self::Success, O> {
		o.into().and_then(|o| match o {
			RawOrigin::Members(n, m) if n * D::VALUE >= N::VALUE * m => Ok(()),
			r => Err(O::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> O {
		O::from(RawOrigin::Members(0u32, 0u32))
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use frame_support::{Hashable, assert_ok, assert_noop, parameter_types, weights::Weight};
	use frame_system::{self as system, EventRecord, Phase};
	use hex_literal::hex;
	use sp_core::H256;
	use sp_runtime::{
		Perbill, traits::{BlakeTwo256, IdentityLookup, Block as BlockT}, testing::Header,
		BuildStorage,
	};
	use crate as collective;

	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
		pub const MotionDuration: u64 = 3;
		pub const MaxMembers: MemberCount = 100;
		pub const MaxProposals: u32 = 100;
	}
	impl frame_system::Trait for Test {
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
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type DbWeight = ();
		type BlockExecutionWeight = ();
		type ExtrinsicBaseWeight = ();
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
		type ModuleToIndex = ();
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
	}
	impl Trait<Instance1> for Test {
		type Origin = Origin;
		type Proposal = Call;
		type Event = Event;
		type MotionDuration = MotionDuration;
		type MaxMembers = MaxMembers;
		type MaxProposals = MaxProposals;
	}
	impl Trait for Test {
		type Origin = Origin;
		type Proposal = Call;
		type Event = Event;
		type MotionDuration = MotionDuration;
		type MaxMembers = MaxMembers;
		type MaxProposals = MaxProposals;
	}

	pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
	pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<u32, u64, Call, ()>;

	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic
		{
			System: system::{Module, Call, Event<T>},
			Collective: collective::<Instance1>::{Module, Call, Event<T>, Origin<T>, Config<T>},
			DefaultCollective: collective::{Module, Call, Event<T>, Origin<T>, Config<T>},
		}
	);

	pub fn new_test_ext() -> sp_io::TestExternalities {
		let mut ext: sp_io::TestExternalities = GenesisConfig {
			collective_Instance1: Some(collective::GenesisConfig {
				members: vec![1, 2, 3],
				phantom: Default::default(),
			}),
			collective: None,
		}.build_storage().unwrap().into();
		ext.execute_with(|| System::set_block_number(1));
		ext
	}

	#[test]
	fn motions_basic_environment_works() {
		new_test_ext().execute_with(|| {
			assert_eq!(Collective::members(), vec![1, 2, 3]);
			assert_eq!(Collective::proposals(), Vec::<H256>::new());
		});
	}

	fn make_proposal(value: u64) -> Call {
		Call::System(frame_system::Call::remark(value.encode()))
	}

	#[test]
	fn test_set_members_error_case() {
		new_test_ext().execute_with(|| {
			assert_noop!(
				Collective::set_members(Origin::ROOT, vec![1; MaxMembers::get() as usize + 1], None),
				Error::<Test, Instance1>::TooManyMembers
			);
		});
	}

	#[test]
	fn close_works() {
		new_test_ext().execute_with(|| {
			let proposal = make_proposal(42);
			let hash = BlakeTwo256::hash_of(&proposal);

			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(2), hash.clone(), 0, true));

			System::set_block_number(3);
			assert_noop!(
				Collective::close(Origin::signed(4), hash.clone(), 0, Weight::max_value()),
				Error::<Test, Instance1>::TooEarly
			);

			System::set_block_number(4);
			assert_ok!(Collective::close(Origin::signed(4), hash.clone(), 0, Weight::max_value()));

			let record = |event| EventRecord { phase: Phase::Initialization, event, topics: vec![] };
			assert_eq!(System::events(), vec![
				record(Event::collective_Instance1(RawEvent::Proposed(1, 0, hash.clone(), 3))),
				record(Event::collective_Instance1(RawEvent::Voted(2, hash.clone(), true, 2, 0))),
				record(Event::collective_Instance1(RawEvent::Closed(hash.clone(), 2, 1))),
				record(Event::collective_Instance1(RawEvent::Disapproved(hash.clone())))
			]);
		});
	}

	#[test]
	fn proposal_weight_limit_works() {
		new_test_ext().execute_with(|| {
			let proposal = Call::Collective(crate::Call::set_members(vec![1, 2, 3], None));
			let hash = BlakeTwo256::hash_of(&proposal);

			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(2), hash.clone(), 0, true));

			System::set_block_number(4);
			let proposal_weight = proposal.get_dispatch_info().weight;
			assert_noop!(
				Collective::close(Origin::signed(4), hash.clone(), 0, proposal_weight - 100),
				Error::<Test, Instance1>::WrongProposalBound
			);
			assert_ok!(Collective::close(Origin::signed(4), hash.clone(), 0, Weight::max_value()));
		})
	}

	#[test]
	fn close_with_prime_works() {
		new_test_ext().execute_with(|| {
			let proposal = make_proposal(42);
			let hash = BlakeTwo256::hash_of(&proposal);
			assert_ok!(Collective::set_members(Origin::ROOT, vec![1, 2, 3], Some(3)));

			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(2), hash.clone(), 0, true));

			System::set_block_number(4);
			assert_ok!(Collective::close(Origin::signed(4), hash.clone(), 0, Weight::max_value()));

			let record = |event| EventRecord { phase: Phase::Initialization, event, topics: vec![] };
			assert_eq!(System::events(), vec![
				record(Event::collective_Instance1(RawEvent::Proposed(1, 0, hash.clone(), 3))),
				record(Event::collective_Instance1(RawEvent::Voted(2, hash.clone(), true, 2, 0))),
				record(Event::collective_Instance1(RawEvent::Closed(hash.clone(), 2, 1))),
				record(Event::collective_Instance1(RawEvent::Disapproved(hash.clone())))
			]);
		});
	}

	#[test]
	fn close_with_voting_prime_works() {
		new_test_ext().execute_with(|| {
			let proposal = make_proposal(42);
			let hash = BlakeTwo256::hash_of(&proposal);
			assert_ok!(Collective::set_members(Origin::ROOT, vec![1, 2, 3], Some(1)));

			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(2), hash.clone(), 0, true));

			System::set_block_number(4);
			assert_ok!(Collective::close(Origin::signed(4), hash.clone(), 0, Weight::max_value()));

			let record = |event| EventRecord { phase: Phase::Initialization, event, topics: vec![] };
			assert_eq!(System::events(), vec![
				record(Event::collective_Instance1(RawEvent::Proposed(1, 0, hash.clone(), 3))),
				record(Event::collective_Instance1(RawEvent::Voted(2, hash.clone(), true, 2, 0))),
				record(Event::collective_Instance1(RawEvent::Closed(hash.clone(), 3, 0))),
				record(Event::collective_Instance1(RawEvent::Approved(hash.clone()))),
				record(Event::collective_Instance1(RawEvent::Executed(hash.clone(), false)))
			]);
		});
	}

	#[test]
	fn removal_of_old_voters_votes_works() {
		new_test_ext().execute_with(|| {
			let proposal = make_proposal(42);
			let hash = BlakeTwo256::hash_of(&proposal);
			let end = 4;
			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(2), hash.clone(), 0, true));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 0, threshold: 3, ayes: vec![1, 2], nays: vec![], end })
			);
			Collective::change_members_sorted(&[4], &[1], &[2, 3, 4]);
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 0, threshold: 3, ayes: vec![2], nays: vec![], end })
			);

			let proposal = make_proposal(69);
			let hash = BlakeTwo256::hash_of(&proposal);
			assert_ok!(Collective::propose(Origin::signed(2), 2, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(3), hash.clone(), 1, false));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 1, threshold: 2, ayes: vec![2], nays: vec![3], end })
			);
			Collective::change_members_sorted(&[], &[3], &[2, 4]);
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 1, threshold: 2, ayes: vec![2], nays: vec![], end })
			);
		});
	}

	#[test]
	fn removal_of_old_voters_votes_works_with_set_members() {
		new_test_ext().execute_with(|| {
			let proposal = make_proposal(42);
			let hash = BlakeTwo256::hash_of(&proposal);
			let end = 4;
			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(2), hash.clone(), 0, true));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 0, threshold: 3, ayes: vec![1, 2], nays: vec![], end })
			);
			assert_ok!(Collective::set_members(Origin::ROOT, vec![2, 3, 4], None));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 0, threshold: 3, ayes: vec![2], nays: vec![], end })
			);

			let proposal = make_proposal(69);
			let hash = BlakeTwo256::hash_of(&proposal);
			assert_ok!(Collective::propose(Origin::signed(2), 2, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(3), hash.clone(), 1, false));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 1, threshold: 2, ayes: vec![2], nays: vec![3], end })
			);
			assert_ok!(Collective::set_members(Origin::ROOT, vec![2, 4], None));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 1, threshold: 2, ayes: vec![2], nays: vec![], end })
			);
		});
	}

	#[test]
	fn propose_works() {
		new_test_ext().execute_with(|| {
			let proposal = make_proposal(42);
			let hash = proposal.blake2_256().into();
			let end = 4;
			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_eq!(Collective::proposals(), vec![hash]);
			assert_eq!(Collective::proposal_of(&hash), Some(proposal));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 0, threshold: 3, ayes: vec![1], nays: vec![], end })
			);

			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::collective_Instance1(RawEvent::Proposed(
						1,
						0,
						hex!["68eea8f20b542ec656c6ac2d10435ae3bd1729efc34d1354ab85af840aad2d35"].into(),
						3,
					)),
					topics: vec![],
				}
			]);
		});
	}

	#[test]
	fn limit_active_proposals() {
		new_test_ext().execute_with(|| {
			for i in 0..MaxProposals::get() {
				let proposal = make_proposal(i as u64);
				assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			}
			let proposal = make_proposal(MaxProposals::get() as u64 + 1);
			assert_noop!(
				Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())),
				Error::<Test, Instance1>::TooManyProposals
			);
		})
	}

	#[test]
	fn motions_ignoring_non_collective_proposals_works() {
		new_test_ext().execute_with(|| {
			let proposal = make_proposal(42);
			assert_noop!(
				Collective::propose(Origin::signed(42), 3, Box::new(proposal.clone())),
				Error::<Test, Instance1>::NotMember
			);
		});
	}

	#[test]
	fn motions_ignoring_non_collective_votes_works() {
		new_test_ext().execute_with(|| {
			let proposal = make_proposal(42);
			let hash: H256 = proposal.blake2_256().into();
			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_noop!(
				Collective::vote(Origin::signed(42), hash.clone(), 0, true),
				Error::<Test, Instance1>::NotMember,
			);
		});
	}

	#[test]
	fn motions_ignoring_bad_index_collective_vote_works() {
		new_test_ext().execute_with(|| {
			System::set_block_number(3);
			let proposal = make_proposal(42);
			let hash: H256 = proposal.blake2_256().into();
			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_noop!(
				Collective::vote(Origin::signed(2), hash.clone(), 1, true),
				Error::<Test, Instance1>::WrongIndex,
			);
		});
	}

	#[test]
	fn motions_revoting_works() {
		new_test_ext().execute_with(|| {
			let proposal = make_proposal(42);
			let hash: H256 = proposal.blake2_256().into();
			let end = 4;
			assert_ok!(Collective::propose(Origin::signed(1), 2, Box::new(proposal.clone())));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 0, threshold: 2, ayes: vec![1], nays: vec![], end })
			);
			assert_noop!(
				Collective::vote(Origin::signed(1), hash.clone(), 0, true),
				Error::<Test, Instance1>::DuplicateVote,
			);
			assert_ok!(Collective::vote(Origin::signed(1), hash.clone(), 0, false));
			assert_eq!(
				Collective::voting(&hash),
				Some(Votes { index: 0, threshold: 2, ayes: vec![], nays: vec![1], end })
			);
			assert_noop!(
				Collective::vote(Origin::signed(1), hash.clone(), 0, false),
				Error::<Test, Instance1>::DuplicateVote,
			);

			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::collective_Instance1(RawEvent::Proposed(
						1,
						0,
						hex!["68eea8f20b542ec656c6ac2d10435ae3bd1729efc34d1354ab85af840aad2d35"].into(),
						2,
					)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::collective_Instance1(RawEvent::Voted(
						1,
						hex!["68eea8f20b542ec656c6ac2d10435ae3bd1729efc34d1354ab85af840aad2d35"].into(),
						false,
						0,
						1,
					)),
					topics: vec![],
				}
			]);
		});
	}

	#[test]
	fn motions_reproposing_disapproved_works() {
		new_test_ext().execute_with(|| {
			let proposal = make_proposal(42);
			let hash: H256 = proposal.blake2_256().into();
			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(2), hash.clone(), 0, false));
			assert_ok!(Collective::close(Origin::signed(2), hash.clone(), 0, Weight::max_value()));
			assert_eq!(Collective::proposals(), vec![]);
			assert_ok!(Collective::propose(Origin::signed(1), 2, Box::new(proposal.clone())));
			assert_eq!(Collective::proposals(), vec![hash]);
		});
	}

	#[test]
	fn motions_disapproval_works() {
		new_test_ext().execute_with(|| {
			let proposal = make_proposal(42);
			let hash: H256 = proposal.blake2_256().into();
			assert_ok!(Collective::propose(Origin::signed(1), 3, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(2), hash.clone(), 0, false));
			assert_ok!(Collective::close(Origin::signed(2), hash.clone(), 0, Weight::max_value()));

			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::collective_Instance1(
						RawEvent::Proposed(
							1,
							0,
							hex!["68eea8f20b542ec656c6ac2d10435ae3bd1729efc34d1354ab85af840aad2d35"].into(),
							3,
						)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::collective_Instance1(RawEvent::Voted(
						2,
						hex!["68eea8f20b542ec656c6ac2d10435ae3bd1729efc34d1354ab85af840aad2d35"].into(),
						false,
						1,
						1,
					)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::collective_Instance1(RawEvent::Disapproved(
						hex!["68eea8f20b542ec656c6ac2d10435ae3bd1729efc34d1354ab85af840aad2d35"].into(),
					)),
					topics: vec![],
				}
			]);
		});
	}

	#[test]
	fn motions_approval_works() {
		new_test_ext().execute_with(|| {
			let proposal = make_proposal(42);
			let hash: H256 = proposal.blake2_256().into();
			assert_ok!(Collective::propose(Origin::signed(1), 2, Box::new(proposal.clone())));
			assert_ok!(Collective::vote(Origin::signed(2), hash.clone(), 0, true));
			assert_ok!(Collective::close(Origin::signed(2), hash.clone(), 0, Weight::max_value()));

			assert_eq!(System::events(), vec![
				EventRecord {
					phase: Phase::Initialization,
					event: Event::collective_Instance1(RawEvent::Proposed(
						1,
						0,
						hex!["68eea8f20b542ec656c6ac2d10435ae3bd1729efc34d1354ab85af840aad2d35"].into(),
						2,
					)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::collective_Instance1(RawEvent::Voted(
						2,
						hex!["68eea8f20b542ec656c6ac2d10435ae3bd1729efc34d1354ab85af840aad2d35"].into(),
						true,
						2,
						0,
					)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::collective_Instance1(RawEvent::Approved(
						hex!["68eea8f20b542ec656c6ac2d10435ae3bd1729efc34d1354ab85af840aad2d35"].into(),
					)),
					topics: vec![],
				},
				EventRecord {
					phase: Phase::Initialization,
					event: Event::collective_Instance1(RawEvent::Executed(
						hex!["68eea8f20b542ec656c6ac2d10435ae3bd1729efc34d1354ab85af840aad2d35"].into(),
						false,
					)),
					topics: vec![],
				}
			]);
		});
	}
}
