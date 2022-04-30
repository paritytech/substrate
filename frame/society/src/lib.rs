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

//! # Society Pallet
//!
//! - [`Config`]
//! - [`Call`]
//!
//! ## Overview
//!
//! The Society pallet is an economic game which incentivizes users to participate
//! and maintain a membership society.
//!
//! ### User Types
//!
//! At any point, a user in the society can be one of a:
//! * Bidder - A user who has submitted intention of joining the society.
//! * Candidate - A user who will be voted on to join the society.
//! * Suspended Candidate - A user who failed to win a vote.
//! * Member - A user who is a member of the society.
//! * Suspended Member - A member of the society who has accumulated too many strikes
//! or failed their membership challenge.
//!
//! Of the non-suspended members, there is always a:
//! * Head - A member who is exempt from suspension.
//! * Defender - A member whose membership is under question and voted on again.
//!
//! Of the non-suspended members of the society, a random set of them are chosen as
//! "skeptics". The mechanics of skeptics is explained in the
//! [member phase](#member-phase) below.
//!
//! ### Mechanics
//!
//! #### Rewards
//!
//! Members are incentivized to participate in the society through rewards paid
//! by the Society treasury. These payments have a maturity period that the user
//! must wait before they are able to access the funds.
//!
//! #### Punishments
//!
//! Members can be punished by slashing the reward payouts that have not been
//! collected. Additionally, members can accumulate "strikes", and when they
//! reach a max strike limit, they become suspended.
//!
//! #### Skeptics
//!
//! During the voting period, a random set of members are selected as "skeptics".
//! These skeptics are expected to vote on the current candidates. If they do not vote,
//! their skeptic status is treated as a rejection vote, the member is deemed
//! "lazy", and are given a strike per missing vote.
//!
//! #### Membership Challenges
//!
//! Every challenge rotation period, an existing member will be randomly selected
//! to defend their membership into society. Then, other members can vote whether
//! this defender should stay in society. A simple majority wins vote will determine
//! the outcome of the user. Ties are treated as a failure of the challenge, but
//! assuming no one else votes, the defender always get a free vote on their
//! own challenge keeping them in the society. The Head member is exempt from the
//! negative outcome of a membership challenge.
//!
//! #### Society Treasury
//!
//! The membership society is independently funded by a treasury managed by this
//! pallet. Some subset of this treasury is placed in a Society Pot, which is used
//! to determine the number of accepted bids.
//!
//! #### Rate of Growth
//!
//! The membership society can grow at a rate of 10 accepted candidates per rotation period up
//! to the max membership threshold. Once this threshold is met, candidate selections
//! are stalled until there is space for new members to join. This can be resolved by
//! voting out existing members through the random challenges or by using governance
//! to increase the maximum membership count.
//!
//! ### User Life Cycle
//!
//! A user can go through the following phases:
//!
//! ```ignore
//!           +------->  User  <----------+
//!           |           +               |
//!           |           |               |
//! +----------------------------------------------+
//! |         |           |               |        |
//! |         |           v               |        |
//! |         |        Bidder <-----------+        |
//! |         |           +               |        |
//! |         |           |               +        |
//! |         |           v            Suspended   |
//! |         |       Candidate +----> Candidate   |
//! |         |           +               +        |
//! |         |           |               |        |
//! |         +           |               |        |
//! |   Suspended +------>|               |        |
//! |      Member         |               |        |
//! |         ^           |               |        |
//! |         |           v               |        |
//! |         +-------+ Member <----------+        |
//! |                                              |
//! |                                              |
//! +------------------Society---------------------+
//! ```
//!
//! #### Initialization
//!
//! The society is initialized with a single member who is automatically chosen as the Head.
//!
//! #### Bid Phase
//!
//! New users must have a bid to join the society.
//!
//! A user can make a bid by reserving a deposit. Alternatively, an already existing member
//! can create a bid on a user's behalf by "vouching" for them.
//!
//! A bid includes reward information that the user would like to receive for joining
//! the society. A vouching bid can additionally request some portion of that reward as a tip
//! to the voucher for vouching for the prospective candidate.
//!
//! Every rotation period, Bids are ordered by reward amount, and the pallet
//! selects as many bids the Society Pot can support for that period.
//!
//! These selected bids become candidates and move on to the Candidate phase.
//! Bids that were not selected stay in the bidder pool until they are selected or
//! a user chooses to "unbid".
//!
//! #### Candidate Phase
//!
//! Once a bidder becomes a candidate, members vote whether to approve or reject
//! that candidate into society. This voting process also happens during a rotation period.
//!
//! The approval and rejection criteria for candidates are not set on chain,
//! and may change for different societies.
//!
//! At the end of the rotation period, we collect the votes for a candidate
//! and randomly select a vote as the final outcome.
//!
//! ```ignore
//!  [ a-accept, r-reject, s-skeptic ]
//! +----------------------------------+
//! |                                  |
//! |  Member   |0|1|2|3|4|5|6|7|8|9|  |
//! |  -----------------------------   |
//! |  Vote     |a|a|a|r|s|r|a|a|s|a|  |
//! |  -----------------------------   |
//! |  Selected | | | |x| | | | | | |  |
//! |                                  |
//! +----------------------------------+
//!
//! Result: Rejected
//! ```
//!
//! Each member that voted opposite to this randomly selected vote is punished by
//! slashing their unclaimed payouts and increasing the number of strikes they have.
//!
//! These slashed funds are given to a random user who voted the same as the
//! selected vote as a reward for participating in the vote.
//!
//! If the candidate wins the vote, they receive their bid reward as a future payout.
//! If the bid was placed by a voucher, they will receive their portion of the reward,
//! before the rest is paid to the winning candidate.
//!
//! One winning candidate is selected as the Head of the members. This is randomly
//! chosen, weighted by the number of approvals the winning candidates accumulated.
//!
//! If the candidate loses the vote, they are suspended and it is up to the Suspension
//! Judgement origin to determine if the candidate should go through the bidding process
//! again, should be accepted into the membership society, or rejected and their deposit
//! slashed.
//!
//! #### Member Phase
//!
//! Once a candidate becomes a member, their role is to participate in society.
//!
//! Regular participation involves voting on candidates who want to join the membership
//! society, and by voting in the right way, a member will accumulate future payouts.
//! When a payout matures, members are able to claim those payouts.
//!
//! Members can also vouch for users to join the society, and request a "tip" from
//! the fees the new member would collect by joining the society. This vouching
//! process is useful in situations where a user may not have enough balance to
//! satisfy the bid deposit. A member can only vouch one user at a time.
//!
//! During rotation periods, a random group of members are selected as "skeptics".
//! These skeptics are expected to vote on the current candidates. If they do not vote,
//! their skeptic status is treated as a rejection vote, the member is deemed
//! "lazy", and are given a strike per missing vote.
//!
//! There is a challenge period in parallel to the rotation period. During a challenge period,
//! a random member is selected to defend their membership to the society. Other members
//! make a traditional majority-wins vote to determine if the member should stay in the society.
//! Ties are treated as a failure of the challenge.
//!
//! If a member accumulates too many strikes or fails their membership challenge,
//! they will become suspended. While a member is suspended, they are unable to
//! claim matured payouts. It is up to the Suspension Judgement origin to determine
//! if the member should re-enter society or be removed from society with all their
//! future payouts slashed.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! #### For General Users
//!
//! * `bid` - A user can make a bid to join the membership society by reserving a deposit.
//! * `unbid` - A user can withdraw their bid for entry, the deposit is returned.
//!
//! #### For Members
//!
//! * `vouch` - A member can place a bid on behalf of a user to join the membership society.
//! * `unvouch` - A member can revoke their vouch for a user.
//! * `vote` - A member can vote to approve or reject a candidate's request to join the society.
//! * `defender_vote` - A member can vote to approve or reject a defender's continued membership
//! to the society.
//! * `payout` - A member can claim their first matured payment.
//! * `unfound` - Allow the founder to unfound the society when they are the only member.
//!
//! #### For Super Users
//!
//! * `found` - The founder origin can initiate this society. Useful for bootstrapping the Society
//! pallet on an already running chain.
//! * `judge_suspended_member` - The suspension judgement origin is able to make
//! judgement on a suspended member.
//! * `judge_suspended_candidate` - The suspension judgement origin is able to
//! make judgement on a suspended candidate.
//! * `set_max_membership` - The ROOT origin can update the maximum member count for the society.
//! The max membership count must be greater than 1.

// TODO: Sort out all the `limit: None` stuff for remove prefix.
// TODO: Membership subsets: ranks and badges.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

use frame_support::{
	pallet_prelude::*,
	traits::{
		BalanceStatus, ChangeMembers, Currency, EnsureOrigin, ExistenceRequirement::AllowDeath,
		Imbalance, OnUnbalanced, Randomness, ReservableCurrency,
	},
	PalletId,
};
use frame_system::pallet_prelude::*;
use rand_chacha::{
	rand_core::{RngCore, SeedableRng},
	ChaChaRng,
};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{
		AccountIdConversion, CheckedAdd, CheckedSub, Hash, IntegerSquareRoot, Saturating,
		StaticLookup, TrailingZeroInput, Zero,
	},
	ArithmeticError::Overflow, Percent, RuntimeDebug,
};
use sp_std::prelude::*;

pub use pallet::*;

type BalanceOf<T, I> =
	<<T as Config<I>>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type NegativeImbalanceOf<T, I> = <<T as Config<I>>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;

/// A vote by a member on a candidate application.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub enum OldVote {
	/// The member has been chosen to be skeptic and has not yet taken any action.
	Skeptic,
	/// The member has rejected the candidate's application.
	Reject,
	/// The member approves of the candidate's application.
	Approve,
}

pub struct Vote {
	approve: bool,
	weight: u32,
}

/// A judgement by the suspension judgement origin on a suspended candidate.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub enum Judgement {
	/// The suspension judgement origin takes no direct judgment
	/// and places the candidate back into the bid pool.
	Rebid,
	/// The suspension judgement origin has rejected the candidate's application.
	Reject,
	/// The suspension judgement origin approves of the candidate's application.
	Approve,
}

/// Details of a payout given as a per-block linear "trickle".
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, Default, TypeInfo)]
pub struct Payout<Balance, BlockNumber> {
	/// Total value of the payout.
	value: Balance,
	/// Block number at which the payout begins.
	begin: BlockNumber,
	/// Total number of blocks over which the payout is spread.
	duration: BlockNumber,
	/// Total value paid out so far.
	paid: Balance,
}

/// Status of a vouching member.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub enum VouchingStatus {
	/// Member is currently vouching for a user.
	Vouching,
	/// Member is banned from vouching for other members.
	Banned,
}

/// Number of strikes that a member has against them.
pub type StrikeCount = u32;

/// A bid for entry into society.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub struct Bid<AccountId, Balance> {
	/// The bidder/candidate trying to enter society
	who: AccountId,
	/// The kind of bid placed for this bidder/candidate. See `BidKind`.
	kind: BidKind<AccountId, Balance>,
	/// The reward that the bidder has requested for successfully joining the society.
	value: Balance,
}

/// The index of a round of candidates.
pub type RoundIndex = u32;

/// The rank of a member.
pub type Rank = u32;

/// A bid for entry into society.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub struct Candidacy<AccountId, Balance> {
	/// The index of the round where the candidacy began.
	round: RoundIndex,
	/// The kind of bid placed for this bidder/candidate. See `BidKind`.
	kind: BidKind<AccountId, Balance>,
	/// The reward that the bidder has requested for successfully joining the society.
	bid: Balance,
	/// The tally of explicit approval votes so far.
	approvals: u32,
	/// The tally of explicit rejection votes so far.
	rejections: u32,
}

/// A vote by a member on a candidate application.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub enum BidKind<AccountId, Balance> {
	/// The CandidateDeposit was paid for this bid.
	Deposit(Balance),
	/// A member vouched for this bid. The account should be reinstated into `Members` once the
	/// bid is successful (or if it is rescinded prior to launch).
	Vouch(AccountId, Balance),
}

impl<AccountId: PartialEq, Balance> BidKind<AccountId, Balance> {
	fn check_voucher(&self, v: &AccountId) -> DispatchResult {
		if let BidKind::Vouch(ref a, _) = self {
			if a == v {
				Ok(())
			} else {
				Err("incorrect identity")?
			}
		} else {
			Err("not vouched")?
		}
	}
}

pub type PayoutsFor<T, I> = BoundedVec<
	(<T as frame_system::Config>::BlockNumber, BalanceOf<T, I>),
	<T as Config<I>>::MaxPayouts,
>;

/// Information concerning a member.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub struct MemberRecord<Balance, BlockNumber, MaxPayouts> {
	rank: Rank,
	strikes: StrikeCount,
	vouching: Option<VouchingStatus>,
	paid: Balance,
	index: u32,
	payouts: BoundedVec<(BlockNumber, Balance), MaxPayouts>,
}

pub type MemberRecordFor<T, I> = MemberRecord<
	BalanceOf<T, I>,
	<T as frame_system::Config>::BlockNumber,
	<T as Config<I>>::MaxPayouts,
>;

/// Record for an individual new member who was elevated from a candidate recently.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub struct IntakeRecord<AccountId, Balance> {
	who: AccountId,
	bid: Balance,
	round: RoundIndex,
}

pub type IntakeRecordFor<T, I> = IntakeRecord<
	<T as frame_system::Config>::AccountId,
	BalanceOf<T, I>,
>;

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::without_storage_info]
	pub struct Pallet<T, I = ()>(_);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self, I>> + IsType<<Self as frame_system::Config>::Event>;

		/// The societies's pallet id
		#[pallet::constant]
		type PalletId: Get<PalletId>;

		/// The currency type used for bidding.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// Something that provides randomness in the runtime.
		type Randomness: Randomness<Self::Hash, Self::BlockNumber>;

		/// The minimum amount of a deposit required for a bid to be made.
		#[pallet::constant]
		type CandidateDeposit: Get<BalanceOf<Self, I>>;

		/// The amount of the unpaid reward that gets deducted in the case that either a skeptic
		/// doesn't vote or someone votes in the wrong way.
		#[pallet::constant]
		type WrongSideDeduction: Get<BalanceOf<Self, I>>;

		/// The number of times a skeptic may not vote or vote the wrong way for a candidate before
		/// they become suspended.
		#[pallet::constant]
		type MaxStrikes: Get<u32>;

		/// The number of times a skeptic may not vote or vote the wrong way for a candidate before
		/// they get any payouts slashed in half.
		#[pallet::constant]
		type GraceStrikes: Get<u32>;

		/// The amount of incentive paid within each period. Doesn't include VoterTip.
		#[pallet::constant]
		type PeriodSpend: Get<BalanceOf<Self, I>>;

		/// The number of blocks on which new candidates should be voted on. Together with
		/// `ClaimPeriod`, this sums to the number of blocks between candidate intake periods.
		#[pallet::constant]
		type VotingPeriod: Get<Self::BlockNumber>;

		/// The number of blocks on which new candidates can claim their membership and be the
		/// named head.
		#[pallet::constant]
		type ClaimPeriod: Get<Self::BlockNumber>;

		/// The maximum duration of the payout lock.
		#[pallet::constant]
		type MaxLockDuration: Get<Self::BlockNumber>;

		/// The origin that is allowed to call `found`.
		type FounderSetOrigin: EnsureOrigin<Self::Origin>;

		/// The origin that is allowed to make suspension judgements.
		type JudgementOrigin: EnsureOrigin<Self::Origin>;

		/// The number of blocks between membership challenges.
		#[pallet::constant]
		type ChallengePeriod: Get<Self::BlockNumber>;

		/// The maximum number of candidates that we accept per round.
		#[pallet::constant]
		type MaxCandidateIntake: Get<u32>;

		/// The origin that is allowed to set the maximum number of members.
		type AdminOrigin: Get<u32>;

		/// The maximum number of payouts a member may have waiting unclaimed.
		#[pallet::constant]
		type MaxPayouts: Get<u32>;

		/// The maximum number of bids at once.
		#[pallet::constant]
		type MaxBids: Get<u32>;
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
		/// An incorrect position was provided.
		BadPosition,
		/// User is not a member.
		NotMember,
		/// User is already a member.
		AlreadyMember,
		/// User is suspended.
		Suspended,
		/// User is not suspended.
		NotSuspended,
		/// Nothing to payout.
		NoPayout,
		/// Society already founded.
		AlreadyFounded,
		/// Not enough in pot to accept candidate.
		InsufficientPot,
		/// Member is already vouching or banned from vouching again.
		AlreadyVouching,
		/// Member is not vouching.
		NotVouching,
		/// Cannot remove the head of the chain.
		Head,
		/// Cannot remove the founder.
		Founder,
		/// User has already made a bid.
		AlreadyBid,
		/// User is already a candidate.
		AlreadyCandidate,
		/// User is not a candidate.
		NotCandidate,
		/// Too many members in the society.
		MaxMembers,
		/// The caller is not the founder.
		NotFounder,
		/// The caller is not the head.
		NotHead,
		/// The membership cannot be claimed as the member does not (yet) have enough votes.
		NotApproved,
		/// The candidacy cannot be claimed/dropped as the voting is still in progress.
		InProgress,
		/// The candidacy cannot be dropped as the candidate is approved.
		Approved,
		/// The candidacy cannot be pruned until a full additional intake period has passed.
		TooEarly,
		/// The skeptic already voted.
		Voted,
		/// The skeptic need not vote on candidates from expired rounds.
		Expired,
		/// User is not a bidder.
		NotBidder,
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// The society is founded by the given identity.
		Founded { founder: T::AccountId },
		/// A membership bid just happened. The given account is the candidate's ID and their offer
		/// is the second.
		Bid { candidate_id: T::AccountId, offer: BalanceOf<T, I> },
		/// A membership bid just happened by vouching. The given account is the candidate's ID and
		/// their offer is the second. The vouching party is the third.
		Vouch { candidate_id: T::AccountId, offer: BalanceOf<T, I>, vouching: T::AccountId },
		/// A candidate was dropped (due to an excess of bids in the system).
		AutoUnbid { candidate: T::AccountId },
		/// A candidate was dropped (by their request).
		Unbid { candidate: T::AccountId },
		/// A candidate was dropped (by request of who vouched for them).
		Unvouch { candidate: T::AccountId },
		/// A group of candidates have been inducted. The batch's primary is the first value, the
		/// batch in full is the second.
		Inducted { primary: T::AccountId, candidates: Vec<T::AccountId> },
		/// A suspended member has been judged.
		SuspendedMemberJudgement { who: T::AccountId, judged: bool },
		/// A candidate has been suspended
		CandidateSuspended { candidate: T::AccountId },
		/// A member has been suspended
		MemberSuspended { member: T::AccountId },
		/// A member has been challenged
		Challenged { member: T::AccountId },
		/// A vote has been placed
		Vote { candidate: T::AccountId, voter: T::AccountId, vote: bool },
		/// A vote has been placed for a defending member
		DefenderVote { voter: T::AccountId, vote: bool },
		/// A new \[max\] member count has been set
		NewMaxMembers { max: u32 },
		/// Society is unfounded.
		Unfounded { founder: T::AccountId },
		/// Some funds were deposited into the society account.
		Deposit { value: BalanceOf<T, I> },
	}

	/// Old name generated by `decl_event`.
	#[deprecated(note = "use `Event` instead")]
	pub type RawEvent<T, I = ()> = Event<T, I>;

	/// The max number of members for the society at one time.
	#[pallet::storage]
	pub(super) type MaxMembers<T: Config<I>, I: 'static = ()> = StorageValue<_, u32, ValueQuery>;

	/// Amount of our account balance that is specifically for the next round's bid(s).
	#[pallet::storage]
	pub type Pot<T: Config<I>, I: 'static = ()> = StorageValue<_, BalanceOf<T, I>, ValueQuery>;

	/// The first member.
	#[pallet::storage]
	pub type Founder<T: Config<I>, I: 'static = ()> = StorageValue<_, T::AccountId>;

	/// The most primary from the most recently approved members.
	#[pallet::storage]
	pub type Head<T: Config<I>, I: 'static = ()> = StorageValue<_, T::AccountId>;

	/// A hash of the rules of this society concerning membership. Can only be set once and
	/// only by the founder.
	// TODO: Should be a map with rules for each rank and badge.
	#[pallet::storage]
	pub type Rules<T: Config<I>, I: 'static = ()> = StorageValue<_, T::Hash>;

	/// The current members and their rank. Doesn't include `SuspendedMembers`.
	#[pallet::storage]
	pub type Membership<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, T::AccountId, MemberRecordFor<T>, OptionQuery>;

	/// The number of items in `Membership` currently. (Doesn't include `SuspendedMembers`.)
	#[pallet::storage]
	pub type MemberCount<T: Config<I>, I: 'static = ()> = StorageValue<_, u32, ValueQuery>;

	/// The current items in `Membership` keyed by their unique index. Keys are densely populated
	/// `0..MemberCount` (does not include `MemberCount`).
	#[pallet::storage]
	pub type MemberByIndex<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, u32, T::AccountId, OptionQuery>;

	/// The set of suspended members.
	#[pallet::storage]
	pub type SuspendedMembers<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, T::AccountId, MemberRecordFor<T>, OptionQuery>;

	/// The number of rounds which have passed.
	#[pallet::storage]
	pub type RoundCount<T: Config<I>, I: 'static = ()> = StorageValue<_, RoundIndex, ValueQuery>;

	/// The current bids, stored ordered by the value of the bid.
	#[pallet::storage]
	pub(super) type Bids<T: Config<I>, I: 'static = ()> =
		StorageValue<_, BoundedVec<Bid<T::AccountId, BalanceOf<T, I>>, T::MaxBids>, ValueQuery>;

	#[pallet::storage]
	pub type Candidate<T: Config<I>, I: 'static = ()> = StorageMap<_,
		Blake2_128Concat,
		T::AccountId,
		Candidacy<T::AccountId, BalanceOf<T, I>>,
		OptionQuery,
	>;

	/// The current skeptics.
	#[pallet::storage]
	pub type Skeptic<T: Config<I>, I: 'static = ()> = StorageValue<_, Vec<T::AccountId>, ValueQuery>;

	/// Double map from Candidate -> Voter -> (Maybe) Vote.
	#[pallet::storage]
	pub(super) type Votes<T: Config<I>, I: 'static = ()> = StorageDoubleMap<_,
		Twox64Concat,
		T::AccountId,
		Twox64Concat,
		T::AccountId,
		Vote,
		OptionQuery,
	>;
	// TODO: Migrate from:
	//pub(super) type Votes<T: Config<I>, I: 'static = ()> =
	//	StorageDoubleMap<_, Twox64Concat, T::AccountId, Twox64Concat, T::AccountId, OldVote>;

	/// At the end of the claim period, this contains the most recently approved members (along with
	/// their bid and round ID) who is from the most recent round with the lowest bid. They will
	/// become the new `Head`.
	#[pallet::storage]
	pub type NextHead<T: Config<I>, I: 'static = ()> = StorageValue<_,
		IntakeRecordFor<T>,
		OptionQuery,
	>;

	/// The defending member currently being challenged, along with a running tally of approval and
	/// rejection votes.
	#[pallet::storage]
	pub(super) type Defending<T: Config<I>, I: 'static = ()> = StorageValue<_, (T::AccountId, T::AccountId, u32, u32)>;

	/// Votes for the defender.
	// TODO: Migrate (used to be `OldVote`)
	#[pallet::storage]
	pub(super) type DefenderVotes<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, T::AccountId, Vote>;

	// OLD STUFF

	// Moved to `Member`.
	// TODO: Needs refactor, migration into Membership, removal.
	/// Members currently vouching or banned from vouching again.
	#[pallet::storage]
	pub(super) type Vouching<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, T::AccountId, VouchingStatus>;

	/// The ongoing number of losing votes cast by the member.
	// TODO: Needs refactor, migration into Membership, removal.
	#[pallet::storage]
	pub(super) type Strikes<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, T::AccountId, StrikeCount, ValueQuery>;

	/// The current set of members, ordered.
	// TODO: Needs refactor, migration into Membership, removal.
	#[pallet::storage]
	#[pallet::getter(fn members)]
	pub type Members<T: Config<I>, I: 'static = ()> =
		StorageValue<_, Vec<T::AccountId>, ValueQuery>;

	/// The current set of candidates; bidders that are attempting to become members.
	// TODO: Needs refactor, migration into Candidate, removal.
	#[pallet::storage]
	#[pallet::getter(fn candidates)]
	pub type Candidates<T: Config<I>, I: 'static = ()> =
		StorageValue<_, Vec<Bid<T::AccountId, BalanceOf<T, I>>>, ValueQuery>;

	/// The set of suspended candidates.
	// TODO: Needs refactor and removal.
	// TODO: Ensure that it is empty immediately prior to upgrade.
	#[pallet::storage]
	#[pallet::getter(fn suspended_candidate)]
	pub type SuspendedCandidates<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Twox64Concat,
		T::AccountId,
		(BalanceOf<T, I>, BidKind<T::AccountId, BalanceOf<T, I>>),
	>;

	#[pallet::hooks]
	impl<T: Config<I>, I: 'static> Hooks<BlockNumberFor<T>> for Pallet<T, I> {
		fn on_initialize(n: T::BlockNumber) -> Weight {
			let mut members = vec![];

			let mut weight = 0;
			let weights = T::BlockWeights::get();

			let phrase = b"society_rotation";
			// we'll need a random seed here.
			// TODO: deal with randomness freshness
			// https://github.com/paritytech/substrate/issues/8312
			let (seed, _) = T::Randomness::random(phrase);
			// seed needs to be guaranteed to be 32 bytes.
			let seed = <[u8; 32]>::decode(&mut TrailingZeroInput::new(seed.as_ref()))
				.expect("input is padded with zeroes; qed");
			let mut rng = ChaChaRng::from_seed(seed);

			// Run a candidate/membership rotation
			match Self::period() {
				Period::Voting { elapsed: 0, .. } => {
					Self::rotate_intake(&mut rng);
					weight += weights.max_block / 20;
				},
				_ => {}
			}

			// Run a challenge rotation
			if (n % T::ChallengePeriod::get()).is_zero() {
				Self::rotate_challenge(&mut rng);
				weight += weights.max_block / 20;
			}

			weight
		}
	}

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config<I>, I: 'static = ()> {
		pub pot: BalanceOf<T, I>,
		pub members: Vec<T::AccountId>,
		pub max_members: u32,
	}

	#[cfg(feature = "std")]
	impl<T: Config<I>, I: 'static> Default for GenesisConfig<T, I> {
		fn default() -> Self {
			Self {
				pot: Default::default(),
				members: Default::default(),
				max_members: Default::default(),
			}
		}
	}

	#[pallet::genesis_build]
	impl<T: Config<I>, I: 'static> GenesisBuild<T, I> for GenesisConfig<T, I> {
		fn build(&self) {
			Pot::<T, I>::put(self.pot);
			MaxMembers::<T, I>::put(self.max_members);
			let first_member = self.members.first();
			if let Some(member) = first_member {
				Founder::<T, I>::put(member.clone());
				Head::<T, I>::put(member.clone());
			};
			let mut m = self.members.clone();
			m.sort();
			Members::<T, I>::put(m);
		}
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// A user outside of the society can make a bid for entry.
		///
		/// Payment: `CandidateDeposit` will be reserved for making a bid. It is returned
		/// when the bid becomes a member, or if the bid calls `unbid`.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// Parameters:
		/// - `value`: A one time payment the bid would like to receive when joining the society.
		///
		/// Key: B (len of bids), C (len of candidates), M (len of members), X (balance reserve)
		/// Total Complexity: O(M + B + C + logM + logB + X)
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn bid(origin: OriginFor<T>, value: BalanceOf<T, I>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(!SuspendedMembers::<T, I>::contains_key(&who), Error::<T, I>::Suspended);
			let mut bids = Bids::<T, I>::get();
			ensure!(!Self::has_bid(&bids, &who), Error::<T, I>::AlreadyBid);
			ensure!(!Candidate::<T, I>::contains_key(&who), Error::<T, I>::AlreadyCandidate);
			ensure!(!Membership::<T, I>::contains_key(&who), Error::<T, I>::AlreadyMember);

			let deposit = T::CandidateDeposit::get();
			T::Currency::reserve(&who, deposit)?;

			Self::insert_bid(&mut bids, &who, value.clone(), BidKind::Deposit(deposit));
			Bids::<T, I>::put(bids);
			Self::deposit_event(Event::<T, I>::Bid { candidate_id: who, offer: value });
			Ok(())
		}

		/// A bidder can remove their bid for entry into society.
		/// By doing so, they will have their candidate deposit returned or
		/// they will unvouch their voucher.
		///
		/// Payment: The bid deposit is unreserved if the user made a bid.
		///
		/// The dispatch origin for this call must be _Signed_ and a bidder.
		///
		/// Key: B (len of bids), X (balance unreserve)
		/// Total Complexity: O(B + X)
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn unbid(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;

			let mut bids = Bids::<T, I>::get();
			let pos = bids.iter().position(|bid| bid.who == who).ok_or(Error::<T, I>::NotBidder)?;
			Self::clean_bid(&bids.remove(pos));
			Bids::<T, I>::put(bids);
			Self::deposit_event(Event::<T, I>::Unbid { candidate: who });
			Ok(())
		}

		/// As a member, vouch for someone to join society by placing a bid on their behalf.
		///
		/// There is no deposit required to vouch for a new bid, but a member can only vouch for
		/// one bid at a time. If the bid becomes a suspended candidate and ultimately rejected by
		/// the suspension judgement origin, the member will be banned from vouching again.
		///
		/// As a vouching member, you can claim a tip if the candidate is accepted. This tip will
		/// be paid as a portion of the reward the member will receive for joining the society.
		///
		/// The dispatch origin for this call must be _Signed_ and a member.
		///
		/// Parameters:
		/// - `who`: The user who you would like to vouch for.
		/// - `value`: The total reward to be paid between you and the candidate if they become
		/// a member in the society.
		/// - `tip`: Your cut of the total `value` payout when the candidate is inducted into
		/// the society. Tips larger than `value` will be saturated upon payout.
		///
		/// Key: B (len of bids), C (len of candidates), M (len of members)
		/// Total Complexity: O(M + B + C + logM + logB + X)
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn vouch(
			origin: OriginFor<T>,
			who: T::AccountId,
			value: BalanceOf<T, I>,
			tip: BalanceOf<T, I>,
		) -> DispatchResult {
			let voucher = ensure_signed(origin)?;
			// Check user is not suspended.
			ensure!(!SuspendedCandidates::<T, I>::contains_key(&who), Error::<T, I>::Suspended);
			ensure!(!SuspendedMembers::<T, I>::contains_key(&who), Error::<T, I>::Suspended);
			// Check user is not a bid or candidate.
			let bids = Bids::<T, I>::get();
			ensure!(!Self::has_bid(&bids, &who), Error::<T, I>::AlreadyBid);
			let candidates = Candidates::<T, I>::get();
			ensure!(!Self::is_candidate(&candidates, &who), Error::<T, I>::AlreadyCandidate);
			// Check user is not already a member.
			let members = Members::<T, I>::get();
			ensure!(!Self::is_member(&members, &who), Error::<T, I>::AlreadyMember);
			// Check sender can vouch.
			ensure!(Self::is_member(&members, &voucher), Error::<T, I>::NotMember);
			ensure!(!Vouching::<T, I>::contains_key(&voucher), Error::<T, I>::AlreadyVouching);

			Vouching::<T, I>::insert(&voucher, VouchingStatus::Vouching);
			Self::put_bid(bids, &who, value.clone(), BidKind::Vouch(voucher.clone(), tip));
			Self::deposit_event(Event::<T, I>::Vouch {
				candidate_id: who,
				offer: value,
				vouching: voucher,
			});
			Ok(())
		}

		/// As a vouching member, unvouch a bid. This only works while vouched user is
		/// only a bidder (and not a candidate).
		///
		/// The dispatch origin for this call must be _Signed_ and a vouching member.
		///
		/// Parameters:
		/// - `pos`: Position in the `Bids` vector of the bid who should be unvouched.
		///
		/// Key: B (len of bids)
		/// Total Complexity: O(B)
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn unvouch(origin: OriginFor<T>, pos: u32) -> DispatchResult {
			let voucher = ensure_signed(origin)?;
			ensure!(
				Vouching::<T, I>::get(&voucher) == Some(VouchingStatus::Vouching),
				Error::<T, I>::NotVouching
			);

			let pos = pos as usize;
			Bids::<T, I>::mutate(|b| {
				if pos < b.len() {
					b[pos].kind.check_voucher(&voucher)?;
					Vouching::<T, I>::remove(&voucher);
					let who = b.remove(pos).who;
					Self::deposit_event(Event::<T, I>::Unvouch { candidate: who });
					Ok(())
				} else {
					Err(Error::<T, I>::BadPosition)?
				}
			})
		}

		/// As a member, vote on a candidate.
		///
		/// The dispatch origin for this call must be _Signed_ and a member.
		///
		/// Parameters:
		/// - `candidate`: The candidate that the member would like to bid on.
		/// - `approve`: A boolean which says if the candidate should be approved (`true`) or
		///   rejected (`false`).
		///
		/// Key: C (len of candidates), M (len of members)
		/// Total Complexity: O(M + logM + C)
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn vote(
			origin: OriginFor<T>,
			candidate: <T::Lookup as StaticLookup>::Source,
			approve: bool,
		) -> DispatchResult {
			let voter = ensure_signed(origin)?;
			let candidate = T::Lookup::lookup(candidate)?;

			let mut candidacy = Candidate::<T, I>::get(candidate).ok_or(Error::<T, I>::NotCandidate)?;
			let record = Membership::<T, I>::get(&voter).ok_or(Error::<T, I>::NotMember)?;

			// remove the old vote from the count, if there was one.
			match Votes::<T, I>::get(&candidate, &voter) {
				Some(Vote { approve: true, weight }) => candidacy.approves.saturating_reduce(weight),
				Some(Vote { approve: false, weight }) => candidacy.rejects.saturating_reduce(weight),
				_ => {},
			}
			let weight_root = record.rank + 1;
			let weight = weight_root * weight_root;
			match approve {
				true => candidacy.approves.saturating_accrue(1),
				false => candidacy.rejects.saturating_accrue(1),
			}
			Votes::<T, I>::insert(&candidate, &voter, Vote { approve, weight });
			Candidate::<T, I>::insert(&candidate, &candidacy);
			Self::deposit_event(Event::<T, I>::Vote { candidate, voter, vote: approve });
			Ok(())
		}

		/// As a member, vote on the defender.
		///
		/// The dispatch origin for this call must be _Signed_ and a member.
		///
		/// Parameters:
		/// - `approve`: A boolean which says if the candidate should be
		/// approved (`true`) or rejected (`false`).
		///
		/// Key: M (len of members)
		/// Total Complexity: O(M + logM)
		/// # </weight>
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn defender_vote(origin: OriginFor<T>, approve: bool) -> DispatchResult {
			let voter = ensure_signed(origin)?;
			let members = Members::<T, I>::get();
			ensure!(Self::is_member(&members, &voter), Error::<T, I>::NotMember);

			let vote = if approve { Vote::Approve } else { Vote::Reject };
			DefenderVotes::<T, I>::insert(&voter, vote);

			Self::deposit_event(Event::<T, I>::DefenderVote { voter, vote: approve });
			Ok(())
		}

		/// Transfer the first matured payout for the sender and remove it from the records.
		///
		/// NOTE: This extrinsic needs to be called multiple times to claim multiple matured
		/// payouts.
		///
		/// Payment: The member will receive a payment equal to their first matured
		/// payout to their free balance.
		///
		/// The dispatch origin for this call must be _Signed_ and a member with
		/// payouts remaining.
		///
		/// Key: M (len of members), P (number of payouts for a particular member)
		/// Total Complexity: O(M + logM + P + X)
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn payout(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let mut record = Membership::<T, I>::get(&who).ok_or(Error::<T, I>::NotMember)?;

			if let Some((when, amount)) = record.payouts.first() {
				if when <= &<frame_system::Pallet<T>>::block_number() {
					record.paid = record.paid.checked_add(amount).ok_or(Overflow)?;
					T::Currency::transfer(&Self::payouts(), &who, *amount, AllowDeath)?;
					record.payouts.remove(0);
					Membership::<T, I>::insert(&who, record);
					return Ok(())
				}
			}
			Err(Error::<T, I>::NoPayout)?
		}

		/// Repay the payment previously given to the member with the signed origin, and elevate
		/// them from rank 0 to rank 1.
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn repay(origin: OriginFor<T>) -> DispatchResult {
			todo!()
		}

		/// Remove the payment owed to the member with the signed origin, and elevate them from
		/// rank 0 to rank 1.
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn waive(origin: OriginFor<T>) -> DispatchResult {
			todo!()
		}

		/// Found the society.
		///
		/// This is done as a discrete action in order to allow for the
		/// pallet to be included into a running chain and can only be done once.
		///
		/// The dispatch origin for this call must be from the _FounderSetOrigin_.
		///
		/// Parameters:
		/// - `founder` - The first member and head of the newly founded society.
		/// - `max_members` - The initial max number of members for the society.
		/// - `rules` - The rules of this society concerning membership.
		///
		/// Complexity: O(1)
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn found(
			origin: OriginFor<T>,
			founder: T::AccountId,
			max_members: u32,
			rules: Vec<u8>,
		) -> DispatchResult {
			T::FounderSetOrigin::ensure_origin(origin)?;
			ensure!(!Head::<T, I>::exists(), Error::<T, I>::AlreadyFounded);
			ensure!(max_members > 1, Error::<T, I>::MaxMembers);
			// This should never fail in the context of this function...
			MaxMembers::<T, I>::put(max_members);
			Self::add_member(&founder, 1, BoundedVec::new())?;
			Head::<T, I>::put(&founder);
			Founder::<T, I>::put(&founder);
			Rules::<T, I>::put(T::Hashing::hash(&rules));
			Self::deposit_event(Event::<T, I>::Founded { founder });
			Ok(())
		}

		/// Annul the founding of the society.
		///
		/// The dispatch origin for this call must be Signed, and the signing account must be both
		/// the `Founder` and the `Head`. This implies that it may only be done when there is one
		/// member.
		///
		/// # <weight>
		/// - Two storage reads O(1).
		/// - Four storage removals O(1).
		/// - One event.
		///
		/// Total Complexity: O(1)
		/// # </weight>
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn unfound(origin: OriginFor<T>) -> DispatchResult {
			let founder = ensure_signed(origin)?;
			ensure!(Founder::<T, I>::get() == Some(founder.clone()), Error::<T, I>::NotFounder);
			ensure!(Head::<T, I>::get() == Some(founder.clone()), Error::<T, I>::NotHead);

			Members::<T, I>::kill();
			MemberCount::<T, I>::kill();
			MemberByIndex::<T, I>::remove_all(None);
			Membership::<T, I>::remove_all(None);
			Votes::<T, I>::remove_all(None);
			Head::<T, I>::kill();
			Founder::<T, I>::kill();
			Rules::<T, I>::kill();
			Candidates::<T, I>::kill();
			Candidate::<T, I>::remove_all(None);
			SuspendedCandidates::<T, I>::remove_all(None);
			Self::deposit_event(Event::<T, I>::Unfounded { founder });
			Ok(())
		}

		/// Allow suspension judgement origin to make judgement on a suspended member.
		///
		/// If a suspended member is forgiven, we simply add them back as a member, not affecting
		/// any of the existing storage items for that member.
		///
		/// If a suspended member is rejected, remove all associated storage items, including
		/// their payouts, and remove any vouched bids they currently have.
		///
		/// The dispatch origin for this call must be from the _JudgementOrigin_.
		///
		/// Parameters:
		/// - `who` - The suspended member to be judged.
		/// - `forgive` - A boolean representing whether the suspension judgement origin forgives
		///   (`true`) or rejects (`false`) a suspended member.
		///
		/// Key: B (len of bids), M (len of members)
		/// Total Complexity: O(M + logM + B)
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn judge_suspended_member(
			origin: OriginFor<T>,
			who: T::AccountId,
			forgive: bool,
		) -> DispatchResult {
			T::JudgementOrigin::ensure_origin(origin)?;
			let record = SuspendedMembers::<T, I>::get(&who).ok_or(Error::<T, I>::NotSuspended)?;

			if forgive {
				// Try to add member back to society. Can fail with `MaxMembers` limit.
				Self::reinstate_member(&who, record.rank, record.payouts)?;
			} else {
				Self::unreserve_payout(record.payouts.into_iter().map(|x| x.1).sum());
			}

			SuspendedMembers::<T, I>::remove(&who);
			Self::deposit_event(Event::<T, I>::SuspendedMemberJudgement { who, judged: forgive });
			Ok(())
		}

		/// Allows root origin to change the maximum number of members in society.
		/// New max membership count must be no less than the current number of members.
		///
		/// The dispatch origin for this call must be Root.
		///
		/// Parameters:
		/// - `max` - The maximum number of members for the society.
		///
		/// Total Complexity: O(1)
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn set_max_members(origin: OriginFor<T>, max: u32) -> DispatchResult {
			T::AdminOrigin::ensure_origin(origin)?;
			ensure!(max >= MemberCount::<T, I>::get(), Error::<T, I>::MaxMembers);
			MaxMembers::<T, I>::put(max);
			Self::deposit_event(Event::<T, I>::NewMaxMembers { max });
			Ok(())
		}

		/// Transform an approved candidate into a member. Callable only by the
		/// the candidate, and only after the period for voting has ended.
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn claim_membership(origin: OriginFor<T>) -> DispatchResult {
			let candidate = ensure_signed(origin)?;
			let candidacy = Candidate::<T, I>::get(&candidate).ok_or(Error::<T, I>::NotCandidate)?;
			ensure!(candidacy.approvals > candidacy.rejections, Error::<T, I>::NotApproved);
			ensure!(!Self::in_progress(candidacy.round), Error::<T, I>::InProgress);
			Self::induct_member(candidate, candidacy, 0)
		}

		/// Transform an approved candidate into a member. Callable only by the
		/// `JudgementOrigin` and only after the period for voting has ended.
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn force_membership(origin: OriginFor<T>, candidate: T::AccountId) -> DispatchResult {
			T::JudgementOrigin::ensure_origin(origin)?;
			let candidacy = Candidate::<T, I>::get(&candidate).ok_or(Error::<T, I>::NotCandidate)?;
			ensure!(!Self::in_progress(candidacy.round), Error::<T, I>::InProgress);
			Self::induct_member(candidate, candidacy, 0)
		}

		/// Remove the candidate's application from the society. Callable only by the
		/// `JudgementOrigin` and the candidate, and only after the period for voting has ended.
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn kick_candidate(origin: OriginFor<T>, candidate: T::AccountId) -> DispatchResult {
			T::JudgementOrigin::ensure_origin(origin)?;
			let candidacy = Candidate::<T, I>::get(&candidate).ok_or(Error::<T, I>::NotCandidate)?;
			ensure!(!Self::in_progress(candidacy.round), Error::<T, I>::InProgress);
			Self::check_skeptic(&candidate, &candidacy);
			Votes::<T, I>::remove_prefix(&candidate, None);
			Candidate::<T, I>::remove(&candidate);
			Ok(())
		}

		/// Remove the candidate's failed application from the society. Callable only by the
		/// the candidate, and only after the period for voting has ended.
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn resign_candidate(origin: OriginFor<T>) -> DispatchResult {
			let candidate = ensure_signed(origin)?;
			let candidacy = Candidate::<T, I>::get(&candidate).ok_or(Error::<T, I>::NotCandidate)?;
			ensure!(candidacy.approvals <= candidacy.rejections, Error::<T, I>::Approved);
			ensure!(!Self::in_progress(candidacy.round), Error::<T, I>::InProgress);
			Self::check_skeptic(&candidate, &candidacy);
			Votes::<T, I>::remove_prefix(&candidate, None);
			Candidate::<T, I>::remove(&candidate);
			Ok(())
		}

		/// Remove a `candidate`'s failed application from the society. Callable by any
		/// signed origin but only after the subsequent period for voting has ended.
		#[pallet::weight(T::BlockWeights::get().max_block / 10)]
		pub fn drop_candidate(origin: OriginFor<T>, candidate: T::AccountId) -> DispatchResult {
			ensure_signed(origin)?;
			let candidacy = Candidate::<T, I>::get(&candidate).ok_or(Error::<T, I>::NotCandidate)?;
			ensure!(candidacy.approvals <= candidacy.rejections, Error::<T, I>::Approved);
			ensure!(RoundCount::<T, I>::get() > candidacy.round + 1, Error::<T, I>::TooEarly);
			Votes::<T, I>::remove_prefix(&candidate, None);
			Candidate::<T, I>::remove(&candidate);
			Ok(())
		}
	}
}

/// Simple ensure origin struct to filter for the founder account.
pub struct EnsureFounder<T>(sp_std::marker::PhantomData<T>);
impl<T: Config> EnsureOrigin<T::Origin> for EnsureFounder<T> {
	type Success = T::AccountId;
	fn try_origin(o: T::Origin) -> Result<Self::Success, T::Origin> {
		o.into().and_then(|o| match (o, Founder::<T>::get()) {
			(frame_system::RawOrigin::Signed(ref who), Some(ref f)) if who == f => Ok(who.clone()),
			(r, _) => Err(T::Origin::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> T::Origin {
		let founder = Founder::<T>::get().expect("society founder should exist");
		T::Origin::from(frame_system::RawOrigin::Signed(founder))
	}
}

/// Pick an item at pseudo-random from the slice, given the `rng`. `None` iff the slice is empty.
fn pick_item<'a, R: RngCore, T>(rng: &mut R, items: &'a [T]) -> Option<&'a T> {
	if items.is_empty() {
		None
	} else {
		Some(&items[pick_usize(rng, items.len() - 1)])
	}
}

/// Pick a new PRN, in the range [0, `max`] (inclusive).
fn pick_usize(rng: &mut impl RngCore, max: usize) -> usize {
	(rng.next_u32() % (max as u32 + 1)) as usize
}

struct InputFromRng<'a, T>(&'a mut T);
impl<'a, T: RngCore> codec::Input for InputFromRng<'a, T> {
	fn remaining_len(&mut self) -> Result<Option<usize>, Error> {
		return Ok(None)
	}

	fn read(&mut self, into: &mut [u8]) -> Result<(), Error> {
		self.0.fill_bytes(into);
		Ok(())
	}
}

pub enum Period<BlockNumber> {
	Voting { elapsed: BlockNumber, more: BlockNumber },
	Claim { elapsed: BlockNumber, more: BlockNumber },
}

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Get the period we are currently in.
	fn period() -> Period<T::BlockNumber> {
		let claim_period = T::ClaimPeriod::get();
		let voting_period = T::VotingPeriod::get();
		let rotation_period = voting_period + claim_period;
		let now = <T as frame_system::Config>::block_number();
		let phase = now % rotation_period;
		if phase < voting_period {
			Period::Voting { elapsed: phase, more: voting_period - phase }
		} else {
			Period::Claim { elapsed: phase - voting_period, more: rotation_period - phase }
		}
	}

	/// Returns true if the given `target_round` is still in its initial voting phase.
	fn in_progress(target_round: RoundIndex) -> bool {
		let round = RoundCount::<T, I>::get();
		target_round == round && matches!(Self::period(), Period::Voting {..})
	}

	fn check_skeptic(candidate: &T::AccountId, candidacy: &Candidacy<T::AccountId, BalanceOf<T>>) {
		if RoundCount::<T, I>::get() != candidacy.round { return }
		// We expect the skeptic to have voted.
		let skeptic = Skeptic::<T, I>::get();
		let maybe_vote = Votes::<T, I>::get(&candidate, &skeptic);
		let approved = candidacy.approvals > candidacy.rejections;
		let rejected = candidacy.rejections > candidacy.approvals;
		match (maybe_vote, approved, rejected) {
			(None, _, _) | (Some(false), true, false) | (Some(true), false, true) => {
				// Can't do much if the punishment doesn't work out.
				let _ = Self::strike_member(&skeptic);
			},
			_ => {},
		}
	}

	/// End the current challenge period and start a new one.
	fn rotate_challenge(rng: &mut impl RngCore) {
		// TODO.
		// End current defender rotation
		if let Some((defender, skeptic, approvals, rejections)) = Defending::<T, I>::get() {
			if rejections > approvals {
				// Member has failed the challenge
				Self::suspend_member(&defender);
			}

			// TODO: check skeptic voted and that their vote was with the majority. Slash if not.

			// Clean up all votes.
			DefenderVotes::<T, I>::remove_all(None);
		}

		// Avoid challenging if there's only two members since we never challenge the Head or
		// the Founder.
		if MemberCount::<T, I>::get() > 2 {
			let defender = Self::pick_defendent(&mut rng).expect("exited if members empty; qed");
			let skeptic = Self::pick_member_except(&mut rng, &defender).expect("exited if members empty; qed");
			Self::deposit_event(Event::<T, I>::Challenged { member: defender.clone() });
			Defending::<T, I>::put((defender, skeptic, 0, 0));
		} else {
			Defending::<T, I>::kill();
		}
	}

	/// End the current intake period and begin a new one.
	///
	/// ---------------------------------------------
	///  #10  || #11           _              || #12
	///       || Voting        | Claiming     ||
	/// ---------------------------------------------
	fn rotate_intake(rng: &mut impl RngCore) {
		// We assume there's at least one member or this logic won't work.
		let member_count = MemberCount::get();
		if member_count < 1 {
			return
		}
		let maybe_head = NextHead::<T, I>::take();
		if let Some(head) = maybe_head {
			Head::<T, I>::put(head);
		}

		// Bump the pot by at most `PeriodSpend`, but less if there's not very much left in our
		// account.
		let mut pot = Pot::<T, I>::get();
		let unaccounted = T::Currency::free_balance(&Self::account_id()).saturating_sub(pot);
		pot.saturating_accrue(T::PeriodSpend::get().min(unaccounted / 2u8.into()));
		Pot::<T, I>::put(&pot);

		// Bump round and create the new intake.
		let mut round_count = RoundCount::<T, I>::get();
		round_count.saturating_inc();
		let candidate_count = Self::select_new_candidates(round_count, member_count, pot);
		if candidate_count > 0 {
			// Select a member at random and make them the skeptic for this round.
			let skeptic = Self::pick_member(&mut rng).expect("exited if members empty; qed");
			Skeptic::<T, I>::put(skeptic);
		}
		RoundCount::<T, I>::put(round_count);
	}

	/// Remove a selection of bidding accounts such that the total bids is no greater than `Pot` and
	/// the number of bids would not surpass `MaxMembers` if all were accepted. At most one bid may
	/// be zero.
	///
	/// Candidates are inserted from each bidder.
	///
	/// The number of candidates inserted are returned.
	pub fn select_new_candidates(
		round: RoundIndex,
		member_count: u32,
		pot: BalanceOf<T, I>,
	) -> usize {
		let max_members = MaxMembers::<T, I>::get() as usize;

		// Get the number of left-most bidders whose bids add up to less than `pot`.
		let mut bids = Bids::<T, I>::get();
		let mut max_selections: usize = (T::MaxCandidateIntake::get() as usize)
			.min(max_members.saturating_sub(member_count))
			.min(bids.len());

		let mut selections = 0;
		// A running total of the cost to onboard these bids
		let mut total_cost: BalanceOf<T, I> = Zero::zero();

		bids.retain(|bid| {
			// We only accept a zero bid as the first selection.
			total_cost.saturating_accrue(bid.value);
			let accept = selections < max_selections
				&& (!bid.value.is_zero() || selections == 0)
				&& total_cost <= pot;
			if accept {
				let candidacy = Candidacy {
					round,
					kind: bid.kind,
					bid: bid.value,
					approvals: 0,
					rejections: 0,
				};
				Candidate::<T, I>::insert(&bid.who, candidacy);
				selections.saturating_inc();
			}
			!accept
		});

		// No need to reset Bids if we're not taking anything.
		Bids::<T, I>::put(bids);
	}

	/// Puts a bid into storage ordered by smallest to largest value.
	/// Allows a maximum of 1000 bids in queue, removing largest value people first.
	fn insert_bid(
		bids: &mut BoundedVec<Bid<T::AccountId, BalanceOf<T, I>>, T::MaxBids>,
		who: &T::AccountId,
		value: BalanceOf<T, I>,
		bid_kind: BidKind<T::AccountId, BalanceOf<T, I>>,
	) {
		let pos = bids.iter().position(|bid| bid.value > value).unwrap_or(bids.len());
		let r = bids.force_insert_keep_left(pos, Bid { value, who: who.clone(), kind: bid_kind });
		let maybe_discarded = r.err().or_else(|| r.ok());
		if let Some(discarded) = maybe_discarded {
			Self::clean_bid(&discarded);
			Self::deposit_event(Event::<T, I>::AutoUnbid { candidate: discarded });
		}
	}

	/// Either unreserve the deposit or free up the vouching member.
	///
	/// In neither case can we do much if the action isn't completable, but there's
	/// no reason that either should fail.
	fn clean_bid(bid: &Bid<T::AccountId, BalanceOf<T, I>>) {
		match &bid.kind {
			BidKind::Deposit(deposit) => {
				let err_amount = T::Currency::unreserve(&bid.who, *deposit);
				debug_assert!(err_amount.is_zero());
			},
			BidKind::Vouch(voucher, _) => {
				Vouching::<T, I>::remove(voucher);
			},
		}
	}

	/// Check a user has a bid.
	fn has_bid(bids: &Vec<Bid<T::AccountId, BalanceOf<T, I>>>, who: &T::AccountId) -> bool {
		// Bids are ordered by `value`, so we cannot binary search for a user.
		bids.iter().any(|bid| bid.who == *who)
	}

	/// Add a member to the sorted members list. If the user is already a member, do nothing.
	/// Can fail when `MaxMember` limit is reached, but in that case it has no side-effects.
	///
	/// Set the `payouts` for the member. NOTE: This *WILL NOT RESERVE THE FUNDS TO MAKE THE
	/// PAYOUT*. Only set this to be non-empty if you already have the funds reserved in the Payouts
	/// account.
	///
	/// NOTE: Generally you should not use this, and instead use `add_new_member` or
	/// `reinstate_member`, whose names clearly match the desired intention.
	fn insert_member(who: &T::AccountId, rank: Rank, payouts: PayoutsFor<T>) -> DispatchResult {
		ensure!(MemberCount::get() < MaxMembers::<T, I>::get() as usize, Error::<T, I>::MaxMembers);
		let index = MemberCount::<T, I>::mutate(|i| { i.saturating_accrue(1); *i - 1 });
		let paid = Zero::zero();
		let record = MemberRecord { rank, strikes: 0, vouching: None, paid, index, payouts };
		Membership::<T, I>::insert(who, record);
		MemberByIndex::<T, I>::insert(index, who);
		Ok(())
	}

	/// Add a member back to the sorted members list, setting their `rank` and `payouts`.
	///
	/// Can fail when `MaxMember` limit is reached, but in that case it has no side-effects.
	///
	/// The `payouts` value must be exactly as it was prior to suspension since no further funds
	/// will be reserved.
	fn reinstate_member(who: &T::AccountId, rank: Rank, payouts: PayoutsFor<T>) -> DispatchResult {
		Self::insert_member(who, rank, payouts)
	}

	/// Add a member to the sorted members list. If the user is already a member, do nothing.
	/// Can fail when `MaxMember` limit is reached, but in that case it has no side-effects.
	fn add_new_member(who: &T::AccountId, rank: Rank) -> DispatchResult {
		Self::insert_member(who, rank, Default::default())
	}

	/// Induct a new member into the set.
	fn induct_member(
		candidate: T::AccountId,
		candidacy: Candidacy<T::AccountId, BalanceOf<T>>,
		rank: Rank,
	) -> DispatchResult {
		Self::check_skeptic(&candidate, &candidacy);
		Self::add_new_member(&candidate, 0)?;
		let next_head = NextHead::<T, I>::get()
			.filter(|old| old.round > candidacy.round
				|| old.round == candidacy.round && old.bid < candidacy.bid
			).unwrap_or_else(|| IntakeRecord { who: candidate.clone(), bid: candidacy.bid, round: candidacy.round });
		NextHead::<T, I>::put(next_head);
		let now = <frame_system::Pallet<T>>::block_number();
		let maturity = now + Self::lock_duration(MemberCount::<T, I>::get());
		Self::reward_bidder(&candidate, candidacy.bid, candidacy.kind, maturity);
		Votes::<T, I>::remove_prefix(&candidate, None);
		Candidate::<T, I>::remove(&candidate);
		Ok(())
	}

	fn strike_member(who: &T::AccountId) -> DispatchResult {
		let mut record = Membership::<T, I>::get(who).ok_or(NotMember)?;
		record.strikes.saturating_inc();
		if record.strikes >= T::GraceStrikes::get() {
			// Too many strikes: slash the payout in half.
			let total_payout = record.payouts.iter().map(|x| x.1).sum();
			Self::slash_payout(who, total_payout / 2u32.into());
		}
		if record.strikes >= T::MaxStrikes::get() {
			// Way too many strikes: suspend.
			Self::suspend_member(who);
		}
		Ok(())
	}

	/// Remove a member from the members list and return the candidacy.
	///
	/// If the member was vouching, then this will be reset. Any bidders that the member was
	/// vouching for will be cancelled unless they are already selected as candidates (in which case
	/// they will be able to stand).
	///
	/// If the member has existing payouts, they will be retained in the resultant `MemberRecord`
	/// and the funds will remain reserved.
	///
	/// The Head and the Founder may never be removed.
	pub fn remove_member(m: &T::AccountId) -> Result<MemberRecord, DispatchError> {
		ensure!(Head::<T, I>::get().as_ref() != Some(m), Error::<T, I>::Head);
		ensure!(Founder::<T, I>::get().as_ref() != Some(m), Error::<T, I>::Founder);
		if let Some(record) = Membership::<T, I>::get(m) {
			let index = record.index;
			let last_index = MemberCount::<T, I>::mutate(|i| { i.saturating_reduce(1); *i });
			if index != last_index {
				// Move the member with the last index down to the index of the member to be removed.
				if let Some(other) = MemberByIndex::<T, I>::get(last_index) {
					MemberByIndex::<T, I>::insert(index, other);
					Membership::<T, I>::mutate(other, |m_r|
						if let Some(r) = m_r { r.index = index }
					);
				} else {
					debug_assert!(false, "ERROR: No member at the last index position?");
				}
			}

			MemberByIndex::<T, I>::remove(last_index);
			Membership::<T, I>::remove(m);
			// Remove their vouching status, potentially unbanning them in the future.
			if record.vouching.take() == Some(VouchingStatus::Vouching) {
				// Try to remove their bid if they are vouching.
				// If their vouch is already a candidate, do nothing.
				Bids::<T, I>::mutate(|bids|
					// Try to find the matching bid
					if let Some(pos) = bids.iter().position(|b| b.kind.check_voucher(&who).is_ok()) {
						// Remove the bid, and emit an event
						let vouched = bids.remove(pos).who;
						Self::deposit_event(Event::<T, I>::Unvouch { candidate: vouched });
					}
				);
			}
			Ok(record)
		} else {
			Err(Error::<T, I>::NotMember.into())
		}
	}

	/// Remove a member from the members set and add them to the suspended members.
	///
	/// If the member was vouching, then this will be reset. Any bidders that the member was
	/// vouching for will be cancelled unless they are already selected as candidates (in which case
	/// they will be able to stand).
	fn suspend_member(who: &T::AccountId) {
		if let Ok(record) = Self::remove_member(&who) {
			SuspendedMembers::<T, I>::insert(who, record);
			Self::deposit_event(Event::<T, I>::MemberSuspended { member: who.clone() });
		}
	}

	/// Select a member at random, given the RNG `rng`.
	///
	/// If no members exist (or the state is inconsistent), then `None` may be returned.
	fn pick_member(rng: &mut impl RngCore) -> Option<T::AccountId> {
		let member_count = MemberCount::get();
		if member_count == 0 {
			return None
		}
		let random_index = rng.next_u32() % member_count;
		MemberByIndex::<T, I>::get(random_index)
	}

	/// Select a member at random except `exception`, given the RNG `rng`.
	///
	/// If `exception` is the only member (or the state is inconsistent), then `None` may be returned.
	fn pick_member_except(rng: &mut impl RngCore, exception: &T::AccountId) -> Option<T::AccountId> {
		let member_count = MemberCount::get();
		if member_count <= 1 {
			return None
		}
		let random_index = rng.next_u32() % (member_count - 1);
		let pick = MemberByIndex::<T, I>::get(random_index);
		if pick.as_ref() == Some(exception) {
			MemberByIndex::<T, I>::get(member_count - 1)
		} else {
			pick
		}
	}

	/// Select a member who is able to defend at random, given the RNG `rng`.
	///
	/// If only the Founder and Head members exist (or the state is inconsistent), then `None`
	/// may be returned.
	fn pick_defendent(rng: &mut impl RngCore) -> Option<T::AccountId> {
		let member_count = MemberCount::get();
		if member_count <= 2 {
			return None
		}
		// Founder is always at index 0, so we should never pick that one.
		// Head will typically but not always be the highest index. We assume it is for now and
		// fix it up later if not.
		let head = Head::<T, I>::get();
		let pickable_count = member_count - if head.is_some() { 2 } else { 1 };
		let random_index = rng.next_u32() % pickable_count + 1;
		let pick = MemberByIndex::<T, I>::get(random_index);
		if pick == head && head.is_some() {
			// Turns out that head was not the last index since we managed to pick it. Exchange our
			// pick for the last index.
			MemberByIndex::<T, I>::get(member_count - 1)
		} else {
			pick
		}
	}

	/// Pay an accepted candidate their bid value.
	fn reward_bidder(
		candidate: &T::AccountId,
		value: BalanceOf<T, I>,
		kind: BidKind<T::AccountId, BalanceOf<T, I>>,
		maturity: T::BlockNumber,
	) {
		let value = match kind {
			BidKind::Deposit(deposit) => {
				// In the case that a normal deposit bid is accepted we unreserve
				// the deposit.
				let err_amount = T::Currency::unreserve(candidate, deposit);
				debug_assert!(err_amount.is_zero());
				value
			},
			BidKind::Vouch(voucher, tip) => {
				// Check that the voucher is still vouching, else some other logic may have removed
				// their status.
				if Vouching::<T, I>::take(&voucher) == Some(VouchingStatus::Vouching) {
					// In the case that a vouched-for bid is accepted we unset the
					// vouching status and transfer the tip over to the voucher.
					Self::bump_payout(&voucher, maturity, tip.min(value));
					value.saturating_sub(tip)
				} else {
					value
				}
			},
		};

		Self::bump_payout(candidate, maturity, value);
	}

	/// Bump the payout amount of `who`, to be unlocked at the given block number.
	///
	/// If it the caller's duty to ensure that `who` is already a member. This does nothing if `who`
	/// is not a member or if `value` is zero.
	fn bump_payout(who: &T::AccountId, when: T::BlockNumber, value: BalanceOf<T, I>) {
		if !value.is_zero() {
			Membership::<T, I>::mutate(who, |maybe_record| if let Some(record) = maybe_record {
				if record.rank == 0 {
					// Members of rank 1 never get payouts.
					match record.payouts.binary_search_by_key(&when, |x| x.0) {
						Ok(index) => record.payouts[index].1.saturating_accrue(value),
						Err(index) => record.payouts.insert(index, (when, value)),
					}
				}
			});
			Self::reserve_payout(value);
		}
	}

	/// Attempt to slash the payout of some member. Return the total amount that was deducted.
	fn slash_payout(who: &T::AccountId, value: BalanceOf<T, I>) -> BalanceOf<T, I> {
		let mut record = match Membership::<T, I>::get(who) {
			Some(record) => record,
			None => return Zero::zero(),
		};
		let mut rest = value;
		while !record.payouts.is_empty() {
			if let Some(new_rest) = rest.checked_sub(&record.payouts[0].1) {
				// not yet totally slashed after this one; drop it completely.
				rest = new_rest;
				record.payouts.remove(0);
			} else {
				// whole slash is accounted for.
				record.payouts[0].1.saturating_reduce(rest);
				rest = Zero::zero();
				break
			}
		}
		Membership::<T, I>::insert(who, record);
		value - rest
	}

	/// Transfer some `amount` from the main account into the payouts account and reduce the Pot
	/// by this amount.
	fn reserve_payout(amount: BalanceOf<T>) {
		// Tramsfer payout from the Pot into the payouts account.
		Pot::<T, I>::mutate(|pot| pot.saturating_reduce(amount));

		// this should never fail since we ensure we can afford the payouts in a previous
		// block, but there's not much we can do to recover if it fails anyway.
		let res = T::Currency::transfer(
			&Self::account_id(),
			&Self::payouts(),
			amount,
			AllowDeath,
		);
		debug_assert!(res.is_ok());
	}

	/// Transfer some `amount` from the main account into the payouts account and increase the Pot
	/// by this amount.
	fn unreserve_payout(amount: BalanceOf<T>) {
		// Tramsfer payout from the Pot into the payouts account.
		Pot::<T, I>::mutate(|pot| pot.saturating_accrue(amount));

		// this should never fail since we ensure we can afford the payouts in a previous
		// block, but there's not much we can do to recover if it fails anyway.
		let res = T::Currency::transfer(
			&Self::payouts(),
			&Self::account_id(),
			amount,
			AllowDeath,
		);
		debug_assert!(res.is_ok());
	}

	/// The account ID of the treasury pot.
	///
	/// This actually does computation. If you need to keep using it, then make sure you cache the
	/// value and only call this once.
	pub fn account_id() -> T::AccountId {
		T::PalletId::get().into_account()
	}

	/// The account ID of the payouts pot. This is where payouts are made from.
	///
	/// This actually does computation. If you need to keep using it, then make sure you cache the
	/// value and only call this once.
	pub fn payouts() -> T::AccountId {
		T::PalletId::get().into_sub_account(b"payouts")
	}

	/// Return the duration of the lock, in blocks, with the given number of members.
	///
	/// This is a rather opaque calculation based on the formula here:
	/// https://www.desmos.com/calculator/9itkal1tce
	fn lock_duration(x: u32) -> T::BlockNumber {
		let lock_pc = 100 - 50_000 / (x + 500);
		Percent::from_percent(lock_pc as u8) * T::MaxLockDuration::get()
	}
}

impl<T: Config<I>, I: 'static> OnUnbalanced<NegativeImbalanceOf<T, I>> for Pallet<T, I> {
	fn on_nonzero_unbalanced(amount: NegativeImbalanceOf<T, I>) {
		let numeric_amount = amount.peek();

		// Must resolve into existing but better to be safe.
		let _ = T::Currency::resolve_creating(&Self::account_id(), amount);

		Self::deposit_event(Event::<T, I>::Deposit { value: numeric_amount });
	}
}
