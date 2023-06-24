// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;

pub mod weights;

pub mod migrations;

use frame_support::{
	impl_ensure_origin_with_arg_ignoring_arg,
	pallet_prelude::*,
	storage::KeyLenOf,
	traits::{
		BalanceStatus, Currency, EnsureOrigin, EnsureOriginWithArg,
		ExistenceRequirement::AllowDeath, Imbalance, OnUnbalanced, Randomness, ReservableCurrency,
		StorageVersion,
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
		AccountIdConversion, CheckedAdd, CheckedSub, Hash, Saturating, StaticLookup,
		TrailingZeroInput, Zero,
	},
	ArithmeticError::Overflow,
	Percent, RuntimeDebug,
};
use sp_std::prelude::*;

pub use weights::WeightInfo;

pub use pallet::*;

type BalanceOf<T, I> =
	<<T as Config<I>>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type NegativeImbalanceOf<T, I> = <<T as Config<I>>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;
type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
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

/// The number of votes.
pub type VoteCount = u32;

/// Tally of votes.
#[derive(Default, Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub struct Tally {
	/// The approval votes.
	approvals: VoteCount,
	/// The rejection votes.
	rejections: VoteCount,
}

impl Tally {
	fn more_approvals(&self) -> bool {
		self.approvals > self.rejections
	}

	fn more_rejections(&self) -> bool {
		self.rejections > self.approvals
	}

	fn clear_approval(&self) -> bool {
		self.approvals >= (2 * self.rejections).max(1)
	}

	fn clear_rejection(&self) -> bool {
		self.rejections >= (2 * self.approvals).max(1)
	}
}

/// A bid for entry into society.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub struct Candidacy<AccountId, Balance> {
	/// The index of the round where the candidacy began.
	round: RoundIndex,
	/// The kind of bid placed for this bidder/candidate. See `BidKind`.
	kind: BidKind<AccountId, Balance>,
	/// The reward that the bidder has requested for successfully joining the society.
	bid: Balance,
	/// The tally of votes so far.
	tally: Tally,
	/// True if the skeptic was already punished for note voting.
	skeptic_struck: bool,
}

/// A vote by a member on a candidate application.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub enum BidKind<AccountId, Balance> {
	/// The given deposit was paid for this bid.
	Deposit(Balance),
	/// A member vouched for this bid. The account should be reinstated into `Members` once the
	/// bid is successful (or if it is rescinded prior to launch).
	Vouch(AccountId, Balance),
}

impl<AccountId: PartialEq, Balance> BidKind<AccountId, Balance> {
	fn is_vouch(&self, v: &AccountId) -> bool {
		matches!(self, BidKind::Vouch(ref a, _) if a == v)
	}
}

pub type PayoutsFor<T, I> = BoundedVec<
	(<T as frame_system::Config>::BlockNumber, BalanceOf<T, I>),
	<T as Config<I>>::MaxPayouts,
>;

/// Information concerning a member.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub struct MemberRecord {
	rank: Rank,
	strikes: StrikeCount,
	vouching: Option<VouchingStatus>,
	index: u32,
}

/// Information concerning a member.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, Default)]
pub struct PayoutRecord<Balance, PayoutsVec> {
	paid: Balance,
	payouts: PayoutsVec,
}

pub type PayoutRecordFor<T, I> = PayoutRecord<
	BalanceOf<T, I>,
	BoundedVec<
		(<T as frame_system::Config>::BlockNumber, BalanceOf<T, I>),
		<T as Config<I>>::MaxPayouts,
	>,
>;

/// Record for an individual new member who was elevated from a candidate recently.
#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub struct IntakeRecord<AccountId, Balance> {
	who: AccountId,
	bid: Balance,
	round: RoundIndex,
}

pub type IntakeRecordFor<T, I> =
	IntakeRecord<<T as frame_system::Config>::AccountId, BalanceOf<T, I>>;

#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub struct GroupParams<Balance> {
	max_members: u32,
	max_intake: u32,
	max_strikes: u32,
	candidate_deposit: Balance,
}

pub type GroupParamsFor<T, I> = GroupParams<BalanceOf<T, I>>;

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	const STORAGE_VERSION: StorageVersion = StorageVersion::new(2);

	#[pallet::pallet]
	#[pallet::storage_version(STORAGE_VERSION)]
	#[pallet::without_storage_info]
	pub struct Pallet<T, I = ()>(_);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The societies's pallet id
		#[pallet::constant]
		type PalletId: Get<PalletId>;

		/// The currency type used for bidding.
		type Currency: ReservableCurrency<Self::AccountId>;

		/// Something that provides randomness in the runtime.
		type Randomness: Randomness<Self::Hash, Self::BlockNumber>;

		/// The maximum number of strikes before a member gets funds slashed.
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
		type FounderSetOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// The number of blocks between membership challenges.
		#[pallet::constant]
		type ChallengePeriod: Get<Self::BlockNumber>;

		/// The maximum number of payouts a member may have waiting unclaimed.
		#[pallet::constant]
		type MaxPayouts: Get<u32>;

		/// The maximum number of bids at once.
		#[pallet::constant]
		type MaxBids: Get<u32>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::error]
	pub enum Error<T, I = ()> {
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
		NotVouchingOnBidder,
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
		/// The membership cannot be claimed as the candidate was not clearly approved.
		NotApproved,
		/// The candidate cannot be kicked as the candidate was not clearly rejected.
		NotRejected,
		/// The candidacy cannot be dropped as the candidate was clearly approved.
		Approved,
		/// The candidacy cannot be bestowed as the candidate was clearly rejected.
		Rejected,
		/// The candidacy cannot be concluded as the voting is still in progress.
		InProgress,
		/// The candidacy cannot be pruned until a full additional intake period has passed.
		TooEarly,
		/// The skeptic already voted.
		Voted,
		/// The skeptic need not vote on candidates from expired rounds.
		Expired,
		/// User is not a bidder.
		NotBidder,
		/// There is no defender currently.
		NoDefender,
		/// Group doesn't exist.
		NotGroup,
		/// The member is already elevated to this rank.
		AlreadyElevated,
		/// The skeptic has already been punished for this offence.
		AlreadyPunished,
		/// Funds are insufficient to pay off society debts.
		InsufficientFunds,
		/// The candidate/defender has no stale votes to remove.
		NoVotes,
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
		/// A new set of \[params\] has been set for the group.
		NewParams { params: GroupParamsFor<T, I> },
		/// Society is unfounded.
		Unfounded { founder: T::AccountId },
		/// Some funds were deposited into the society account.
		Deposit { value: BalanceOf<T, I> },
		/// A \[member\] got elevated to \[rank\].
		Elevated { member: T::AccountId, rank: Rank },
	}

	/// Old name generated by `decl_event`.
	#[deprecated(note = "use `Event` instead")]
	pub type RawEvent<T, I = ()> = Event<T, I>;

	/// The max number of members for the society at one time.
	#[pallet::storage]
	pub(super) type Parameters<T: Config<I>, I: 'static = ()> =
		StorageValue<_, GroupParamsFor<T, I>, OptionQuery>;

	/// Amount of our account balance that is specifically for the next round's bid(s).
	#[pallet::storage]
	pub type Pot<T: Config<I>, I: 'static = ()> = StorageValue<_, BalanceOf<T, I>, ValueQuery>;

	/// The first member.
	#[pallet::storage]
	pub type Founder<T: Config<I>, I: 'static = ()> = StorageValue<_, T::AccountId>;

	/// The most primary from the most recently approved rank 0 members in the society.
	#[pallet::storage]
	pub type Head<T: Config<I>, I: 'static = ()> = StorageValue<_, T::AccountId>;

	/// A hash of the rules of this society concerning membership. Can only be set once and
	/// only by the founder.
	#[pallet::storage]
	pub type Rules<T: Config<I>, I: 'static = ()> = StorageValue<_, T::Hash>;

	/// The current members and their rank. Doesn't include `SuspendedMembers`.
	#[pallet::storage]
	pub type Members<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, T::AccountId, MemberRecord, OptionQuery>;

	/// Information regarding rank-0 payouts, past and future.
	#[pallet::storage]
	pub type Payouts<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, T::AccountId, PayoutRecordFor<T, I>, ValueQuery>;

	/// The number of items in `Members` currently. (Doesn't include `SuspendedMembers`.)
	#[pallet::storage]
	pub type MemberCount<T: Config<I>, I: 'static = ()> = StorageValue<_, u32, ValueQuery>;

	/// The current items in `Members` keyed by their unique index. Keys are densely populated
	/// `0..MemberCount` (does not include `MemberCount`).
	#[pallet::storage]
	pub type MemberByIndex<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, u32, T::AccountId, OptionQuery>;

	/// The set of suspended members, with their old membership record.
	#[pallet::storage]
	pub type SuspendedMembers<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, T::AccountId, MemberRecord, OptionQuery>;

	/// The number of rounds which have passed.
	#[pallet::storage]
	pub type RoundCount<T: Config<I>, I: 'static = ()> = StorageValue<_, RoundIndex, ValueQuery>;

	/// The current bids, stored ordered by the value of the bid.
	#[pallet::storage]
	pub(super) type Bids<T: Config<I>, I: 'static = ()> =
		StorageValue<_, BoundedVec<Bid<T::AccountId, BalanceOf<T, I>>, T::MaxBids>, ValueQuery>;

	#[pallet::storage]
	pub type Candidates<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Blake2_128Concat,
		T::AccountId,
		Candidacy<T::AccountId, BalanceOf<T, I>>,
		OptionQuery,
	>;

	/// The current skeptic.
	#[pallet::storage]
	pub type Skeptic<T: Config<I>, I: 'static = ()> = StorageValue<_, T::AccountId, OptionQuery>;

	/// Double map from Candidate -> Voter -> (Maybe) Vote.
	#[pallet::storage]
	pub(super) type Votes<T: Config<I>, I: 'static = ()> = StorageDoubleMap<
		_,
		Twox64Concat,
		T::AccountId,
		Twox64Concat,
		T::AccountId,
		Vote,
		OptionQuery,
	>;

	/// Clear-cursor for Vote, map from Candidate -> (Maybe) Cursor.
	#[pallet::storage]
	pub(super) type VoteClearCursor<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, T::AccountId, BoundedVec<u8, KeyLenOf<Votes<T, I>>>>;

	/// At the end of the claim period, this contains the most recently approved members (along with
	/// their bid and round ID) who is from the most recent round with the lowest bid. They will
	/// become the new `Head`.
	#[pallet::storage]
	pub type NextHead<T: Config<I>, I: 'static = ()> =
		StorageValue<_, IntakeRecordFor<T, I>, OptionQuery>;

	/// The number of challenge rounds there have been. Used to identify stale DefenderVotes.
	#[pallet::storage]
	pub(super) type ChallengeRoundCount<T: Config<I>, I: 'static = ()> =
		StorageValue<_, RoundIndex, ValueQuery>;

	/// The defending member currently being challenged, along with a running tally of votes.
	#[pallet::storage]
	pub(super) type Defending<T: Config<I>, I: 'static = ()> =
		StorageValue<_, (T::AccountId, T::AccountId, Tally)>;

	/// Votes for the defender, keyed by challenge round.
	#[pallet::storage]
	pub(super) type DefenderVotes<T: Config<I>, I: 'static = ()> =
		StorageDoubleMap<_, Twox64Concat, RoundIndex, Twox64Concat, T::AccountId, Vote>;

	#[pallet::hooks]
	impl<T: Config<I>, I: 'static> Hooks<BlockNumberFor<T>> for Pallet<T, I> {
		fn on_initialize(n: T::BlockNumber) -> Weight {
			let mut weight = Weight::zero();
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
				Period::Voting { elapsed, .. } if elapsed.is_zero() => {
					Self::rotate_intake(&mut rng);
					weight.saturating_accrue(weights.max_block / 20);
				},
				_ => {},
			}

			// Run a challenge rotation
			if (n % T::ChallengePeriod::get()).is_zero() {
				Self::rotate_challenge(&mut rng);
				weight.saturating_accrue(weights.max_block / 20);
			}

			weight
		}
	}

	#[pallet::genesis_config]
	#[derive(frame_support::DefaultNoBound)]
	pub struct GenesisConfig<T: Config<I>, I: 'static = ()> {
		pub pot: BalanceOf<T, I>,
	}

	#[pallet::genesis_build]
	impl<T: Config<I>, I: 'static> GenesisBuild<T, I> for GenesisConfig<T, I> {
		fn build(&self) {
			Pot::<T, I>::put(self.pot);
		}
	}

	#[pallet::call]
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// A user outside of the society can make a bid for entry.
		///
		/// Payment: The group's Candidate Deposit will be reserved for making a bid. It is returned
		/// when the bid becomes a member, or if the bid calls `unbid`.
		///
		/// The dispatch origin for this call must be _Signed_.
		///
		/// Parameters:
		/// - `value`: A one time payment the bid would like to receive when joining the society.
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::bid())]
		pub fn bid(origin: OriginFor<T>, value: BalanceOf<T, I>) -> DispatchResult {
			let who = ensure_signed(origin)?;

			let mut bids = Bids::<T, I>::get();
			ensure!(!Self::has_bid(&bids, &who), Error::<T, I>::AlreadyBid);
			ensure!(!Candidates::<T, I>::contains_key(&who), Error::<T, I>::AlreadyCandidate);
			ensure!(!Members::<T, I>::contains_key(&who), Error::<T, I>::AlreadyMember);
			ensure!(!SuspendedMembers::<T, I>::contains_key(&who), Error::<T, I>::Suspended);

			let params = Parameters::<T, I>::get().ok_or(Error::<T, I>::NotGroup)?;
			let deposit = params.candidate_deposit;
			// NOTE: Reserve must happen before `insert_bid` since that could end up unreserving.
			T::Currency::reserve(&who, deposit)?;
			Self::insert_bid(&mut bids, &who, value, BidKind::Deposit(deposit));

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
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::unbid())]
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
		#[pallet::call_index(2)]
		#[pallet::weight(T::WeightInfo::vouch())]
		pub fn vouch(
			origin: OriginFor<T>,
			who: AccountIdLookupOf<T>,
			value: BalanceOf<T, I>,
			tip: BalanceOf<T, I>,
		) -> DispatchResult {
			let voucher = ensure_signed(origin)?;
			let who = T::Lookup::lookup(who)?;

			// Get bids and check user is not bidding.
			let mut bids = Bids::<T, I>::get();
			ensure!(!Self::has_bid(&bids, &who), Error::<T, I>::AlreadyBid);

			// Check user is not already a candidate, member or suspended member.
			ensure!(!Candidates::<T, I>::contains_key(&who), Error::<T, I>::AlreadyCandidate);
			ensure!(!Members::<T, I>::contains_key(&who), Error::<T, I>::AlreadyMember);
			ensure!(!SuspendedMembers::<T, I>::contains_key(&who), Error::<T, I>::Suspended);

			// Check sender can vouch.
			let mut record = Members::<T, I>::get(&voucher).ok_or(Error::<T, I>::NotMember)?;
			ensure!(record.vouching.is_none(), Error::<T, I>::AlreadyVouching);

			// Update voucher record.
			record.vouching = Some(VouchingStatus::Vouching);
			// Update bids
			Self::insert_bid(&mut bids, &who, value, BidKind::Vouch(voucher.clone(), tip));

			// Write new state.
			Members::<T, I>::insert(&voucher, &record);
			Bids::<T, I>::put(bids);
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
		#[pallet::call_index(3)]
		#[pallet::weight(T::WeightInfo::unvouch())]
		pub fn unvouch(origin: OriginFor<T>) -> DispatchResult {
			let voucher = ensure_signed(origin)?;

			let mut bids = Bids::<T, I>::get();
			let pos = bids
				.iter()
				.position(|bid| bid.kind.is_vouch(&voucher))
				.ok_or(Error::<T, I>::NotVouchingOnBidder)?;
			let bid = bids.remove(pos);
			Self::clean_bid(&bid);

			Bids::<T, I>::put(bids);
			Self::deposit_event(Event::<T, I>::Unvouch { candidate: bid.who });
			Ok(())
		}

		/// As a member, vote on a candidate.
		///
		/// The dispatch origin for this call must be _Signed_ and a member.
		///
		/// Parameters:
		/// - `candidate`: The candidate that the member would like to bid on.
		/// - `approve`: A boolean which says if the candidate should be approved (`true`) or
		///   rejected (`false`).
		#[pallet::call_index(4)]
		#[pallet::weight(T::WeightInfo::vote())]
		pub fn vote(
			origin: OriginFor<T>,
			candidate: AccountIdLookupOf<T>,
			approve: bool,
		) -> DispatchResultWithPostInfo {
			let voter = ensure_signed(origin)?;
			let candidate = T::Lookup::lookup(candidate)?;

			let mut candidacy =
				Candidates::<T, I>::get(&candidate).ok_or(Error::<T, I>::NotCandidate)?;
			let record = Members::<T, I>::get(&voter).ok_or(Error::<T, I>::NotMember)?;

			let first_time = Votes::<T, I>::mutate(&candidate, &voter, |v| {
				let first_time = v.is_none();
				*v = Some(Self::do_vote(*v, approve, record.rank, &mut candidacy.tally));
				first_time
			});

			Candidates::<T, I>::insert(&candidate, &candidacy);
			Self::deposit_event(Event::<T, I>::Vote { candidate, voter, vote: approve });
			Ok(if first_time { Pays::No } else { Pays::Yes }.into())
		}

		/// As a member, vote on the defender.
		///
		/// The dispatch origin for this call must be _Signed_ and a member.
		///
		/// Parameters:
		/// - `approve`: A boolean which says if the candidate should be
		/// approved (`true`) or rejected (`false`).
		#[pallet::call_index(5)]
		#[pallet::weight(T::WeightInfo::defender_vote())]
		pub fn defender_vote(origin: OriginFor<T>, approve: bool) -> DispatchResultWithPostInfo {
			let voter = ensure_signed(origin)?;

			let mut defending = Defending::<T, I>::get().ok_or(Error::<T, I>::NoDefender)?;
			let record = Members::<T, I>::get(&voter).ok_or(Error::<T, I>::NotMember)?;

			let round = ChallengeRoundCount::<T, I>::get();
			let first_time = DefenderVotes::<T, I>::mutate(round, &voter, |v| {
				let first_time = v.is_none();
				*v = Some(Self::do_vote(*v, approve, record.rank, &mut defending.2));
				first_time
			});

			Defending::<T, I>::put(defending);
			Self::deposit_event(Event::<T, I>::DefenderVote { voter, vote: approve });
			Ok(if first_time { Pays::No } else { Pays::Yes }.into())
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
		#[pallet::call_index(6)]
		#[pallet::weight(T::WeightInfo::payout())]
		pub fn payout(origin: OriginFor<T>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(
				Members::<T, I>::get(&who).ok_or(Error::<T, I>::NotMember)?.rank == 0,
				Error::<T, I>::NoPayout
			);
			let mut record = Payouts::<T, I>::get(&who);

			if let Some((when, amount)) = record.payouts.first() {
				if when <= &<frame_system::Pallet<T>>::block_number() {
					record.paid = record.paid.checked_add(amount).ok_or(Overflow)?;
					T::Currency::transfer(&Self::payouts(), &who, *amount, AllowDeath)?;
					record.payouts.remove(0);
					Payouts::<T, I>::insert(&who, record);
					return Ok(())
				}
			}
			Err(Error::<T, I>::NoPayout)?
		}

		/// Repay the payment previously given to the member with the signed origin, remove any
		/// pending payments, and elevate them from rank 0 to rank 1.
		#[pallet::call_index(7)]
		#[pallet::weight(T::WeightInfo::waive_repay())]
		pub fn waive_repay(origin: OriginFor<T>, amount: BalanceOf<T, I>) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let mut record = Members::<T, I>::get(&who).ok_or(Error::<T, I>::NotMember)?;
			let mut payout_record = Payouts::<T, I>::get(&who);
			ensure!(record.rank == 0, Error::<T, I>::AlreadyElevated);
			ensure!(amount >= payout_record.paid, Error::<T, I>::InsufficientFunds);

			T::Currency::transfer(&who, &Self::account_id(), payout_record.paid, AllowDeath)?;
			payout_record.paid = Zero::zero();
			payout_record.payouts.clear();
			record.rank = 1;
			Members::<T, I>::insert(&who, record);
			Payouts::<T, I>::insert(&who, payout_record);
			Self::deposit_event(Event::<T, I>::Elevated { member: who, rank: 1 });

			Ok(())
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
		/// - `max_intake` - The maximum number of candidates per intake period.
		/// - `max_strikes`: The maximum number of strikes a member may get before they become
		///   suspended and may only be reinstated by the founder.
		/// - `candidate_deposit`: The deposit required to make a bid for membership of the group.
		/// - `rules` - The rules of this society concerning membership.
		///
		/// Complexity: O(1)
		#[pallet::call_index(8)]
		#[pallet::weight(T::WeightInfo::found_society())]
		pub fn found_society(
			origin: OriginFor<T>,
			founder: AccountIdLookupOf<T>,
			max_members: u32,
			max_intake: u32,
			max_strikes: u32,
			candidate_deposit: BalanceOf<T, I>,
			rules: Vec<u8>,
		) -> DispatchResult {
			T::FounderSetOrigin::ensure_origin(origin)?;
			let founder = T::Lookup::lookup(founder)?;
			ensure!(!Head::<T, I>::exists(), Error::<T, I>::AlreadyFounded);
			ensure!(max_members > 1, Error::<T, I>::MaxMembers);
			// This should never fail in the context of this function...
			let params = GroupParams { max_members, max_intake, max_strikes, candidate_deposit };
			Parameters::<T, I>::put(params);
			Self::insert_member(&founder, 1)?;
			Head::<T, I>::put(&founder);
			Founder::<T, I>::put(&founder);
			Rules::<T, I>::put(T::Hashing::hash(&rules));
			Self::deposit_event(Event::<T, I>::Founded { founder });
			Ok(())
		}

		/// Dissolve the society and remove all members.
		///
		/// The dispatch origin for this call must be Signed, and the signing account must be both
		/// the `Founder` and the `Head`. This implies that it may only be done when there is one
		/// member.
		#[pallet::call_index(9)]
		#[pallet::weight(T::WeightInfo::dissolve())]
		pub fn dissolve(origin: OriginFor<T>) -> DispatchResult {
			let founder = ensure_signed(origin)?;
			ensure!(Founder::<T, I>::get().as_ref() == Some(&founder), Error::<T, I>::NotFounder);
			ensure!(MemberCount::<T, I>::get() == 1, Error::<T, I>::NotHead);

			let _ = Members::<T, I>::clear(u32::MAX, None);
			MemberCount::<T, I>::kill();
			let _ = MemberByIndex::<T, I>::clear(u32::MAX, None);
			let _ = SuspendedMembers::<T, I>::clear(u32::MAX, None);
			let _ = Payouts::<T, I>::clear(u32::MAX, None);
			let _ = Votes::<T, I>::clear(u32::MAX, None);
			let _ = VoteClearCursor::<T, I>::clear(u32::MAX, None);
			Head::<T, I>::kill();
			NextHead::<T, I>::kill();
			Founder::<T, I>::kill();
			Rules::<T, I>::kill();
			Parameters::<T, I>::kill();
			Pot::<T, I>::kill();
			RoundCount::<T, I>::kill();
			Bids::<T, I>::kill();
			Skeptic::<T, I>::kill();
			ChallengeRoundCount::<T, I>::kill();
			Defending::<T, I>::kill();
			let _ = DefenderVotes::<T, I>::clear(u32::MAX, None);
			let _ = Candidates::<T, I>::clear(u32::MAX, None);
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
		/// The dispatch origin for this call must be Signed from the Founder.
		///
		/// Parameters:
		/// - `who` - The suspended member to be judged.
		/// - `forgive` - A boolean representing whether the suspension judgement origin forgives
		///   (`true`) or rejects (`false`) a suspended member.
		#[pallet::call_index(10)]
		#[pallet::weight(T::WeightInfo::judge_suspended_member())]
		pub fn judge_suspended_member(
			origin: OriginFor<T>,
			who: AccountIdLookupOf<T>,
			forgive: bool,
		) -> DispatchResultWithPostInfo {
			ensure!(
				Some(ensure_signed(origin)?) == Founder::<T, I>::get(),
				Error::<T, I>::NotFounder
			);
			let who = T::Lookup::lookup(who)?;
			let record = SuspendedMembers::<T, I>::get(&who).ok_or(Error::<T, I>::NotSuspended)?;
			if forgive {
				// Try to add member back to society. Can fail with `MaxMembers` limit.
				Self::reinstate_member(&who, record.rank)?;
			} else {
				let payout_record = Payouts::<T, I>::take(&who);
				let total = payout_record
					.payouts
					.into_iter()
					.map(|x| x.1)
					.fold(Zero::zero(), |acc: BalanceOf<T, I>, x| acc.saturating_add(x));
				Self::unreserve_payout(total);
			}
			SuspendedMembers::<T, I>::remove(&who);
			Self::deposit_event(Event::<T, I>::SuspendedMemberJudgement { who, judged: forgive });
			Ok(Pays::No.into())
		}

		/// Change the maximum number of members in society and the maximum number of new candidates
		/// in a single intake period.
		///
		/// The dispatch origin for this call must be Signed by the Founder.
		///
		/// Parameters:
		/// - `max_members` - The maximum number of members for the society. This must be no less
		///   than the current number of members.
		/// - `max_intake` - The maximum number of candidates per intake period.
		/// - `max_strikes`: The maximum number of strikes a member may get before they become
		///   suspended and may only be reinstated by the founder.
		/// - `candidate_deposit`: The deposit required to make a bid for membership of the group.
		#[pallet::call_index(11)]
		#[pallet::weight(T::WeightInfo::set_parameters())]
		pub fn set_parameters(
			origin: OriginFor<T>,
			max_members: u32,
			max_intake: u32,
			max_strikes: u32,
			candidate_deposit: BalanceOf<T, I>,
		) -> DispatchResult {
			ensure!(
				Some(ensure_signed(origin)?) == Founder::<T, I>::get(),
				Error::<T, I>::NotFounder
			);
			ensure!(max_members >= MemberCount::<T, I>::get(), Error::<T, I>::MaxMembers);
			let params = GroupParams { max_members, max_intake, max_strikes, candidate_deposit };
			Parameters::<T, I>::put(&params);
			Self::deposit_event(Event::<T, I>::NewParams { params });
			Ok(())
		}

		/// Punish the skeptic with a strike if they did not vote on a candidate. Callable by the
		/// candidate.
		#[pallet::call_index(12)]
		#[pallet::weight(T::WeightInfo::punish_skeptic())]
		pub fn punish_skeptic(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let candidate = ensure_signed(origin)?;
			let mut candidacy =
				Candidates::<T, I>::get(&candidate).ok_or(Error::<T, I>::NotCandidate)?;
			ensure!(!candidacy.skeptic_struck, Error::<T, I>::AlreadyPunished);
			ensure!(!Self::in_progress(candidacy.round), Error::<T, I>::InProgress);
			let punished = Self::check_skeptic(&candidate, &mut candidacy);
			Candidates::<T, I>::insert(&candidate, candidacy);
			Ok(if punished { Pays::No } else { Pays::Yes }.into())
		}

		/// Transform an approved candidate into a member. Callable only by the
		/// the candidate, and only after the period for voting has ended.
		#[pallet::call_index(13)]
		#[pallet::weight(T::WeightInfo::claim_membership())]
		pub fn claim_membership(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let candidate = ensure_signed(origin)?;
			let candidacy =
				Candidates::<T, I>::get(&candidate).ok_or(Error::<T, I>::NotCandidate)?;
			ensure!(candidacy.tally.clear_approval(), Error::<T, I>::NotApproved);
			ensure!(!Self::in_progress(candidacy.round), Error::<T, I>::InProgress);
			Self::induct_member(candidate, candidacy, 0)?;
			Ok(Pays::No.into())
		}

		/// Transform an approved candidate into a member. Callable only by the Signed origin of the
		/// Founder, only after the period for voting has ended and only when the candidate is not
		/// clearly rejected.
		#[pallet::call_index(14)]
		#[pallet::weight(T::WeightInfo::bestow_membership())]
		pub fn bestow_membership(
			origin: OriginFor<T>,
			candidate: T::AccountId,
		) -> DispatchResultWithPostInfo {
			ensure!(
				Some(ensure_signed(origin)?) == Founder::<T, I>::get(),
				Error::<T, I>::NotFounder
			);
			let candidacy =
				Candidates::<T, I>::get(&candidate).ok_or(Error::<T, I>::NotCandidate)?;
			ensure!(!candidacy.tally.clear_rejection(), Error::<T, I>::Rejected);
			ensure!(!Self::in_progress(candidacy.round), Error::<T, I>::InProgress);
			Self::induct_member(candidate, candidacy, 0)?;
			Ok(Pays::No.into())
		}

		/// Remove the candidate's application from the society. Callable only by the Signed origin
		/// of the Founder, only after the period for voting has ended, and only when they do not
		/// have a clear approval.
		///
		/// Any bid deposit is lost and voucher is banned.
		#[pallet::call_index(15)]
		#[pallet::weight(T::WeightInfo::kick_candidate())]
		pub fn kick_candidate(
			origin: OriginFor<T>,
			candidate: T::AccountId,
		) -> DispatchResultWithPostInfo {
			ensure!(
				Some(ensure_signed(origin)?) == Founder::<T, I>::get(),
				Error::<T, I>::NotFounder
			);
			let mut candidacy =
				Candidates::<T, I>::get(&candidate).ok_or(Error::<T, I>::NotCandidate)?;
			ensure!(!Self::in_progress(candidacy.round), Error::<T, I>::InProgress);
			ensure!(!candidacy.tally.clear_approval(), Error::<T, I>::Approved);
			Self::check_skeptic(&candidate, &mut candidacy);
			Self::reject_candidate(&candidate, &candidacy.kind);
			Candidates::<T, I>::remove(&candidate);
			Ok(Pays::No.into())
		}

		/// Remove the candidate's application from the society. Callable only by the candidate.
		///
		/// Any bid deposit is lost and voucher is banned.
		#[pallet::call_index(16)]
		#[pallet::weight(T::WeightInfo::resign_candidacy())]
		pub fn resign_candidacy(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let candidate = ensure_signed(origin)?;
			let mut candidacy =
				Candidates::<T, I>::get(&candidate).ok_or(Error::<T, I>::NotCandidate)?;
			if !Self::in_progress(candidacy.round) {
				Self::check_skeptic(&candidate, &mut candidacy);
			}
			Self::reject_candidate(&candidate, &candidacy.kind);
			Candidates::<T, I>::remove(&candidate);
			Ok(Pays::No.into())
		}

		/// Remove a `candidate`'s failed application from the society. Callable by any
		/// signed origin but only at the end of the subsequent round and only for
		/// a candidate with more rejections than approvals.
		///
		/// The bid deposit is lost and the voucher is banned.
		#[pallet::call_index(17)]
		#[pallet::weight(T::WeightInfo::drop_candidate())]
		pub fn drop_candidate(
			origin: OriginFor<T>,
			candidate: T::AccountId,
		) -> DispatchResultWithPostInfo {
			ensure_signed(origin)?;
			let candidacy =
				Candidates::<T, I>::get(&candidate).ok_or(Error::<T, I>::NotCandidate)?;
			ensure!(candidacy.tally.clear_rejection(), Error::<T, I>::NotRejected);
			ensure!(RoundCount::<T, I>::get() > candidacy.round + 1, Error::<T, I>::TooEarly);
			Self::reject_candidate(&candidate, &candidacy.kind);
			Candidates::<T, I>::remove(&candidate);
			Ok(Pays::No.into())
		}

		/// Remove up to `max` stale votes for the given `candidate`.
		///
		/// May be called by any Signed origin, but only after the candidate's candidacy is ended.
		#[pallet::call_index(18)]
		#[pallet::weight(T::WeightInfo::cleanup_candidacy())]
		pub fn cleanup_candidacy(
			origin: OriginFor<T>,
			candidate: T::AccountId,
			max: u32,
		) -> DispatchResultWithPostInfo {
			ensure_signed(origin)?;
			ensure!(!Candidates::<T, I>::contains_key(&candidate), Error::<T, I>::InProgress);
			let maybe_cursor = VoteClearCursor::<T, I>::get(&candidate);
			let r =
				Votes::<T, I>::clear_prefix(&candidate, max, maybe_cursor.as_ref().map(|x| &x[..]));
			if let Some(cursor) = r.maybe_cursor {
				VoteClearCursor::<T, I>::insert(&candidate, BoundedVec::truncate_from(cursor));
			}
			Ok(if r.loops == 0 { Pays::Yes } else { Pays::No }.into())
		}

		/// Remove up to `max` stale votes for the defender in the given `challenge_round`.
		///
		/// May be called by any Signed origin, but only after the challenge round is ended.
		#[pallet::call_index(19)]
		#[pallet::weight(T::WeightInfo::cleanup_challenge())]
		pub fn cleanup_challenge(
			origin: OriginFor<T>,
			challenge_round: RoundIndex,
			max: u32,
		) -> DispatchResultWithPostInfo {
			ensure_signed(origin)?;
			ensure!(
				challenge_round < ChallengeRoundCount::<T, I>::get(),
				Error::<T, I>::InProgress
			);
			let _ = DefenderVotes::<T, I>::clear_prefix(challenge_round, max, None);
			// clear_prefix() v2 is always returning backend = 0, ignoring it till v3.
			// let (_, backend, _, _) = r.deconstruct();
			// if backend == 0 { return Err(Error::<T, I>::NoVotes.into()); };
			Ok(Pays::No.into())
		}
	}
}

/// Simple ensure origin struct to filter for the founder account.
pub struct EnsureFounder<T>(sp_std::marker::PhantomData<T>);
impl<T: Config> EnsureOrigin<<T as frame_system::Config>::RuntimeOrigin> for EnsureFounder<T> {
	type Success = T::AccountId;
	fn try_origin(o: T::RuntimeOrigin) -> Result<Self::Success, T::RuntimeOrigin> {
		o.into().and_then(|o| match (o, Founder::<T>::get()) {
			(frame_system::RawOrigin::Signed(ref who), Some(ref f)) if who == f => Ok(who.clone()),
			(r, _) => Err(T::RuntimeOrigin::from(r)),
		})
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<T::RuntimeOrigin, ()> {
		let founder = Founder::<T>::get().ok_or(())?;
		Ok(T::RuntimeOrigin::from(frame_system::RawOrigin::Signed(founder)))
	}
}

impl_ensure_origin_with_arg_ignoring_arg! {
	impl<{ T: Config, A }>
		EnsureOriginWithArg<T::RuntimeOrigin, A> for EnsureFounder<T>
	{}
}

struct InputFromRng<'a, T>(&'a mut T);
impl<'a, T: RngCore> codec::Input for InputFromRng<'a, T> {
	fn remaining_len(&mut self) -> Result<Option<usize>, codec::Error> {
		return Ok(None)
	}

	fn read(&mut self, into: &mut [u8]) -> Result<(), codec::Error> {
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
		let now = frame_system::Pallet::<T>::block_number();
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
		target_round == round && matches!(Self::period(), Period::Voting { .. })
	}

	/// Returns the new vote.
	fn do_vote(maybe_old: Option<Vote>, approve: bool, rank: Rank, tally: &mut Tally) -> Vote {
		match maybe_old {
			Some(Vote { approve: true, weight }) => tally.approvals.saturating_reduce(weight),
			Some(Vote { approve: false, weight }) => tally.rejections.saturating_reduce(weight),
			_ => {},
		}
		let weight_root = rank + 1;
		let weight = weight_root * weight_root;
		match approve {
			true => tally.approvals.saturating_accrue(1),
			false => tally.rejections.saturating_accrue(1),
		}
		Vote { approve, weight }
	}

	/// Returns `true` if a punishment was given.
	fn check_skeptic(
		candidate: &T::AccountId,
		candidacy: &mut Candidacy<T::AccountId, BalanceOf<T, I>>,
	) -> bool {
		if RoundCount::<T, I>::get() != candidacy.round || candidacy.skeptic_struck {
			return false
		}
		// We expect the skeptic to have voted.
		let skeptic = match Skeptic::<T, I>::get() {
			Some(s) => s,
			None => return false,
		};
		let maybe_vote = Votes::<T, I>::get(&candidate, &skeptic);
		let approved = candidacy.tally.clear_approval();
		let rejected = candidacy.tally.clear_rejection();
		match (maybe_vote, approved, rejected) {
			(None, _, _) |
			(Some(Vote { approve: true, .. }), false, true) |
			(Some(Vote { approve: false, .. }), true, false) => {
				// Can't do much if the punishment doesn't work out.
				if Self::strike_member(&skeptic).is_ok() {
					candidacy.skeptic_struck = true;
					true
				} else {
					false
				}
			},
			_ => false,
		}
	}

	/// End the current challenge period and start a new one.
	fn rotate_challenge(rng: &mut impl RngCore) {
		let mut next_defender = None;
		let mut round = ChallengeRoundCount::<T, I>::get();

		// End current defender rotation
		if let Some((defender, skeptic, tally)) = Defending::<T, I>::get() {
			// We require strictly more approvals, since the member should be voting for themselves.
			if !tally.more_approvals() {
				// Member has failed the challenge: Suspend them. This will fail if they are Head
				// or Founder, in which case we ignore.
				let _ = Self::suspend_member(&defender);
			}

			// Check defender skeptic voted and that their vote was with the majority.
			let skeptic_vote = DefenderVotes::<T, I>::get(round, &skeptic);
			match (skeptic_vote, tally.more_approvals(), tally.more_rejections()) {
				(None, _, _) |
				(Some(Vote { approve: true, .. }), false, true) |
				(Some(Vote { approve: false, .. }), true, false) => {
					// Punish skeptic and challenge them next.
					let _ = Self::strike_member(&skeptic);
					let founder = Founder::<T, I>::get();
					let head = Head::<T, I>::get();
					if Some(&skeptic) != founder.as_ref() && Some(&skeptic) != head.as_ref() {
						next_defender = Some(skeptic);
					}
				},
				_ => {},
			}
			round.saturating_inc();
			ChallengeRoundCount::<T, I>::put(round);
		}

		// Avoid challenging if there's only two members since we never challenge the Head or
		// the Founder.
		if MemberCount::<T, I>::get() > 2 {
			let defender = next_defender
				.or_else(|| Self::pick_defendent(rng))
				.expect("exited if members empty; qed");
			let skeptic =
				Self::pick_member_except(rng, &defender).expect("exited if members empty; qed");
			Self::deposit_event(Event::<T, I>::Challenged { member: defender.clone() });
			Defending::<T, I>::put((defender, skeptic, Tally::default()));
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
		let member_count = MemberCount::<T, I>::get();
		if member_count < 1 {
			return
		}
		let maybe_head = NextHead::<T, I>::take();
		if let Some(head) = maybe_head {
			Head::<T, I>::put(&head.who);
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
			let skeptic = Self::pick_member(rng).expect("exited if members empty; qed");
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
	) -> u32 {
		// Get the number of left-most bidders whose bids add up to less than `pot`.
		let mut bids = Bids::<T, I>::get();
		let params = match Parameters::<T, I>::get() {
			Some(params) => params,
			None => return 0,
		};
		let max_selections: u32 = params
			.max_intake
			.min(params.max_members.saturating_sub(member_count))
			.min(bids.len() as u32);

		let mut selections = 0;
		// A running total of the cost to onboard these bids
		let mut total_cost: BalanceOf<T, I> = Zero::zero();

		bids.retain(|bid| {
			// We only accept a zero bid as the first selection.
			total_cost.saturating_accrue(bid.value);
			let accept = selections < max_selections &&
				(!bid.value.is_zero() || selections == 0) &&
				total_cost <= pot;
			if accept {
				let candidacy = Candidacy {
					round,
					kind: bid.kind.clone(),
					bid: bid.value,
					tally: Default::default(),
					skeptic_struck: false,
				};
				Candidates::<T, I>::insert(&bid.who, candidacy);
				selections.saturating_inc();
			}
			!accept
		});

		// No need to reset Bids if we're not taking anything.
		Bids::<T, I>::put(&bids);
		selections
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
		let maybe_discarded = match r {
			Ok(x) => x,
			Err(x) => Some(x),
		};
		if let Some(discarded) = maybe_discarded {
			Self::clean_bid(&discarded);
			Self::deposit_event(Event::<T, I>::AutoUnbid { candidate: discarded.who });
		}
	}

	/// Either unreserve the deposit or free up the vouching member.
	///
	/// In neither case can we do much if the action isn't completable, but there's
	/// no reason that either should fail.
	///
	/// WARNING: This alters the voucher item of `Members`. You must ensure that you do not
	/// accidentally overwrite it with an older value after calling this.
	fn clean_bid(bid: &Bid<T::AccountId, BalanceOf<T, I>>) {
		match &bid.kind {
			BidKind::Deposit(deposit) => {
				let err_amount = T::Currency::unreserve(&bid.who, *deposit);
				debug_assert!(err_amount.is_zero());
			},
			BidKind::Vouch(voucher, _) => {
				Members::<T, I>::mutate_extant(voucher, |record| record.vouching = None);
			},
		}
	}

	/// Either repatriate the deposit into the Society account or ban the vouching member.
	///
	/// In neither case can we do much if the action isn't completable, but there's
	/// no reason that either should fail.
	///
	/// WARNING: This alters the voucher item of `Members`. You must ensure that you do not
	/// accidentally overwrite it with an older value after calling this.
	fn reject_candidate(who: &T::AccountId, kind: &BidKind<T::AccountId, BalanceOf<T, I>>) {
		match kind {
			BidKind::Deposit(deposit) => {
				let pot = Self::account_id();
				let free = BalanceStatus::Free;
				let r = T::Currency::repatriate_reserved(&who, &pot, *deposit, free);
				debug_assert!(r.is_ok());
			},
			BidKind::Vouch(voucher, _) => {
				Members::<T, I>::mutate_extant(voucher, |record| {
					record.vouching = Some(VouchingStatus::Banned)
				});
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
	fn insert_member(who: &T::AccountId, rank: Rank) -> DispatchResult {
		let params = Parameters::<T, I>::get().ok_or(Error::<T, I>::NotGroup)?;
		ensure!(MemberCount::<T, I>::get() < params.max_members, Error::<T, I>::MaxMembers);
		let index = MemberCount::<T, I>::mutate(|i| {
			i.saturating_accrue(1);
			*i - 1
		});
		let record = MemberRecord { rank, strikes: 0, vouching: None, index };
		Members::<T, I>::insert(who, record);
		MemberByIndex::<T, I>::insert(index, who);
		Ok(())
	}

	/// Add a member back to the sorted members list, setting their `rank` and `payouts`.
	///
	/// Can fail when `MaxMember` limit is reached, but in that case it has no side-effects.
	///
	/// The `payouts` value must be exactly as it was prior to suspension since no further funds
	/// will be reserved.
	fn reinstate_member(who: &T::AccountId, rank: Rank) -> DispatchResult {
		Self::insert_member(who, rank)
	}

	/// Add a member to the sorted members list. If the user is already a member, do nothing.
	/// Can fail when `MaxMember` limit is reached, but in that case it has no side-effects.
	fn add_new_member(who: &T::AccountId, rank: Rank) -> DispatchResult {
		Self::insert_member(who, rank)
	}

	/// Induct a new member into the set.
	fn induct_member(
		candidate: T::AccountId,
		mut candidacy: Candidacy<T::AccountId, BalanceOf<T, I>>,
		rank: Rank,
	) -> DispatchResult {
		Self::add_new_member(&candidate, rank)?;
		Self::check_skeptic(&candidate, &mut candidacy);

		let next_head = NextHead::<T, I>::get()
			.filter(|old| {
				old.round > candidacy.round ||
					old.round == candidacy.round && old.bid < candidacy.bid
			})
			.unwrap_or_else(|| IntakeRecord {
				who: candidate.clone(),
				bid: candidacy.bid,
				round: candidacy.round,
			});
		NextHead::<T, I>::put(next_head);

		let now = <frame_system::Pallet<T>>::block_number();
		let maturity = now + Self::lock_duration(MemberCount::<T, I>::get());
		Self::reward_bidder(&candidate, candidacy.bid, candidacy.kind, maturity);

		Candidates::<T, I>::remove(&candidate);
		Ok(())
	}

	fn strike_member(who: &T::AccountId) -> DispatchResult {
		let mut record = Members::<T, I>::get(who).ok_or(Error::<T, I>::NotMember)?;
		record.strikes.saturating_inc();
		Members::<T, I>::insert(who, &record);
		// ^^^ Keep the member record mutation self-contained as we might be suspending them later
		// in this function.

		if record.strikes >= T::GraceStrikes::get() {
			// Too many strikes: slash the payout in half.
			let total_payout = Payouts::<T, I>::get(who)
				.payouts
				.iter()
				.fold(BalanceOf::<T, I>::zero(), |acc, x| acc.saturating_add(x.1));
			Self::slash_payout(who, total_payout / 2u32.into());
		}

		let params = Parameters::<T, I>::get().ok_or(Error::<T, I>::NotGroup)?;
		if record.strikes >= params.max_strikes {
			// Way too many strikes: suspend.
			let _ = Self::suspend_member(who);
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
		if let Some(mut record) = Members::<T, I>::get(m) {
			let index = record.index;
			let last_index = MemberCount::<T, I>::mutate(|i| {
				i.saturating_reduce(1);
				*i
			});
			if index != last_index {
				// Move the member with the last index down to the index of the member to be
				// removed.
				if let Some(other) = MemberByIndex::<T, I>::get(last_index) {
					MemberByIndex::<T, I>::insert(index, &other);
					Members::<T, I>::mutate(other, |m_r| {
						if let Some(r) = m_r {
							r.index = index
						}
					});
				} else {
					debug_assert!(false, "ERROR: No member at the last index position?");
				}
			}

			MemberByIndex::<T, I>::remove(last_index);
			Members::<T, I>::remove(m);
			// Remove their vouching status, potentially unbanning them in the future.
			if record.vouching.take() == Some(VouchingStatus::Vouching) {
				// Try to remove their bid if they are vouching.
				// If their vouch is already a candidate, do nothing.
				Bids::<T, I>::mutate(|bids|
					// Try to find the matching bid
					if let Some(pos) = bids.iter().position(|b| b.kind.is_vouch(&m)) {
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
	fn suspend_member(who: &T::AccountId) -> DispatchResult {
		let record = Self::remove_member(&who)?;
		SuspendedMembers::<T, I>::insert(who, record);
		Self::deposit_event(Event::<T, I>::MemberSuspended { member: who.clone() });
		Ok(())
	}

	/// Select a member at random, given the RNG `rng`.
	///
	/// If no members exist (or the state is inconsistent), then `None` may be returned.
	fn pick_member(rng: &mut impl RngCore) -> Option<T::AccountId> {
		let member_count = MemberCount::<T, I>::get();
		if member_count == 0 {
			return None
		}
		let random_index = rng.next_u32() % member_count;
		MemberByIndex::<T, I>::get(random_index)
	}

	/// Select a member at random except `exception`, given the RNG `rng`.
	///
	/// If `exception` is the only member (or the state is inconsistent), then `None` may be
	/// returned.
	fn pick_member_except(
		rng: &mut impl RngCore,
		exception: &T::AccountId,
	) -> Option<T::AccountId> {
		let member_count = MemberCount::<T, I>::get();
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
		let member_count = MemberCount::<T, I>::get();
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
				if let Some(mut record) = Members::<T, I>::get(&voucher) {
					if let Some(VouchingStatus::Vouching) = record.vouching {
						// In the case that a vouched-for bid is accepted we unset the
						// vouching status and transfer the tip over to the voucher.
						record.vouching = None;
						Self::bump_payout(&voucher, maturity, tip.min(value));
						Members::<T, I>::insert(&voucher, record);
						value.saturating_sub(tip)
					} else {
						value
					}
				} else {
					value
				}
			},
		};

		Self::bump_payout(candidate, maturity, value);
	}

	/// Bump the payout amount of `who`, to be unlocked at the given block number.
	///
	/// It is the caller's duty to ensure that `who` is already a member. This does nothing if `who`
	/// is not a member or if `value` is zero.
	fn bump_payout(who: &T::AccountId, when: T::BlockNumber, value: BalanceOf<T, I>) {
		if value.is_zero() {
			return
		}
		if let Some(MemberRecord { rank: 0, .. }) = Members::<T, I>::get(who) {
			Payouts::<T, I>::mutate(who, |record| {
				// Members of rank 1 never get payouts.
				match record.payouts.binary_search_by_key(&when, |x| x.0) {
					Ok(index) => record.payouts[index].1.saturating_accrue(value),
					Err(index) => {
						// If they have too many pending payouts, then we take discard the payment.
						let _ = record.payouts.try_insert(index, (when, value));
					},
				}
			});
			Self::reserve_payout(value);
		}
	}

	/// Attempt to slash the payout of some member. Return the total amount that was deducted.
	fn slash_payout(who: &T::AccountId, value: BalanceOf<T, I>) -> BalanceOf<T, I> {
		let mut record = Payouts::<T, I>::get(who);
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
		Payouts::<T, I>::insert(who, record);
		value - rest
	}

	/// Transfer some `amount` from the main account into the payouts account and reduce the Pot
	/// by this amount.
	fn reserve_payout(amount: BalanceOf<T, I>) {
		// Tramsfer payout from the Pot into the payouts account.
		Pot::<T, I>::mutate(|pot| pot.saturating_reduce(amount));

		// this should never fail since we ensure we can afford the payouts in a previous
		// block, but there's not much we can do to recover if it fails anyway.
		let res = T::Currency::transfer(&Self::account_id(), &Self::payouts(), amount, AllowDeath);
		debug_assert!(res.is_ok());
	}

	/// Transfer some `amount` from the main account into the payouts account and increase the Pot
	/// by this amount.
	fn unreserve_payout(amount: BalanceOf<T, I>) {
		// Tramsfer payout from the Pot into the payouts account.
		Pot::<T, I>::mutate(|pot| pot.saturating_accrue(amount));

		// this should never fail since we ensure we can afford the payouts in a previous
		// block, but there's not much we can do to recover if it fails anyway.
		let res = T::Currency::transfer(&Self::payouts(), &Self::account_id(), amount, AllowDeath);
		debug_assert!(res.is_ok());
	}

	/// The account ID of the treasury pot.
	///
	/// This actually does computation. If you need to keep using it, then make sure you cache the
	/// value and only call this once.
	pub fn account_id() -> T::AccountId {
		T::PalletId::get().into_account_truncating()
	}

	/// The account ID of the payouts pot. This is where payouts are made from.
	///
	/// This actually does computation. If you need to keep using it, then make sure you cache the
	/// value and only call this once.
	pub fn payouts() -> T::AccountId {
		T::PalletId::get().into_sub_account_truncating(b"payouts")
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
