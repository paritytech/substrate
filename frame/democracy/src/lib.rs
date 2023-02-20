// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! # Democracy Pallet
//!
//! - [`Config`]
//! - [`Call`]
//!
//! ## Overview
//!
//! The Democracy pallet handles the administration of general stakeholder voting.
//!
//! There are two different queues that a proposal can be added to before it
//! becomes a referendum, 1) the proposal queue consisting of all public proposals
//! and 2) the external queue consisting of a single proposal that originates
//! from one of the _external_ origins (such as a collective group).
//!
//! Every launch period - a length defined in the runtime - the Democracy pallet
//! launches a referendum from a proposal that it takes from either the proposal
//! queue or the external queue in turn. Any token holder in the system can vote
//! on referenda. The voting system
//! uses time-lock voting by allowing the token holder to set their _conviction_
//! behind a vote. The conviction will dictate the length of time the tokens
//! will be locked, as well as the multiplier that scales the vote power.
//!
//! ### Terminology
//!
//! - **Enactment Period:** The minimum period of locking and the period between a proposal being
//! approved and enacted.
//! - **Lock Period:** A period of time after proposal enactment that the tokens of _winning_ voters
//! will be locked.
//! - **Conviction:** An indication of a voter's strength of belief in their vote. An increase
//! of one in conviction indicates that a token holder is willing to lock their tokens for twice
//! as many lock periods after enactment.
//! - **Vote:** A value that can either be in approval ("Aye") or rejection ("Nay") of a particular
//!   referendum.
//! - **Proposal:** A submission to the chain that represents an action that a proposer (either an
//! account or an external origin) suggests that the system adopt.
//! - **Referendum:** A proposal that is in the process of being voted on for either acceptance or
//!   rejection as a change to the system.
//! - **Delegation:** The act of granting your voting power to the decisions of another account for
//!   up to a certain conviction.
//!
//! ### Adaptive Quorum Biasing
//!
//! A _referendum_ can be either simple majority-carries in which 50%+1 of the
//! votes decide the outcome or _adaptive quorum biased_. Adaptive quorum biasing
//! makes the threshold for passing or rejecting a referendum higher or lower
//! depending on how the referendum was originally proposed. There are two types of
//! adaptive quorum biasing: 1) _positive turnout bias_ makes a referendum
//! require a super-majority to pass that decreases as turnout increases and
//! 2) _negative turnout bias_ makes a referendum require a super-majority to
//! reject that decreases as turnout increases. Another way to think about the
//! quorum biasing is that _positive bias_ referendums will be rejected by
//! default and _negative bias_ referendums get passed by default.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! #### Public
//!
//! These calls can be made from any externally held account capable of creating
//! a signed extrinsic.
//!
//! Basic actions:
//! - `propose` - Submits a sensitive action, represented as a hash. Requires a deposit.
//! - `second` - Signals agreement with a proposal, moves it higher on the proposal queue, and
//!   requires a matching deposit to the original.
//! - `vote` - Votes in a referendum, either the vote is "Aye" to enact the proposal or "Nay" to
//!   keep the status quo.
//! - `unvote` - Cancel a previous vote, this must be done by the voter before the vote ends.
//! - `delegate` - Delegates the voting power (tokens * conviction) to another account.
//! - `undelegate` - Stops the delegation of voting power to another account.
//!
//! Administration actions that can be done to any account:
//! - `reap_vote` - Remove some account's expired votes.
//! - `unlock` - Redetermine the account's balance lock, potentially making tokens available.
//!
//! Preimage actions:
//! - `note_preimage` - Registers the preimage for an upcoming proposal, requires a deposit that is
//!   returned once the proposal is enacted.
//! - `note_preimage_operational` - same but provided by `T::OperationalPreimageOrigin`.
//! - `note_imminent_preimage` - Registers the preimage for an upcoming proposal. Does not require a
//!   deposit, but the proposal must be in the dispatch queue.
//! - `note_imminent_preimage_operational` - same but provided by `T::OperationalPreimageOrigin`.
//! - `reap_preimage` - Removes the preimage for an expired proposal. Will only work under the
//!   condition that it's the same account that noted it and after the voting period, OR it's a
//!   different account after the enactment period.
//!
//! #### Cancellation Origin
//!
//! This call can only be made by the `CancellationOrigin`.
//!
//! - `emergency_cancel` - Schedules an emergency cancellation of a referendum. Can only happen once
//!   to a specific referendum.
//!
//! #### ExternalOrigin
//!
//! This call can only be made by the `ExternalOrigin`.
//!
//! - `external_propose` - Schedules a proposal to become a referendum once it is is legal for an
//!   externally proposed referendum.
//!
//! #### External Majority Origin
//!
//! This call can only be made by the `ExternalMajorityOrigin`.
//!
//! - `external_propose_majority` - Schedules a proposal to become a majority-carries referendum
//!   once it is legal for an externally proposed referendum.
//!
//! #### External Default Origin
//!
//! This call can only be made by the `ExternalDefaultOrigin`.
//!
//! - `external_propose_default` - Schedules a proposal to become a negative-turnout-bias referendum
//!   once it is legal for an externally proposed referendum.
//!
//! #### Fast Track Origin
//!
//! This call can only be made by the `FastTrackOrigin`.
//!
//! - `fast_track` - Schedules the current externally proposed proposal that is "majority-carries"
//!   to become a referendum immediately.
//!
//! #### Veto Origin
//!
//! This call can only be made by the `VetoOrigin`.
//!
//! - `veto_external` - Vetoes and blacklists the external proposal hash.
//!
//! #### Root
//!
//! - `cancel_referendum` - Removes a referendum.
//! - `cancel_queued` - Cancels a proposal that is queued for enactment.
//! - `clear_public_proposal` - Removes all public proposals.

#![recursion_limit = "256"]
#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
use frame_support::{
	ensure,
	error::BadOrigin,
	traits::{
		defensive_prelude::*,
		schedule::{v3::Named as ScheduleNamed, DispatchTime},
		Bounded, Currency, EnsureOrigin, Get, Hash as PreimageHash, LockIdentifier,
		LockableCurrency, OnUnbalanced, QueryPreimage, ReservableCurrency, StorePreimage,
		WithdrawReasons,
	},
	weights::Weight,
};
use frame_system::pallet_prelude::OriginFor;
use sp_runtime::{
	traits::{Bounded as ArithBounded, One, Saturating, StaticLookup, Zero},
	ArithmeticError, DispatchError, DispatchResult,
};
use sp_std::prelude::*;

mod conviction;
mod types;
mod vote;
mod vote_threshold;
pub mod weights;
pub use conviction::Conviction;
pub use pallet::*;
pub use types::{
	Delegations, MetadataOwner, PropIndex, ReferendumIndex, ReferendumInfo, ReferendumStatus,
	Tally, UnvoteScope,
};
pub use vote::{AccountVote, Vote, Voting};
pub use vote_threshold::{Approved, VoteThreshold};
pub use weights::WeightInfo;

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
pub mod benchmarking;

pub mod migrations;

const DEMOCRACY_ID: LockIdentifier = *b"democrac";

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;
pub type CallOf<T> = <T as frame_system::Config>::RuntimeCall;
pub type BoundedCallOf<T> = Bounded<CallOf<T>>;
type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

#[frame_support::pallet]
pub mod pallet {
	use super::{DispatchResult, *};
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;
	use sp_core::H256;

	/// The current storage version.
	const STORAGE_VERSION: StorageVersion = StorageVersion::new(1);

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config + Sized {
		type WeightInfo: WeightInfo;
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// The Scheduler.
		type Scheduler: ScheduleNamed<Self::BlockNumber, CallOf<Self>, Self::PalletsOrigin>;

		/// The Preimage provider.
		type Preimages: QueryPreimage + StorePreimage;

		/// Currency type for this pallet.
		type Currency: ReservableCurrency<Self::AccountId>
			+ LockableCurrency<Self::AccountId, Moment = Self::BlockNumber>;

		/// The period between a proposal being approved and enacted.
		///
		/// It should generally be a little more than the unstake period to ensure that
		/// voting stakers have an opportunity to remove themselves from the system in the case
		/// where they are on the losing side of a vote.
		#[pallet::constant]
		type EnactmentPeriod: Get<Self::BlockNumber>;

		/// How often (in blocks) new public referenda are launched.
		#[pallet::constant]
		type LaunchPeriod: Get<Self::BlockNumber>;

		/// How often (in blocks) to check for new votes.
		#[pallet::constant]
		type VotingPeriod: Get<Self::BlockNumber>;

		/// The minimum period of vote locking.
		///
		/// It should be no shorter than enactment period to ensure that in the case of an approval,
		/// those successful voters are locked into the consequences that their votes entail.
		#[pallet::constant]
		type VoteLockingPeriod: Get<Self::BlockNumber>;

		/// The minimum amount to be used as a deposit for a public referendum proposal.
		#[pallet::constant]
		type MinimumDeposit: Get<BalanceOf<Self>>;

		/// Indicator for whether an emergency origin is even allowed to happen. Some chains may
		/// want to set this permanently to `false`, others may want to condition it on things such
		/// as an upgrade having happened recently.
		#[pallet::constant]
		type InstantAllowed: Get<bool>;

		/// Minimum voting period allowed for a fast-track referendum.
		#[pallet::constant]
		type FastTrackVotingPeriod: Get<Self::BlockNumber>;

		/// Period in blocks where an external proposal may not be re-submitted after being vetoed.
		#[pallet::constant]
		type CooloffPeriod: Get<Self::BlockNumber>;

		/// The maximum number of votes for an account.
		///
		/// Also used to compute weight, an overly big value can
		/// lead to extrinsic with very big weight: see `delegate` for instance.
		#[pallet::constant]
		type MaxVotes: Get<u32>;

		/// The maximum number of public proposals that can exist at any time.
		#[pallet::constant]
		type MaxProposals: Get<u32>;

		/// The maximum number of deposits a public proposal may have at any time.
		#[pallet::constant]
		type MaxDeposits: Get<u32>;

		/// The maximum number of items which can be blacklisted.
		#[pallet::constant]
		type MaxBlacklisted: Get<u32>;

		/// Origin from which the next tabled referendum may be forced. This is a normal
		/// "super-majority-required" referendum.
		type ExternalOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Origin from which the next tabled referendum may be forced; this allows for the tabling
		/// of a majority-carries referendum.
		type ExternalMajorityOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Origin from which the next tabled referendum may be forced; this allows for the tabling
		/// of a negative-turnout-bias (default-carries) referendum.
		type ExternalDefaultOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Origin from which the next majority-carries (or more permissive) referendum may be
		/// tabled to vote according to the `FastTrackVotingPeriod` asynchronously in a similar
		/// manner to the emergency origin. It retains its threshold method.
		type FastTrackOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Origin from which the next majority-carries (or more permissive) referendum may be
		/// tabled to vote immediately and asynchronously in a similar manner to the emergency
		/// origin. It retains its threshold method.
		type InstantOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Origin from which any referendum may be cancelled in an emergency.
		type CancellationOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Origin from which proposals may be blacklisted.
		type BlacklistOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Origin from which a proposal may be cancelled and its backers slashed.
		type CancelProposalOrigin: EnsureOrigin<Self::RuntimeOrigin>;

		/// Origin for anyone able to veto proposals.
		type VetoOrigin: EnsureOrigin<Self::RuntimeOrigin, Success = Self::AccountId>;

		/// Overarching type of all pallets origins.
		type PalletsOrigin: From<frame_system::RawOrigin<Self::AccountId>>;

		/// Handler for the unbalanced reduction when slashing a preimage deposit.
		type Slash: OnUnbalanced<NegativeImbalanceOf<Self>>;
	}

	/// The number of (public) proposals that have been made so far.
	#[pallet::storage]
	#[pallet::getter(fn public_prop_count)]
	pub type PublicPropCount<T> = StorageValue<_, PropIndex, ValueQuery>;

	/// The public proposals. Unsorted. The second item is the proposal.
	#[pallet::storage]
	#[pallet::getter(fn public_props)]
	pub type PublicProps<T: Config> = StorageValue<
		_,
		BoundedVec<(PropIndex, BoundedCallOf<T>, T::AccountId), T::MaxProposals>,
		ValueQuery,
	>;

	/// Those who have locked a deposit.
	///
	/// TWOX-NOTE: Safe, as increasing integer keys are safe.
	#[pallet::storage]
	#[pallet::getter(fn deposit_of)]
	pub type DepositOf<T: Config> = StorageMap<
		_,
		Twox64Concat,
		PropIndex,
		(BoundedVec<T::AccountId, T::MaxDeposits>, BalanceOf<T>),
	>;

	/// The next free referendum index, aka the number of referenda started so far.
	#[pallet::storage]
	#[pallet::getter(fn referendum_count)]
	pub type ReferendumCount<T> = StorageValue<_, ReferendumIndex, ValueQuery>;

	/// The lowest referendum index representing an unbaked referendum. Equal to
	/// `ReferendumCount` if there isn't a unbaked referendum.
	#[pallet::storage]
	#[pallet::getter(fn lowest_unbaked)]
	pub type LowestUnbaked<T> = StorageValue<_, ReferendumIndex, ValueQuery>;

	/// Information concerning any given referendum.
	///
	/// TWOX-NOTE: SAFE as indexes are not under an attacker’s control.
	#[pallet::storage]
	#[pallet::getter(fn referendum_info)]
	pub type ReferendumInfoOf<T: Config> = StorageMap<
		_,
		Twox64Concat,
		ReferendumIndex,
		ReferendumInfo<T::BlockNumber, BoundedCallOf<T>, BalanceOf<T>>,
	>;

	/// All votes for a particular voter. We store the balance for the number of votes that we
	/// have recorded. The second item is the total amount of delegations, that will be added.
	///
	/// TWOX-NOTE: SAFE as `AccountId`s are crypto hashes anyway.
	#[pallet::storage]
	pub type VotingOf<T: Config> = StorageMap<
		_,
		Twox64Concat,
		T::AccountId,
		Voting<BalanceOf<T>, T::AccountId, T::BlockNumber, T::MaxVotes>,
		ValueQuery,
	>;

	/// True if the last referendum tabled was submitted externally. False if it was a public
	/// proposal.
	#[pallet::storage]
	pub type LastTabledWasExternal<T> = StorageValue<_, bool, ValueQuery>;

	/// The referendum to be tabled whenever it would be valid to table an external proposal.
	/// This happens when a referendum needs to be tabled and one of two conditions are met:
	/// - `LastTabledWasExternal` is `false`; or
	/// - `PublicProps` is empty.
	#[pallet::storage]
	pub type NextExternal<T: Config> = StorageValue<_, (BoundedCallOf<T>, VoteThreshold)>;

	/// A record of who vetoed what. Maps proposal hash to a possible existent block number
	/// (until when it may not be resubmitted) and who vetoed it.
	#[pallet::storage]
	pub type Blacklist<T: Config> = StorageMap<
		_,
		Identity,
		H256,
		(T::BlockNumber, BoundedVec<T::AccountId, T::MaxBlacklisted>),
	>;

	/// Record of all proposals that have been subject to emergency cancellation.
	#[pallet::storage]
	pub type Cancellations<T: Config> = StorageMap<_, Identity, H256, bool, ValueQuery>;

	/// General information concerning any proposal or referendum.
	/// The `PreimageHash` refers to the preimage of the `Preimages` provider which can be a JSON
	/// dump or IPFS hash of a JSON file.
	///
	/// Consider a garbage collection for a metadata of finished referendums to `unrequest` (remove)
	/// large preimages.
	#[pallet::storage]
	pub type MetadataOf<T: Config> = StorageMap<_, Blake2_128Concat, MetadataOwner, PreimageHash>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		_phantom: sp_std::marker::PhantomData<T>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			GenesisConfig { _phantom: Default::default() }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			PublicPropCount::<T>::put(0 as PropIndex);
			ReferendumCount::<T>::put(0 as ReferendumIndex);
			LowestUnbaked::<T>::put(0 as ReferendumIndex);
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A motion has been proposed by a public account.
		Proposed { proposal_index: PropIndex, deposit: BalanceOf<T> },
		/// A public proposal has been tabled for referendum vote.
		Tabled { proposal_index: PropIndex, deposit: BalanceOf<T> },
		/// An external proposal has been tabled.
		ExternalTabled,
		/// A referendum has begun.
		Started { ref_index: ReferendumIndex, threshold: VoteThreshold },
		/// A proposal has been approved by referendum.
		Passed { ref_index: ReferendumIndex },
		/// A proposal has been rejected by referendum.
		NotPassed { ref_index: ReferendumIndex },
		/// A referendum has been cancelled.
		Cancelled { ref_index: ReferendumIndex },
		/// An account has delegated their vote to another account.
		Delegated { who: T::AccountId, target: T::AccountId },
		/// An account has cancelled a previous delegation operation.
		Undelegated { account: T::AccountId },
		/// An external proposal has been vetoed.
		Vetoed { who: T::AccountId, proposal_hash: H256, until: T::BlockNumber },
		/// A proposal_hash has been blacklisted permanently.
		Blacklisted { proposal_hash: H256 },
		/// An account has voted in a referendum
		Voted { voter: T::AccountId, ref_index: ReferendumIndex, vote: AccountVote<BalanceOf<T>> },
		/// An account has secconded a proposal
		Seconded { seconder: T::AccountId, prop_index: PropIndex },
		/// A proposal got canceled.
		ProposalCanceled { prop_index: PropIndex },
		/// Metadata for a proposal or a referendum has been set.
		MetadataSet {
			/// Metadata owner.
			owner: MetadataOwner,
			/// Preimage hash.
			hash: PreimageHash,
		},
		/// Metadata for a proposal or a referendum has been cleared.
		MetadataCleared {
			/// Metadata owner.
			owner: MetadataOwner,
			/// Preimage hash.
			hash: PreimageHash,
		},
		/// Metadata has been transferred to new owner.
		MetadataTransferred {
			/// Previous metadata owner.
			prev_owner: MetadataOwner,
			/// New metadata owner.
			owner: MetadataOwner,
			/// Preimage hash.
			hash: PreimageHash,
		},
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Value too low
		ValueLow,
		/// Proposal does not exist
		ProposalMissing,
		/// Cannot cancel the same proposal twice
		AlreadyCanceled,
		/// Proposal already made
		DuplicateProposal,
		/// Proposal still blacklisted
		ProposalBlacklisted,
		/// Next external proposal not simple majority
		NotSimpleMajority,
		/// Invalid hash
		InvalidHash,
		/// No external proposal
		NoProposal,
		/// Identity may not veto a proposal twice
		AlreadyVetoed,
		/// Vote given for invalid referendum
		ReferendumInvalid,
		/// No proposals waiting
		NoneWaiting,
		/// The given account did not vote on the referendum.
		NotVoter,
		/// The actor has no permission to conduct the action.
		NoPermission,
		/// The account is already delegating.
		AlreadyDelegating,
		/// Too high a balance was provided that the account cannot afford.
		InsufficientFunds,
		/// The account is not currently delegating.
		NotDelegating,
		/// The account currently has votes attached to it and the operation cannot succeed until
		/// these are removed, either through `unvote` or `reap_vote`.
		VotesExist,
		/// The instant referendum origin is currently disallowed.
		InstantNotAllowed,
		/// Delegation to oneself makes no sense.
		Nonsense,
		/// Invalid upper bound.
		WrongUpperBound,
		/// Maximum number of votes reached.
		MaxVotesReached,
		/// Maximum number of items reached.
		TooMany,
		/// Voting period too low
		VotingPeriodLow,
		/// The preimage does not exist.
		PreimageNotExist,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		/// Weight: see `begin_block`
		fn on_initialize(n: T::BlockNumber) -> Weight {
			Self::begin_block(n)
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Propose a sensitive action to be taken.
		///
		/// The dispatch origin of this call must be _Signed_ and the sender must
		/// have funds to cover the deposit.
		///
		/// - `proposal_hash`: The hash of the proposal preimage.
		/// - `value`: The amount of deposit (must be at least `MinimumDeposit`).
		///
		/// Emits `Proposed`.
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::propose())]
		pub fn propose(
			origin: OriginFor<T>,
			proposal: BoundedCallOf<T>,
			#[pallet::compact] value: BalanceOf<T>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			ensure!(value >= T::MinimumDeposit::get(), Error::<T>::ValueLow);

			let index = Self::public_prop_count();
			let real_prop_count = PublicProps::<T>::decode_len().unwrap_or(0) as u32;
			let max_proposals = T::MaxProposals::get();
			ensure!(real_prop_count < max_proposals, Error::<T>::TooMany);
			let proposal_hash = proposal.hash();

			if let Some((until, _)) = <Blacklist<T>>::get(proposal_hash) {
				ensure!(
					<frame_system::Pallet<T>>::block_number() >= until,
					Error::<T>::ProposalBlacklisted,
				);
			}

			T::Currency::reserve(&who, value)?;

			let depositors = BoundedVec::<_, T::MaxDeposits>::truncate_from(vec![who.clone()]);
			DepositOf::<T>::insert(index, (depositors, value));

			PublicPropCount::<T>::put(index + 1);

			PublicProps::<T>::try_append((index, proposal, who))
				.map_err(|_| Error::<T>::TooMany)?;

			Self::deposit_event(Event::<T>::Proposed { proposal_index: index, deposit: value });
			Ok(())
		}

		/// Signals agreement with a particular proposal.
		///
		/// The dispatch origin of this call must be _Signed_ and the sender
		/// must have funds to cover the deposit, equal to the original deposit.
		///
		/// - `proposal`: The index of the proposal to second.
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::second())]
		pub fn second(
			origin: OriginFor<T>,
			#[pallet::compact] proposal: PropIndex,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			let seconds = Self::len_of_deposit_of(proposal).ok_or(Error::<T>::ProposalMissing)?;
			ensure!(seconds < T::MaxDeposits::get(), Error::<T>::TooMany);
			let mut deposit = Self::deposit_of(proposal).ok_or(Error::<T>::ProposalMissing)?;
			T::Currency::reserve(&who, deposit.1)?;
			let ok = deposit.0.try_push(who.clone()).is_ok();
			debug_assert!(ok, "`seconds` is below static limit; `try_insert` should succeed; qed");
			<DepositOf<T>>::insert(proposal, deposit);
			Self::deposit_event(Event::<T>::Seconded { seconder: who, prop_index: proposal });
			Ok(())
		}

		/// Vote in a referendum. If `vote.is_aye()`, the vote is to enact the proposal;
		/// otherwise it is a vote to keep the status quo.
		///
		/// The dispatch origin of this call must be _Signed_.
		///
		/// - `ref_index`: The index of the referendum to vote for.
		/// - `vote`: The vote configuration.
		#[pallet::call_index(2)]
		#[pallet::weight(T::WeightInfo::vote_new().max(T::WeightInfo::vote_existing()))]
		pub fn vote(
			origin: OriginFor<T>,
			#[pallet::compact] ref_index: ReferendumIndex,
			vote: AccountVote<BalanceOf<T>>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::try_vote(&who, ref_index, vote)
		}

		/// Schedule an emergency cancellation of a referendum. Cannot happen twice to the same
		/// referendum.
		///
		/// The dispatch origin of this call must be `CancellationOrigin`.
		///
		/// -`ref_index`: The index of the referendum to cancel.
		///
		/// Weight: `O(1)`.
		#[pallet::call_index(3)]
		#[pallet::weight((T::WeightInfo::emergency_cancel(), DispatchClass::Operational))]
		pub fn emergency_cancel(
			origin: OriginFor<T>,
			ref_index: ReferendumIndex,
		) -> DispatchResult {
			T::CancellationOrigin::ensure_origin(origin)?;

			let status = Self::referendum_status(ref_index)?;
			let h = status.proposal.hash();
			ensure!(!<Cancellations<T>>::contains_key(h), Error::<T>::AlreadyCanceled);

			<Cancellations<T>>::insert(h, true);
			Self::internal_cancel_referendum(ref_index);
			Ok(())
		}

		/// Schedule a referendum to be tabled once it is legal to schedule an external
		/// referendum.
		///
		/// The dispatch origin of this call must be `ExternalOrigin`.
		///
		/// - `proposal_hash`: The preimage hash of the proposal.
		#[pallet::call_index(4)]
		#[pallet::weight(T::WeightInfo::external_propose())]
		pub fn external_propose(
			origin: OriginFor<T>,
			proposal: BoundedCallOf<T>,
		) -> DispatchResult {
			T::ExternalOrigin::ensure_origin(origin)?;
			ensure!(!<NextExternal<T>>::exists(), Error::<T>::DuplicateProposal);
			if let Some((until, _)) = <Blacklist<T>>::get(proposal.hash()) {
				ensure!(
					<frame_system::Pallet<T>>::block_number() >= until,
					Error::<T>::ProposalBlacklisted,
				);
			}
			<NextExternal<T>>::put((proposal, VoteThreshold::SuperMajorityApprove));
			Ok(())
		}

		/// Schedule a majority-carries referendum to be tabled next once it is legal to schedule
		/// an external referendum.
		///
		/// The dispatch of this call must be `ExternalMajorityOrigin`.
		///
		/// - `proposal_hash`: The preimage hash of the proposal.
		///
		/// Unlike `external_propose`, blacklisting has no effect on this and it may replace a
		/// pre-scheduled `external_propose` call.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(5)]
		#[pallet::weight(T::WeightInfo::external_propose_majority())]
		pub fn external_propose_majority(
			origin: OriginFor<T>,
			proposal: BoundedCallOf<T>,
		) -> DispatchResult {
			T::ExternalMajorityOrigin::ensure_origin(origin)?;
			<NextExternal<T>>::put((proposal, VoteThreshold::SimpleMajority));
			Ok(())
		}

		/// Schedule a negative-turnout-bias referendum to be tabled next once it is legal to
		/// schedule an external referendum.
		///
		/// The dispatch of this call must be `ExternalDefaultOrigin`.
		///
		/// - `proposal_hash`: The preimage hash of the proposal.
		///
		/// Unlike `external_propose`, blacklisting has no effect on this and it may replace a
		/// pre-scheduled `external_propose` call.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(6)]
		#[pallet::weight(T::WeightInfo::external_propose_default())]
		pub fn external_propose_default(
			origin: OriginFor<T>,
			proposal: BoundedCallOf<T>,
		) -> DispatchResult {
			T::ExternalDefaultOrigin::ensure_origin(origin)?;
			<NextExternal<T>>::put((proposal, VoteThreshold::SuperMajorityAgainst));
			Ok(())
		}

		/// Schedule the currently externally-proposed majority-carries referendum to be tabled
		/// immediately. If there is no externally-proposed referendum currently, or if there is one
		/// but it is not a majority-carries referendum then it fails.
		///
		/// The dispatch of this call must be `FastTrackOrigin`.
		///
		/// - `proposal_hash`: The hash of the current external proposal.
		/// - `voting_period`: The period that is allowed for voting on this proposal. Increased to
		/// 	Must be always greater than zero.
		/// 	For `FastTrackOrigin` must be equal or greater than `FastTrackVotingPeriod`.
		/// - `delay`: The number of block after voting has ended in approval and this should be
		///   enacted. This doesn't have a minimum amount.
		///
		/// Emits `Started`.
		///
		/// Weight: `O(1)`
		#[pallet::call_index(7)]
		#[pallet::weight(T::WeightInfo::fast_track())]
		pub fn fast_track(
			origin: OriginFor<T>,
			proposal_hash: H256,
			voting_period: T::BlockNumber,
			delay: T::BlockNumber,
		) -> DispatchResult {
			// Rather complicated bit of code to ensure that either:
			// - `voting_period` is at least `FastTrackVotingPeriod` and `origin` is
			//   `FastTrackOrigin`; or
			// - `InstantAllowed` is `true` and `origin` is `InstantOrigin`.
			let maybe_ensure_instant = if voting_period < T::FastTrackVotingPeriod::get() {
				Some(origin)
			} else if let Err(origin) = T::FastTrackOrigin::try_origin(origin) {
				Some(origin)
			} else {
				None
			};
			if let Some(ensure_instant) = maybe_ensure_instant {
				T::InstantOrigin::ensure_origin(ensure_instant)?;
				ensure!(T::InstantAllowed::get(), Error::<T>::InstantNotAllowed);
			}

			ensure!(voting_period > T::BlockNumber::zero(), Error::<T>::VotingPeriodLow);
			let (ext_proposal, threshold) =
				<NextExternal<T>>::get().ok_or(Error::<T>::ProposalMissing)?;
			ensure!(
				threshold != VoteThreshold::SuperMajorityApprove,
				Error::<T>::NotSimpleMajority,
			);
			ensure!(proposal_hash == ext_proposal.hash(), Error::<T>::InvalidHash);

			<NextExternal<T>>::kill();
			let now = <frame_system::Pallet<T>>::block_number();
			let ref_index = Self::inject_referendum(
				now.saturating_add(voting_period),
				ext_proposal,
				threshold,
				delay,
			);
			Self::transfer_metadata(MetadataOwner::External, MetadataOwner::Referendum(ref_index));
			Ok(())
		}

		/// Veto and blacklist the external proposal hash.
		///
		/// The dispatch origin of this call must be `VetoOrigin`.
		///
		/// - `proposal_hash`: The preimage hash of the proposal to veto and blacklist.
		///
		/// Emits `Vetoed`.
		///
		/// Weight: `O(V + log(V))` where V is number of `existing vetoers`
		#[pallet::call_index(8)]
		#[pallet::weight(T::WeightInfo::veto_external())]
		pub fn veto_external(origin: OriginFor<T>, proposal_hash: H256) -> DispatchResult {
			let who = T::VetoOrigin::ensure_origin(origin)?;

			if let Some((ext_proposal, _)) = NextExternal::<T>::get() {
				ensure!(proposal_hash == ext_proposal.hash(), Error::<T>::ProposalMissing);
			} else {
				return Err(Error::<T>::NoProposal.into())
			}

			let mut existing_vetoers =
				<Blacklist<T>>::get(&proposal_hash).map(|pair| pair.1).unwrap_or_default();
			let insert_position =
				existing_vetoers.binary_search(&who).err().ok_or(Error::<T>::AlreadyVetoed)?;
			existing_vetoers
				.try_insert(insert_position, who.clone())
				.map_err(|_| Error::<T>::TooMany)?;

			let until =
				<frame_system::Pallet<T>>::block_number().saturating_add(T::CooloffPeriod::get());
			<Blacklist<T>>::insert(&proposal_hash, (until, existing_vetoers));

			Self::deposit_event(Event::<T>::Vetoed { who, proposal_hash, until });
			<NextExternal<T>>::kill();
			Self::clear_metadata(MetadataOwner::External);
			Ok(())
		}

		/// Remove a referendum.
		///
		/// The dispatch origin of this call must be _Root_.
		///
		/// - `ref_index`: The index of the referendum to cancel.
		///
		/// # Weight: `O(1)`.
		#[pallet::call_index(9)]
		#[pallet::weight(T::WeightInfo::cancel_referendum())]
		pub fn cancel_referendum(
			origin: OriginFor<T>,
			#[pallet::compact] ref_index: ReferendumIndex,
		) -> DispatchResult {
			ensure_root(origin)?;
			Self::internal_cancel_referendum(ref_index);
			Ok(())
		}

		/// Delegate the voting power (with some given conviction) of the sending account.
		///
		/// The balance delegated is locked for as long as it's delegated, and thereafter for the
		/// time appropriate for the conviction's lock period.
		///
		/// The dispatch origin of this call must be _Signed_, and the signing account must either:
		///   - be delegating already; or
		///   - have no voting activity (if there is, then it will need to be removed/consolidated
		///     through `reap_vote` or `unvote`).
		///
		/// - `to`: The account whose voting the `target` account's voting power will follow.
		/// - `conviction`: The conviction that will be attached to the delegated votes. When the
		///   account is undelegated, the funds will be locked for the corresponding period.
		/// - `balance`: The amount of the account's balance to be used in delegating. This must not
		///   be more than the account's current balance.
		///
		/// Emits `Delegated`.
		///
		/// Weight: `O(R)` where R is the number of referendums the voter delegating to has
		///   voted on. Weight is charged as if maximum votes.
		// NOTE: weight must cover an incorrect voting of origin with max votes, this is ensure
		// because a valid delegation cover decoding a direct voting with max votes.
		#[pallet::call_index(10)]
		#[pallet::weight(T::WeightInfo::delegate(T::MaxVotes::get()))]
		pub fn delegate(
			origin: OriginFor<T>,
			to: AccountIdLookupOf<T>,
			conviction: Conviction,
			balance: BalanceOf<T>,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let to = T::Lookup::lookup(to)?;
			let votes = Self::try_delegate(who, to, conviction, balance)?;

			Ok(Some(T::WeightInfo::delegate(votes)).into())
		}

		/// Undelegate the voting power of the sending account.
		///
		/// Tokens may be unlocked following once an amount of time consistent with the lock period
		/// of the conviction with which the delegation was issued.
		///
		/// The dispatch origin of this call must be _Signed_ and the signing account must be
		/// currently delegating.
		///
		/// Emits `Undelegated`.
		///
		/// Weight: `O(R)` where R is the number of referendums the voter delegating to has
		///   voted on. Weight is charged as if maximum votes.
		// NOTE: weight must cover an incorrect voting of origin with max votes, this is ensure
		// because a valid delegation cover decoding a direct voting with max votes.
		#[pallet::call_index(11)]
		#[pallet::weight(T::WeightInfo::undelegate(T::MaxVotes::get()))]
		pub fn undelegate(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let votes = Self::try_undelegate(who)?;
			Ok(Some(T::WeightInfo::undelegate(votes)).into())
		}

		/// Clears all public proposals.
		///
		/// The dispatch origin of this call must be _Root_.
		///
		/// Weight: `O(1)`.
		#[pallet::call_index(12)]
		#[pallet::weight(T::WeightInfo::clear_public_proposals())]
		pub fn clear_public_proposals(origin: OriginFor<T>) -> DispatchResult {
			ensure_root(origin)?;
			<PublicProps<T>>::kill();
			Ok(())
		}

		/// Unlock tokens that have an expired lock.
		///
		/// The dispatch origin of this call must be _Signed_.
		///
		/// - `target`: The account to remove the lock on.
		///
		/// Weight: `O(R)` with R number of vote of target.
		#[pallet::call_index(13)]
		#[pallet::weight(T::WeightInfo::unlock_set(T::MaxVotes::get()).max(T::WeightInfo::unlock_remove(T::MaxVotes::get())))]
		pub fn unlock(origin: OriginFor<T>, target: AccountIdLookupOf<T>) -> DispatchResult {
			ensure_signed(origin)?;
			let target = T::Lookup::lookup(target)?;
			Self::update_lock(&target);
			Ok(())
		}

		/// Remove a vote for a referendum.
		///
		/// If:
		/// - the referendum was cancelled, or
		/// - the referendum is ongoing, or
		/// - the referendum has ended such that
		///   - the vote of the account was in opposition to the result; or
		///   - there was no conviction to the account's vote; or
		///   - the account made a split vote
		/// ...then the vote is removed cleanly and a following call to `unlock` may result in more
		/// funds being available.
		///
		/// If, however, the referendum has ended and:
		/// - it finished corresponding to the vote of the account, and
		/// - the account made a standard vote with conviction, and
		/// - the lock period of the conviction is not over
		/// ...then the lock will be aggregated into the overall account's lock, which may involve
		/// *overlocking* (where the two locks are combined into a single lock that is the maximum
		/// of both the amount locked and the time is it locked for).
		///
		/// The dispatch origin of this call must be _Signed_, and the signer must have a vote
		/// registered for referendum `index`.
		///
		/// - `index`: The index of referendum of the vote to be removed.
		///
		/// Weight: `O(R + log R)` where R is the number of referenda that `target` has voted on.
		///   Weight is calculated for the maximum number of vote.
		#[pallet::call_index(14)]
		#[pallet::weight(T::WeightInfo::remove_vote(T::MaxVotes::get()))]
		pub fn remove_vote(origin: OriginFor<T>, index: ReferendumIndex) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::try_remove_vote(&who, index, UnvoteScope::Any)
		}

		/// Remove a vote for a referendum.
		///
		/// If the `target` is equal to the signer, then this function is exactly equivalent to
		/// `remove_vote`. If not equal to the signer, then the vote must have expired,
		/// either because the referendum was cancelled, because the voter lost the referendum or
		/// because the conviction period is over.
		///
		/// The dispatch origin of this call must be _Signed_.
		///
		/// - `target`: The account of the vote to be removed; this account must have voted for
		///   referendum `index`.
		/// - `index`: The index of referendum of the vote to be removed.
		///
		/// Weight: `O(R + log R)` where R is the number of referenda that `target` has voted on.
		///   Weight is calculated for the maximum number of vote.
		#[pallet::call_index(15)]
		#[pallet::weight(T::WeightInfo::remove_other_vote(T::MaxVotes::get()))]
		pub fn remove_other_vote(
			origin: OriginFor<T>,
			target: AccountIdLookupOf<T>,
			index: ReferendumIndex,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let target = T::Lookup::lookup(target)?;
			let scope = if target == who { UnvoteScope::Any } else { UnvoteScope::OnlyExpired };
			Self::try_remove_vote(&target, index, scope)?;
			Ok(())
		}

		/// Permanently place a proposal into the blacklist. This prevents it from ever being
		/// proposed again.
		///
		/// If called on a queued public or external proposal, then this will result in it being
		/// removed. If the `ref_index` supplied is an active referendum with the proposal hash,
		/// then it will be cancelled.
		///
		/// The dispatch origin of this call must be `BlacklistOrigin`.
		///
		/// - `proposal_hash`: The proposal hash to blacklist permanently.
		/// - `ref_index`: An ongoing referendum whose hash is `proposal_hash`, which will be
		/// cancelled.
		///
		/// Weight: `O(p)` (though as this is an high-privilege dispatch, we assume it has a
		///   reasonable value).
		#[pallet::call_index(16)]
		#[pallet::weight((T::WeightInfo::blacklist(), DispatchClass::Operational))]
		pub fn blacklist(
			origin: OriginFor<T>,
			proposal_hash: H256,
			maybe_ref_index: Option<ReferendumIndex>,
		) -> DispatchResult {
			T::BlacklistOrigin::ensure_origin(origin)?;

			// Insert the proposal into the blacklist.
			let permanent = (T::BlockNumber::max_value(), BoundedVec::<T::AccountId, _>::default());
			Blacklist::<T>::insert(&proposal_hash, permanent);

			// Remove the queued proposal, if it's there.
			PublicProps::<T>::mutate(|props| {
				if let Some(index) = props.iter().position(|p| p.1.hash() == proposal_hash) {
					let (prop_index, ..) = props.remove(index);
					if let Some((whos, amount)) = DepositOf::<T>::take(prop_index) {
						for who in whos.into_iter() {
							T::Slash::on_unbalanced(T::Currency::slash_reserved(&who, amount).0);
						}
					}
					Self::clear_metadata(MetadataOwner::Proposal(prop_index));
				}
			});

			// Remove the external queued referendum, if it's there.
			if matches!(NextExternal::<T>::get(), Some((p, ..)) if p.hash() == proposal_hash) {
				NextExternal::<T>::kill();
				Self::clear_metadata(MetadataOwner::External);
			}

			// Remove the referendum, if it's there.
			if let Some(ref_index) = maybe_ref_index {
				if let Ok(status) = Self::referendum_status(ref_index) {
					if status.proposal.hash() == proposal_hash {
						Self::internal_cancel_referendum(ref_index);
					}
				}
			}

			Self::deposit_event(Event::<T>::Blacklisted { proposal_hash });
			Ok(())
		}

		/// Remove a proposal.
		///
		/// The dispatch origin of this call must be `CancelProposalOrigin`.
		///
		/// - `prop_index`: The index of the proposal to cancel.
		///
		/// Weight: `O(p)` where `p = PublicProps::<T>::decode_len()`
		#[pallet::call_index(17)]
		#[pallet::weight(T::WeightInfo::cancel_proposal())]
		pub fn cancel_proposal(
			origin: OriginFor<T>,
			#[pallet::compact] prop_index: PropIndex,
		) -> DispatchResult {
			T::CancelProposalOrigin::ensure_origin(origin)?;

			PublicProps::<T>::mutate(|props| props.retain(|p| p.0 != prop_index));
			if let Some((whos, amount)) = DepositOf::<T>::take(prop_index) {
				for who in whos.into_iter() {
					T::Slash::on_unbalanced(T::Currency::slash_reserved(&who, amount).0);
				}
			}
			Self::deposit_event(Event::<T>::ProposalCanceled { prop_index });
			Self::clear_metadata(MetadataOwner::Proposal(prop_index));
			Ok(())
		}

		/// Set or clear a metadata of a proposal or a referendum.
		///
		/// Parameters:
		/// - `origin`: Must correspond to the `MetadataOwner`.
		///     - `ExternalOrigin` for an external proposal with the `SuperMajorityApprove`
		///       threshold.
		///     - `ExternalDefaultOrigin` for an external proposal with the `SuperMajorityAgainst`
		///       threshold.
		///     - `ExternalMajorityOrigin` for an external proposal with the `SimpleMajority`
		///       threshold.
		///     - `Signed` by a creator for a public proposal.
		///     - `Signed` to clear a metadata for a finished referendum.
		///     - `Root` to set a metadata for an ongoing referendum.
		/// - `owner`: an identifier of a metadata owner.
		/// - `maybe_hash`: The hash of an on-chain stored preimage. `None` to clear a metadata.
		#[pallet::call_index(18)]
		#[pallet::weight(
			match (owner, maybe_hash) {
				(MetadataOwner::External, Some(_)) => T::WeightInfo::set_external_metadata(),
				(MetadataOwner::External, None) => T::WeightInfo::clear_external_metadata(),
				(MetadataOwner::Proposal(_), Some(_)) => T::WeightInfo::set_proposal_metadata(),
				(MetadataOwner::Proposal(_), None) => T::WeightInfo::clear_proposal_metadata(),
				(MetadataOwner::Referendum(_), Some(_)) => T::WeightInfo::set_referendum_metadata(),
				(MetadataOwner::Referendum(_), None) => T::WeightInfo::clear_referendum_metadata(),
			}
		)]
		pub fn set_metadata(
			origin: OriginFor<T>,
			owner: MetadataOwner,
			maybe_hash: Option<PreimageHash>,
		) -> DispatchResult {
			match owner {
				MetadataOwner::External => {
					let (_, threshold) = <NextExternal<T>>::get().ok_or(Error::<T>::NoProposal)?;
					Self::ensure_external_origin(threshold, origin)?;
				},
				MetadataOwner::Proposal(index) => {
					let who = ensure_signed(origin)?;
					let (_, _, proposer) = Self::proposal(index)?;
					ensure!(proposer == who, Error::<T>::NoPermission);
				},
				MetadataOwner::Referendum(index) => {
					let is_root = ensure_signed_or_root(origin)?.is_none();
					ensure!(is_root || maybe_hash.is_none(), Error::<T>::NoPermission);
					ensure!(
						is_root || Self::referendum_status(index).is_err(),
						Error::<T>::NoPermission
					);
				},
			}
			if let Some(hash) = maybe_hash {
				ensure!(T::Preimages::len(&hash).is_some(), Error::<T>::PreimageNotExist);
				MetadataOf::<T>::insert(owner.clone(), hash);
				Self::deposit_event(Event::<T>::MetadataSet { owner, hash });
			} else {
				Self::clear_metadata(owner);
			}
			Ok(())
		}
	}
}

pub trait EncodeInto: Encode {
	fn encode_into<T: AsMut<[u8]> + Default>(&self) -> T {
		let mut t = T::default();
		self.using_encoded(|data| {
			if data.len() <= t.as_mut().len() {
				t.as_mut()[0..data.len()].copy_from_slice(data);
			} else {
				// encoded self is too big to fit into a T. hash it and use the first bytes of that
				// instead.
				let hash = sp_io::hashing::blake2_256(data);
				let l = t.as_mut().len().min(hash.len());
				t.as_mut()[0..l].copy_from_slice(&hash[0..l]);
			}
		});
		t
	}
}
impl<T: Encode> EncodeInto for T {}

impl<T: Config> Pallet<T> {
	// exposed immutables.

	/// Get the amount locked in support of `proposal`; `None` if proposal isn't a valid proposal
	/// index.
	pub fn backing_for(proposal: PropIndex) -> Option<BalanceOf<T>> {
		Self::deposit_of(proposal).map(|(l, d)| d.saturating_mul((l.len() as u32).into()))
	}

	/// Get all referenda ready for tally at block `n`.
	pub fn maturing_referenda_at(
		n: T::BlockNumber,
	) -> Vec<(ReferendumIndex, ReferendumStatus<T::BlockNumber, BoundedCallOf<T>, BalanceOf<T>>)> {
		let next = Self::lowest_unbaked();
		let last = Self::referendum_count();
		Self::maturing_referenda_at_inner(n, next..last)
	}

	fn maturing_referenda_at_inner(
		n: T::BlockNumber,
		range: core::ops::Range<PropIndex>,
	) -> Vec<(ReferendumIndex, ReferendumStatus<T::BlockNumber, BoundedCallOf<T>, BalanceOf<T>>)> {
		range
			.into_iter()
			.map(|i| (i, Self::referendum_info(i)))
			.filter_map(|(i, maybe_info)| match maybe_info {
				Some(ReferendumInfo::Ongoing(status)) => Some((i, status)),
				_ => None,
			})
			.filter(|(_, status)| status.end == n)
			.collect()
	}

	// Exposed mutables.

	/// Start a referendum.
	pub fn internal_start_referendum(
		proposal: BoundedCallOf<T>,
		threshold: VoteThreshold,
		delay: T::BlockNumber,
	) -> ReferendumIndex {
		<Pallet<T>>::inject_referendum(
			<frame_system::Pallet<T>>::block_number().saturating_add(T::VotingPeriod::get()),
			proposal,
			threshold,
			delay,
		)
	}

	/// Remove a referendum.
	pub fn internal_cancel_referendum(ref_index: ReferendumIndex) {
		Self::deposit_event(Event::<T>::Cancelled { ref_index });
		ReferendumInfoOf::<T>::remove(ref_index);
		Self::clear_metadata(MetadataOwner::Referendum(ref_index));
	}

	// private.

	/// Ok if the given referendum is active, Err otherwise
	fn ensure_ongoing(
		r: ReferendumInfo<T::BlockNumber, BoundedCallOf<T>, BalanceOf<T>>,
	) -> Result<ReferendumStatus<T::BlockNumber, BoundedCallOf<T>, BalanceOf<T>>, DispatchError> {
		match r {
			ReferendumInfo::Ongoing(s) => Ok(s),
			_ => Err(Error::<T>::ReferendumInvalid.into()),
		}
	}

	fn referendum_status(
		ref_index: ReferendumIndex,
	) -> Result<ReferendumStatus<T::BlockNumber, BoundedCallOf<T>, BalanceOf<T>>, DispatchError> {
		let info = ReferendumInfoOf::<T>::get(ref_index).ok_or(Error::<T>::ReferendumInvalid)?;
		Self::ensure_ongoing(info)
	}

	/// Actually enact a vote, if legit.
	fn try_vote(
		who: &T::AccountId,
		ref_index: ReferendumIndex,
		vote: AccountVote<BalanceOf<T>>,
	) -> DispatchResult {
		let mut status = Self::referendum_status(ref_index)?;
		ensure!(vote.balance() <= T::Currency::free_balance(who), Error::<T>::InsufficientFunds);
		VotingOf::<T>::try_mutate(who, |voting| -> DispatchResult {
			if let Voting::Direct { ref mut votes, delegations, .. } = voting {
				match votes.binary_search_by_key(&ref_index, |i| i.0) {
					Ok(i) => {
						// Shouldn't be possible to fail, but we handle it gracefully.
						status.tally.remove(votes[i].1).ok_or(ArithmeticError::Underflow)?;
						if let Some(approve) = votes[i].1.as_standard() {
							status.tally.reduce(approve, *delegations);
						}
						votes[i].1 = vote;
					},
					Err(i) => {
						votes
							.try_insert(i, (ref_index, vote))
							.map_err(|_| Error::<T>::MaxVotesReached)?;
					},
				}
				Self::deposit_event(Event::<T>::Voted { voter: who.clone(), ref_index, vote });
				// Shouldn't be possible to fail, but we handle it gracefully.
				status.tally.add(vote).ok_or(ArithmeticError::Overflow)?;
				if let Some(approve) = vote.as_standard() {
					status.tally.increase(approve, *delegations);
				}
				Ok(())
			} else {
				Err(Error::<T>::AlreadyDelegating.into())
			}
		})?;
		// Extend the lock to `balance` (rather than setting it) since we don't know what other
		// votes are in place.
		T::Currency::extend_lock(DEMOCRACY_ID, who, vote.balance(), WithdrawReasons::TRANSFER);
		ReferendumInfoOf::<T>::insert(ref_index, ReferendumInfo::Ongoing(status));
		Ok(())
	}

	/// Remove the account's vote for the given referendum if possible. This is possible when:
	/// - The referendum has not finished.
	/// - The referendum has finished and the voter lost their direction.
	/// - The referendum has finished and the voter's lock period is up.
	///
	/// This will generally be combined with a call to `unlock`.
	fn try_remove_vote(
		who: &T::AccountId,
		ref_index: ReferendumIndex,
		scope: UnvoteScope,
	) -> DispatchResult {
		let info = ReferendumInfoOf::<T>::get(ref_index);
		VotingOf::<T>::try_mutate(who, |voting| -> DispatchResult {
			if let Voting::Direct { ref mut votes, delegations, ref mut prior } = voting {
				let i = votes
					.binary_search_by_key(&ref_index, |i| i.0)
					.map_err(|_| Error::<T>::NotVoter)?;
				match info {
					Some(ReferendumInfo::Ongoing(mut status)) => {
						ensure!(matches!(scope, UnvoteScope::Any), Error::<T>::NoPermission);
						// Shouldn't be possible to fail, but we handle it gracefully.
						status.tally.remove(votes[i].1).ok_or(ArithmeticError::Underflow)?;
						if let Some(approve) = votes[i].1.as_standard() {
							status.tally.reduce(approve, *delegations);
						}
						ReferendumInfoOf::<T>::insert(ref_index, ReferendumInfo::Ongoing(status));
					},
					Some(ReferendumInfo::Finished { end, approved }) => {
						if let Some((lock_periods, balance)) = votes[i].1.locked_if(approved) {
							let unlock_at = end.saturating_add(
								T::VoteLockingPeriod::get().saturating_mul(lock_periods.into()),
							);
							let now = frame_system::Pallet::<T>::block_number();
							if now < unlock_at {
								ensure!(
									matches!(scope, UnvoteScope::Any),
									Error::<T>::NoPermission
								);
								prior.accumulate(unlock_at, balance)
							}
						}
					},
					None => {}, // Referendum was cancelled.
				}
				votes.remove(i);
			}
			Ok(())
		})?;
		Ok(())
	}

	/// Return the number of votes for `who`
	fn increase_upstream_delegation(who: &T::AccountId, amount: Delegations<BalanceOf<T>>) -> u32 {
		VotingOf::<T>::mutate(who, |voting| match voting {
			Voting::Delegating { delegations, .. } => {
				// We don't support second level delegating, so we don't need to do anything more.
				*delegations = delegations.saturating_add(amount);
				1
			},
			Voting::Direct { votes, delegations, .. } => {
				*delegations = delegations.saturating_add(amount);
				for &(ref_index, account_vote) in votes.iter() {
					if let AccountVote::Standard { vote, .. } = account_vote {
						ReferendumInfoOf::<T>::mutate(ref_index, |maybe_info| {
							if let Some(ReferendumInfo::Ongoing(ref mut status)) = maybe_info {
								status.tally.increase(vote.aye, amount);
							}
						});
					}
				}
				votes.len() as u32
			},
		})
	}

	/// Return the number of votes for `who`
	fn reduce_upstream_delegation(who: &T::AccountId, amount: Delegations<BalanceOf<T>>) -> u32 {
		VotingOf::<T>::mutate(who, |voting| match voting {
			Voting::Delegating { delegations, .. } => {
				// We don't support second level delegating, so we don't need to do anything more.
				*delegations = delegations.saturating_sub(amount);
				1
			},
			Voting::Direct { votes, delegations, .. } => {
				*delegations = delegations.saturating_sub(amount);
				for &(ref_index, account_vote) in votes.iter() {
					if let AccountVote::Standard { vote, .. } = account_vote {
						ReferendumInfoOf::<T>::mutate(ref_index, |maybe_info| {
							if let Some(ReferendumInfo::Ongoing(ref mut status)) = maybe_info {
								status.tally.reduce(vote.aye, amount);
							}
						});
					}
				}
				votes.len() as u32
			},
		})
	}

	/// Attempt to delegate `balance` times `conviction` of voting power from `who` to `target`.
	///
	/// Return the upstream number of votes.
	fn try_delegate(
		who: T::AccountId,
		target: T::AccountId,
		conviction: Conviction,
		balance: BalanceOf<T>,
	) -> Result<u32, DispatchError> {
		ensure!(who != target, Error::<T>::Nonsense);
		ensure!(balance <= T::Currency::free_balance(&who), Error::<T>::InsufficientFunds);
		let votes = VotingOf::<T>::try_mutate(&who, |voting| -> Result<u32, DispatchError> {
			let mut old = Voting::Delegating {
				balance,
				target: target.clone(),
				conviction,
				delegations: Default::default(),
				prior: Default::default(),
			};
			sp_std::mem::swap(&mut old, voting);
			match old {
				Voting::Delegating {
					balance, target, conviction, delegations, mut prior, ..
				} => {
					// remove any delegation votes to our current target.
					Self::reduce_upstream_delegation(&target, conviction.votes(balance));
					let now = frame_system::Pallet::<T>::block_number();
					let lock_periods = conviction.lock_periods().into();
					let unlock_block = now
						.saturating_add(T::VoteLockingPeriod::get().saturating_mul(lock_periods));
					prior.accumulate(unlock_block, balance);
					voting.set_common(delegations, prior);
				},
				Voting::Direct { votes, delegations, prior } => {
					// here we just ensure that we're currently idling with no votes recorded.
					ensure!(votes.is_empty(), Error::<T>::VotesExist);
					voting.set_common(delegations, prior);
				},
			}
			let votes = Self::increase_upstream_delegation(&target, conviction.votes(balance));
			// Extend the lock to `balance` (rather than setting it) since we don't know what other
			// votes are in place.
			T::Currency::extend_lock(DEMOCRACY_ID, &who, balance, WithdrawReasons::TRANSFER);
			Ok(votes)
		})?;
		Self::deposit_event(Event::<T>::Delegated { who, target });
		Ok(votes)
	}

	/// Attempt to end the current delegation.
	///
	/// Return the number of votes of upstream.
	fn try_undelegate(who: T::AccountId) -> Result<u32, DispatchError> {
		let votes = VotingOf::<T>::try_mutate(&who, |voting| -> Result<u32, DispatchError> {
			let mut old = Voting::default();
			sp_std::mem::swap(&mut old, voting);
			match old {
				Voting::Delegating { balance, target, conviction, delegations, mut prior } => {
					// remove any delegation votes to our current target.
					let votes =
						Self::reduce_upstream_delegation(&target, conviction.votes(balance));
					let now = frame_system::Pallet::<T>::block_number();
					let lock_periods = conviction.lock_periods().into();
					let unlock_block = now
						.saturating_add(T::VoteLockingPeriod::get().saturating_mul(lock_periods));
					prior.accumulate(unlock_block, balance);
					voting.set_common(delegations, prior);

					Ok(votes)
				},
				Voting::Direct { .. } => Err(Error::<T>::NotDelegating.into()),
			}
		})?;
		Self::deposit_event(Event::<T>::Undelegated { account: who });
		Ok(votes)
	}

	/// Rejig the lock on an account. It will never get more stringent (since that would indicate
	/// a security hole) but may be reduced from what they are currently.
	fn update_lock(who: &T::AccountId) {
		let lock_needed = VotingOf::<T>::mutate(who, |voting| {
			voting.rejig(frame_system::Pallet::<T>::block_number());
			voting.locked_balance()
		});
		if lock_needed.is_zero() {
			T::Currency::remove_lock(DEMOCRACY_ID, who);
		} else {
			T::Currency::set_lock(DEMOCRACY_ID, who, lock_needed, WithdrawReasons::TRANSFER);
		}
	}

	/// Start a referendum
	fn inject_referendum(
		end: T::BlockNumber,
		proposal: BoundedCallOf<T>,
		threshold: VoteThreshold,
		delay: T::BlockNumber,
	) -> ReferendumIndex {
		let ref_index = Self::referendum_count();
		ReferendumCount::<T>::put(ref_index + 1);
		let status =
			ReferendumStatus { end, proposal, threshold, delay, tally: Default::default() };
		let item = ReferendumInfo::Ongoing(status);
		<ReferendumInfoOf<T>>::insert(ref_index, item);
		Self::deposit_event(Event::<T>::Started { ref_index, threshold });
		ref_index
	}

	/// Table the next waiting proposal for a vote.
	fn launch_next(now: T::BlockNumber) -> DispatchResult {
		if LastTabledWasExternal::<T>::take() {
			Self::launch_public(now).or_else(|_| Self::launch_external(now))
		} else {
			Self::launch_external(now).or_else(|_| Self::launch_public(now))
		}
		.map_err(|_| Error::<T>::NoneWaiting.into())
	}

	/// Table the waiting external proposal for a vote, if there is one.
	fn launch_external(now: T::BlockNumber) -> DispatchResult {
		if let Some((proposal, threshold)) = <NextExternal<T>>::take() {
			LastTabledWasExternal::<T>::put(true);
			Self::deposit_event(Event::<T>::ExternalTabled);
			let ref_index = Self::inject_referendum(
				now.saturating_add(T::VotingPeriod::get()),
				proposal,
				threshold,
				T::EnactmentPeriod::get(),
			);
			Self::transfer_metadata(MetadataOwner::External, MetadataOwner::Referendum(ref_index));
			Ok(())
		} else {
			return Err(Error::<T>::NoneWaiting.into())
		}
	}

	/// Table the waiting public proposal with the highest backing for a vote.
	fn launch_public(now: T::BlockNumber) -> DispatchResult {
		let mut public_props = Self::public_props();
		if let Some((winner_index, _)) = public_props.iter().enumerate().max_by_key(
			// defensive only: All current public proposals have an amount locked
			|x| Self::backing_for((x.1).0).defensive_unwrap_or_else(Zero::zero),
		) {
			let (prop_index, proposal, _) = public_props.swap_remove(winner_index);
			<PublicProps<T>>::put(public_props);

			if let Some((depositors, deposit)) = <DepositOf<T>>::take(prop_index) {
				// refund depositors
				for d in depositors.iter() {
					T::Currency::unreserve(d, deposit);
				}
				Self::deposit_event(Event::<T>::Tabled { proposal_index: prop_index, deposit });
				let ref_index = Self::inject_referendum(
					now.saturating_add(T::VotingPeriod::get()),
					proposal,
					VoteThreshold::SuperMajorityApprove,
					T::EnactmentPeriod::get(),
				);
				Self::transfer_metadata(
					MetadataOwner::Proposal(prop_index),
					MetadataOwner::Referendum(ref_index),
				)
			}
			Ok(())
		} else {
			return Err(Error::<T>::NoneWaiting.into())
		}
	}

	fn bake_referendum(
		now: T::BlockNumber,
		index: ReferendumIndex,
		status: ReferendumStatus<T::BlockNumber, BoundedCallOf<T>, BalanceOf<T>>,
	) -> bool {
		let total_issuance = T::Currency::total_issuance();
		let approved = status.threshold.approved(status.tally, total_issuance);

		if approved {
			Self::deposit_event(Event::<T>::Passed { ref_index: index });
			// Actually `hold` the proposal now since we didn't hold it when it came in via the
			// submit extrinsic and we now know that it will be needed. This will be reversed by
			// Scheduler pallet once it is executed which assumes that we will already have placed
			// a `hold` on it.
			T::Preimages::hold(&status.proposal);

			// Earliest it can be scheduled for is next block.
			let when = now.saturating_add(status.delay.max(One::one()));
			if T::Scheduler::schedule_named(
				(DEMOCRACY_ID, index).encode_into(),
				DispatchTime::At(when),
				None,
				63,
				frame_system::RawOrigin::Root.into(),
				status.proposal,
			)
			.is_err()
			{
				frame_support::print("LOGIC ERROR: bake_referendum/schedule_named failed");
			}
		} else {
			Self::deposit_event(Event::<T>::NotPassed { ref_index: index });
		}

		approved
	}

	/// Current era is ending; we should finish up any proposals.
	///
	///
	/// ## Complexity:
	/// If a referendum is launched or maturing, this will take full block weight if queue is not
	/// empty. Otherwise, `O(R)` where `R` is the number of unbaked referenda.
	fn begin_block(now: T::BlockNumber) -> Weight {
		let max_block_weight = T::BlockWeights::get().max_block;
		let mut weight = Weight::zero();

		let next = Self::lowest_unbaked();
		let last = Self::referendum_count();
		let r = last.saturating_sub(next);

		// pick out another public referendum if it's time.
		if (now % T::LaunchPeriod::get()).is_zero() {
			// Errors come from the queue being empty. If the queue is not empty, it will take
			// full block weight.
			if Self::launch_next(now).is_ok() {
				weight = max_block_weight;
			} else {
				weight.saturating_accrue(T::WeightInfo::on_initialize_base_with_launch_period(r));
			}
		} else {
			weight.saturating_accrue(T::WeightInfo::on_initialize_base(r));
		}

		// tally up votes for any expiring referenda.
		for (index, info) in Self::maturing_referenda_at_inner(now, next..last).into_iter() {
			let approved = Self::bake_referendum(now, index, info);
			ReferendumInfoOf::<T>::insert(index, ReferendumInfo::Finished { end: now, approved });
			weight = max_block_weight;
		}

		// Notes:
		// * We don't consider the lowest unbaked to be the last maturing in case some referenda
		//   have a longer voting period than others.
		// * The iteration here shouldn't trigger any storage read that are not in cache, due to
		//   `maturing_referenda_at_inner` having already read them.
		// * We shouldn't iterate more than `LaunchPeriod/VotingPeriod + 1` times because the number
		//   of unbaked referendum is bounded by this number. In case those number have changed in a
		//   runtime upgrade the formula should be adjusted but the bound should still be sensible.
		<LowestUnbaked<T>>::mutate(|ref_index| {
			while *ref_index < last &&
				Self::referendum_info(*ref_index)
					.map_or(true, |info| matches!(info, ReferendumInfo::Finished { .. }))
			{
				*ref_index += 1
			}
		});

		weight
	}

	/// Reads the length of account in DepositOf without getting the complete value in the runtime.
	///
	/// Return 0 if no deposit for this proposal.
	fn len_of_deposit_of(proposal: PropIndex) -> Option<u32> {
		// DepositOf first tuple element is a vec, decoding its len is equivalent to decode a
		// `Compact<u32>`.
		decode_compact_u32_at(&<DepositOf<T>>::hashed_key_for(proposal))
	}

	/// Return a proposal of an index.
	fn proposal(index: PropIndex) -> Result<(PropIndex, BoundedCallOf<T>, T::AccountId), Error<T>> {
		PublicProps::<T>::get()
			.into_iter()
			.find(|(prop_index, _, _)| prop_index == &index)
			.ok_or(Error::<T>::ProposalMissing)
	}

	/// Clear metadata if exist for a given owner.
	fn clear_metadata(owner: MetadataOwner) {
		if let Some(hash) = MetadataOf::<T>::take(&owner) {
			Self::deposit_event(Event::<T>::MetadataCleared { owner, hash });
		}
	}

	/// Transfer the metadata of an `owner` to a `new_owner`.
	fn transfer_metadata(owner: MetadataOwner, new_owner: MetadataOwner) {
		if let Some(hash) = MetadataOf::<T>::take(&owner) {
			MetadataOf::<T>::insert(&new_owner, hash);
			Self::deposit_event(Event::<T>::MetadataTransferred {
				prev_owner: owner,
				owner: new_owner,
				hash,
			});
		}
	}

	/// Ensure external origin for corresponding vote threshold.
	fn ensure_external_origin(
		threshold: VoteThreshold,
		origin: OriginFor<T>,
	) -> Result<(), BadOrigin> {
		match threshold {
			VoteThreshold::SuperMajorityApprove => {
				let _ = T::ExternalOrigin::ensure_origin(origin)?;
			},
			VoteThreshold::SuperMajorityAgainst => {
				let _ = T::ExternalDefaultOrigin::ensure_origin(origin)?;
			},
			VoteThreshold::SimpleMajority => {
				let _ = T::ExternalMajorityOrigin::ensure_origin(origin)?;
			},
		};
		Ok(())
	}
}

/// Decode `Compact<u32>` from the trie at given key.
fn decode_compact_u32_at(key: &[u8]) -> Option<u32> {
	// `Compact<u32>` takes at most 5 bytes.
	let mut buf = [0u8; 5];
	let bytes = sp_io::storage::read(key, &mut buf, 0)?;
	// The value may be smaller than 5 bytes.
	let mut input = &buf[0..buf.len().min(bytes as usize)];
	match codec::Compact::<u32>::decode(&mut input) {
		Ok(c) => Some(c.0),
		Err(_) => {
			sp_runtime::print("Failed to decode compact u32 at:");
			sp_runtime::print(key);
			None
		},
	}
}
