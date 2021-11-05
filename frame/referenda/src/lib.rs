// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0sp_runtime::{DispatchResult, traits::One}asp_runtime::{DispatchResult, traits::AtLeast32BitUnsigned} in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Assembly Pallet
//!
//! - [`Config`]
//! - [`Call`]
//!
//! ## Overview
//!
//! The Assembly pallet handles the administration of general stakeholder voting.

#![recursion_limit = "256"]
#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode, Input, Codec};
use frame_support::{
	ensure, BoundedVec, weights::Weight, traits::{
		schedule::{DispatchTime, Named as ScheduleNamed},
		BalanceStatus, Currency, Get, LockIdentifier, LockableCurrency, OnUnbalanced,
		ReservableCurrency, WithdrawReasons,
	},
};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{Bounded, Dispatchable, Hash, Saturating, Zero, AtLeast32BitUnsigned, One},
	ArithmeticError, DispatchError, DispatchResult, RuntimeDebug, PerThing, Perbill,
};
use sp_std::prelude::*;

mod conviction;
mod types;
mod vote;
pub mod weights;
pub use conviction::Conviction;
pub use pallet::*;
pub use types::{
	Delegations, ReferendumInfo, ReferendumStatus, Tally, UnvoteScope, TrackInfo, TracksInfo,
	Curve, DecidingStatus, Deposit, AtOrAfter,
};
pub use vote::{AccountVote, Vote, Voting};
pub use weights::WeightInfo;

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
pub mod benchmarking;

const ASSEMBLY_ID: LockIdentifier = *b"assembly";

/// A referendum index.
pub type ReferendumIndex = u32;

type BalanceOf<T> =
	<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
type NegativeImbalanceOf<T> = <<T as Config>::Currency as Currency<
	<T as frame_system::Config>::AccountId,
>>::NegativeImbalance;
type ReferendumInfoOf<T> = ReferendumInfo<
	TrackIdOf<T>,
	<T as frame_system::Config>::Origin,
	<T as frame_system::Config>::BlockNumber,
	<T as frame_system::Config>::Hash,
	BalanceOf<T>,
	BalanceOf<T>,
	<T as frame_system::Config>::AccountId,
>;
type ReferendumStatusOf<T> = ReferendumStatus<
	TrackIdOf<T>,
	<T as frame_system::Config>::Origin,
	<T as frame_system::Config>::BlockNumber,
	<T as frame_system::Config>::Hash,
	BalanceOf<T>,
	BalanceOf<T>,
	<T as frame_system::Config>::AccountId,
>;
type VotingOf<T> = Voting<
	BalanceOf<T>,
	<T as frame_system::Config>::AccountId,
	<T as frame_system::Config>::BlockNumber,
>;
type TracksInfoOf<T> = TracksInfo<
	BalanceOf<T>,
	<T as frame_system::Config>::BlockNumber,
>;
type TrackInfoOf<T> = TrackInfo<
	BalanceOf<T>,
	<T as frame_system::Config>::BlockNumber,
>;
type TrackIdOf<T> = TracksInfoOf<T>::Id;

pub trait InsertSorted<T> {
	fn insert_sorted_by_key(&mut self, t: T) -> bool;
}
impl<T, S: Get<u32>> InsertSorted<T> for BoundedVec<T, S> {
	fn insert_sorted_by_key<
		F: FnMut(&T) -> K,
		K: PartialOrd<K>,
	>(&mut self, t: T, f: F,) -> Result<(), ()> {
		let index = self.binary_search_by_key(&t, f).unwrap_or_else(|x| x);
		if index >= S::get() as usize {
			return Err(())
		}
		self.truncate(S::get() as usize - 1);
		self.insert(index, t);
		Ok(())
	}
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::{
		dispatch::DispatchResultWithPostInfo,
		pallet_prelude::*,
		traits::EnsureOrigin,
		weights::{DispatchClass, Pays},
		Parameter,
	};
	use frame_system::pallet_prelude::*;
	use sp_runtime::DispatchResult;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config + Sized {
		// System level stuff.
		type Proposal: Parameter + Dispatchable<Origin = Self::Origin> + From<Call<Self>>;
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;
		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
		/// The Scheduler.
		type Scheduler: ScheduleNamed<Self::BlockNumber, Self::Proposal, Self::Origin>;
		/// Currency type for this pallet.
		type Currency: ReservableCurrency<Self::AccountId>
			+ LockableCurrency<Self::AccountId, Moment = Self::BlockNumber>;

		// Origins and unbalances.
		/// Origin from which any vote may be cancelled.
		type CancelOrigin: EnsureOrigin<Self::Origin>;
		/// Origin from which any vote may be killed.
		type KillOrigin: EnsureOrigin<Self::Origin>;
		/// Handler for the unbalanced reduction when slashing a preimage deposit.
		type Slash: OnUnbalanced<NegativeImbalanceOf<Self>>;

		// Constants
		/// The minimum amount to be used as a deposit for a public referendum proposal.
		#[pallet::constant]
		type SubmissionDeposit: Get<BalanceOf<Self>>;

		/// The maximum number of concurrent votes an account may have.
		///
		/// Also used to compute weight, an overly large value can
		/// lead to extrinsic with large weight estimation: see `delegate` for instance.
		#[pallet::constant]
		type MaxVotes: Get<u32>;

		/// Maximum size of the referendum queue for a single track.
		#[pallet::constant]
		type MaxQueued: Get<u32>;

		/// The number of blocks after submission that a referendum must begin being decided by.
		/// Once this passes, then anyone may cancel the referendum.
		#[pallet::constant]
		type UndecidingTimeout: Get<Self::BlockNumber>;

		/// The minimum period of vote locking.
		///
		/// It should be no shorter than enactment period to ensure that in the case of an approval,
		/// those successful voters are locked into the consequences that their votes entail.
		#[pallet::constant]
		type VoteLockingPeriod: Get<Self::BlockNumber>;

		/// Quantization level for the referendum wakeup scheduler. A higher number will result in
		/// fewer storage reads/writes needed for smaller voters, but also result in delays to the
		/// automatic referendum status changes. Explicit servicing instructions are unaffected.
		#[pallet::constant]
		type AlarmInterval: Get<Self::BlockNumber>;

		// The other stuff.
		/// Information concerning the different referendum tracks.
		type Tracks: TracksInfo<BalanceOf<Self>, Self::BlockNumber, Origin = Self::Origin>;
	}

	/// The next free referendum index, aka the number of referenda started so far.
	#[pallet::storage]
	pub type ReferendumCount<T> = StorageValue<_, ReferendumIndex, ValueQuery>;

	/// The sorted list of referenda
	/// ready to be decided but not yet being decided, ordered by conviction-weighted approvals.
	///
	/// This should be empty if `DecidingCount` is less than `TrackInfo::max_deciding`.
	#[pallet::storage]
	pub type TrackQueue<T: Config> = StorageMap<
		_,
		Twox64Concat,
		TrackIdOf<T>,
		BoundedVec<(ReferendumIndex, BalanceOf<T>), T::MaxQueued>,
		ValueQuery,
	>;

	/// The number of referenda being decided currently.
	#[pallet::storage]
	pub type DecidingCount<T: Config> = StorageMap<
		_,
		Twox64Concat,
		TrackIdOf<T>,
		u32,
		ValueQuery,
	>;

	/// Information concerning any given referendum.
	///
	/// TWOX-NOTE: SAFE as indexes are not under an attacker’s control.
	#[pallet::storage]
	pub type ReferendumInfoFor<T: Config> = StorageMap<
		_,
		Twox64Concat,
		ReferendumIndex,
		ReferendumInfoOf<T>,
	>;

	/// All votes for a particular voter. We store the balance for the number of votes that we
	/// have recorded. The second item is the total amount of delegations, that will be added.
	///
	/// TWOX-NOTE: SAFE as `AccountId`s are crypto hashes anyway.
	#[pallet::storage]
	pub type VotingFor<T: Config> = StorageMap<
		_,
		Twox64Concat,
		T::AccountId,
		VotingOf<T>,
		ValueQuery,
	>;

	/// Accounts for which there are locks in action which may be removed at some point in the
	/// future. The value is the block number at which the lock expires and may be removed.
	///
	/// TWOX-NOTE: OK ― `AccountId` is a secure hash.
	#[pallet::storage]
	#[pallet::getter(fn locks)]
	pub type Locks<T: Config> = StorageMap<_, Twox64Concat, T::AccountId, T::BlockNumber>;

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
			ReferendumCount::<T>::put(0 as ReferendumIndex);
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// A referendum has being submitted.
		Submitted {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The track (and by extension proposal dispatch origin) of this referendum.
			track: TrackIdOf<T>,
			/// The hash of the proposal up for referendum.
			proposal_hash: T::Hash,
		},
		/// A referendum has moved into the deciding phase.
		StartedDeciding {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The track (and by extension proposal dispatch origin) of this referendum.
			track: TrackIdOf<T>,
			/// The hash of the proposal up for referendum.
			proposal_hash: T::Hash,
			/// The current tally of votes in this referendum.
			tally: Tally<BalanceOf<T>>,
		},
		/// A referendum has ended its confirmation phase and is ready for approval.
		Confirmed {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The final tally of votes in this referendum.
			tally: Tally<BalanceOf<T>>,
		},
		/// A referendum has been approved and its proposal has been scheduled.
		Approved {
			/// Index of the referendum.
			index: ReferendumIndex,
		},
		/// A proposal has been rejected by referendum.
		Rejected {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The final tally of votes in this referendum.
			tally: Tally<BalanceOf<T>>,
		},
		/// A referendum has been timed out without being decided.
		TimedOut {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The final tally of votes in this referendum.
			tally: Tally<BalanceOf<T>>,
		},
		/// A referendum has been cancelled.
		Cancelled {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The final tally of votes in this referendum.
			tally: Tally<BalanceOf<T>>,
		},
		/// A referendum has been killed.
		Killed {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The final tally of votes in this referendum.
			tally: Tally<BalanceOf<T>>,
		},
		/// An account has delegated their vote to another account. \[who, target\]
		Delegated(T::AccountId, T::AccountId),
		/// An \[account\] has cancelled a previous delegation operation.
		Undelegated(T::AccountId),
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Value too low
		ValueLow,
		/// Referendum is not ongoing.
		NotOngoing,
		/// Referendum's decision deposit is already paid.
		HaveDeposit,
		/// Proposal does not exist
		ProposalMissing,
		/// Cannot cancel the same proposal twice
		AlreadyCanceled,
		/// Proposal already made
		DuplicateProposal,
		/// Vote given for invalid referendum
		ReferendumInvalid,
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
		/// Delegation to oneself makes no sense.
		Nonsense,
		/// Invalid upper bound.
		WrongUpperBound,
		/// Maximum number of votes reached.
		MaxVotesReached,
		/// The track identifier given was invalid.
		BadTrack,
		/// There are already a full complement of referendums in progress for this track.
		Full,
		/// The queue of the track is empty.
		QueueEmpty,
		/// The referendum index provided is invalid in this context.
		BadReferendum,
		/// There was nothing to do in the advancement.
		NothingToDo,
	}

	// TODO: bans

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Propose a referendum on a privileged action.
		///
		/// The dispatch origin of this call must be _Signed_ and the sender must
		/// have funds to cover the deposit.
		///
		/// - `proposal_origin`: The origin from which the proposal should be executed.
		/// - `proposal_hash`: The hash of the proposal preimage.
		/// - `enactment_moment`: The moment that the proposal should be enacted.
		///
		/// Emits `Submitted`.
		#[pallet::weight(T::WeightInfo::propose())]
		pub fn submit(
			origin: OriginFor<T>,
			proposal_origin: T::Origin,
			proposal_hash: T::Hash,
			enactment_moment: AtOrAfter<T::BlockNumber>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			let index = ReferendumCount::<T>::mutate(|x| { let r = *x; *x += 1; r });
			let track = T::Tracks::track_for(&proposal_origin);
			let status = ReferendumStatus {
				track,
				origin: proposal_origin,
				proposal_hash: proposal_hash.clone(),
				enactment: enactment_moment,
				submitted: frame_system::Pallet::<T>::block_number(),
				submission_deposit: Self::take_deposit(who, T::SubmissionDeposit::get())?,
				decision_deposit: None,
				deciding: None,
				tally: Tally::default(),
				ayes_in_queue: None,
			};
			ReferendumInfoFor::<T>::insert(index, ReferendumInfo::Ongoing(status));

			Self::deposit_event(Event::<T>::Submitted { index, track, proposal_hash });
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn place_decision_deposit(
			origin: OriginFor<T>,
			index: ReferendumIndex,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let status = Self::ensure_ongoing(index)?;
			ensure!(status.decision_deposit.is_none(), Error::<T>::HaveDeposit);
			let track = Self::track(status.track);
			status.decision_deposit = Self::take_deposit(who, track.decision_deposit)?;
			ReferendumInfoFor::<T>::insert(index, ReferendumInfo::Ongoing(status));
			let now = frame_system::Pallet::<T>::block_number();
			Self::service_referendum(now, index, status);
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn refund_decision_deposit(
			origin: OriginFor<T>,
			index: ReferendumIndex,
		) -> DispatchResult {
			ensure_signed_or_root(origin)?;
			let mut info = ReferendumInfoFor::<T>::get(index).ok_or(Error::<T>::BadReferendum)?;
			Self::refund_deposit(info.take_decision_deposit());
			ReferendumInfoFor::<T>::insert(index, info);
			Ok(())
		}

		///
		#[pallet::weight(0)]
		pub fn consider_referendum(origin: OriginFor<T>, index: ReferendumIndex) -> DispatchResult {
			ensure_signed_or_root(origin)?;
			Self::do_consider_referendum(index)?;
			Ok(Pays::No.into())
		}

		#[pallet::weight(0)]
		pub fn advance_referendum(origin: OriginFor<T>, index: ReferendumIndex) -> DispatchResult {
			ensure_signed_or_root(origin)?;
			Self::do_advance_referendum(index)?;
			Ok(Pays::No.into())
		}

		#[pallet::weight(0)]
		pub fn advance_track(origin: OriginFor<T>, track: TrackIdOf<T>) -> DispatchResult {
			ensure_signed_or_root(origin)?;
			Self::do_advance_track(track)?;
			Ok(Pays::No.into())
		}

		#[pallet::weight(0)]
		pub fn pass_referendum(origin: OriginFor<T>, index: ReferendumIndex) -> DispatchResult {
			ensure_signed(origin)?;
			let info = ReferendumInfoFor::<T>::get(index);
			let mut status = match info {
				ReferendumInfo::Confirmed(status) => status,
				_ => return Err(()),
			};
			Self::refund_deposit(status.decision_deposit.take());

			// Enqueue proposal
			let now = frame_system::Pallet::<T>::block_number();
			let track = Self::track(status.track)?;
			let earliest_allowed = now.saturating_add(track.min_enactment_period);
			let desired = status.enactment.evaluate(now);
			let enactment = desired.max(earliest_allowed);
			let ok = T::Scheduler::schedule_named(
				(ASSEMBLY_ID, index).encode(),
				DispatchTime::At(enactment),
				None,
				63,
				status.origin,
				Call::stub { call_hash: status.proposal_hash }.into(),
			).is_ok();
			debug_assert!(ok, "LOGIC ERROR: bake_referendum/schedule_named failed");

			Self::deposit_event(Event::<T>::Approved { index });

			let info = ReferendumInfo::Approved(status.submission_deposit);
			ReferendumStatusOf::<T>::insert(index, info);

			Ok(Pays::No.into())
		}

		/// Just a stub - not meant to do anything.
		#[pallet::weight(0)]
		pub fn stub(_origin: OriginFor<T>, _call_hash: T::Hash) -> DispatchResult { Ok(()) }
	}
}

impl<T: Config> Pallet<T> {
	pub fn ensure_ongoing(index: ReferendumIndex) -> Result<ReferendumStatusOf<T>, DispatchError> {
		match ReferendumInfoFor::<T>::get(index) {
			ReferendumInfo::Ongoing(status) => Ok(status),
			_ => Err(Error::<T>::NotOngoing.into()),
		}
	}

	fn set_referendum_alarm(index: ReferendumIndex, when: T::BlockNumber) -> bool {
		let scheduler_id = (ASSEMBLY_ID, "referendum", index).encode();
		Self::set_alarm(scheduler_id, Call::advance_referendum { index }, when)
	}

	fn set_track_alarm(track: TrackIdOf<T>, when: T::BlockNumber) -> bool {
		let scheduler_id = (ASSEMBLY_ID, "track", track).encode();
		Self::set_alarm(scheduler_id, Call::advance_track { track }, when)
	}

	/// Returns `false` if there is no change.
	fn set_alarm(id: Vec<u8>, call: impl Into<T::Call>, when: T::BlockNumber) -> bool {
		let alarm_interval = T::AlarmInterval::get();
		let when = (when / alarm_interval + 1) * alarm_interval;
		if let Ok(t) = T::Scheduler::next_dispatch_time(id.clone()) {
			if t == when {
				return false
			}
			let ok = T::Scheduler::reschedule_named(id, when).is_ok();
			debug_assert!(ok, "Unable to reschedule an extant referendum?!");
		} else {
			let _ = T::Scheduler::cancel_named(id.clone());
			let ok = T::Scheduler::schedule_named(
				id,
				when,
				None,
				128u8,
				frame_system::Origin::Root.into(),
				call.into(),
			).is_ok();
			debug_assert!(ok, "Unable to schedule a new referendum?!");
		}
		true
	}

	fn ready_for_deciding(
		now: T::BlockNumber,
		track: &TrackInfoOf<T>,
		index: ReferendumIndex,
		status: &mut ReferendumStatusOf<T>,
	) {
		let deciding_count = DecidingCount::<T>::get(status.track);
		if deciding_count < track.max_deciding {
			// Begin deciding.
			status.begin_deciding(now, track.decision_period);
			DecidingCount::<T>::insert(status.track, deciding_count.saturating_add(1));
		} else {
			// Add to queue.
			let item = (index, status.tally.ayes);
			TrackQueue::<T>::mutate(status.track, |q| q.insert_sorted_by_key(item, |x| x.1))
		}
	}

	/// Grab the index and status for the referendum which is the highest priority of those for the
	/// given track which are ready for being decided.
	fn next_for_deciding(track_queue: BoundedVec<(u32, BalanceOf<T>), T::MaxQueued>) -> Option<(ReferendumIndex, ReferendumStatusOf<T>)> {
		loop {
			let (index, _) = track_queue.pop()?;
			match Self::ensure_ongoing(index) {
				Ok(s) => return Some((index, s)),
				Err() => debug_assert!(false, "Queued referendum not ongoing?!"),
			}
		}
	}

	/// Advance a track - this dequeues one or more referenda from the from the `TrackQueue` of
	/// referenda which are ready to be decided until the `DecidingCount` is equal to the track's
	/// `max_deciding`.
	fn do_advance_track(track: TrackIdOf<T>) -> Result<u32, DispatchError> {
		let track_info = Self::track(track).ok_or(Error::<T>::BadTrack)?;
		let deciding_count = DecidingCount::<T>::get(track);
		let track_queue = TrackQueue::<T>::get(track);
		let count = 0;
		while deciding_count < track_info.max_deciding {
			if let Some((index, mut status)) = Self::next_for_deciding(&mut track_queue) {
				let now = frame_system::Pallet::<T>::block_number();
				status.begin_deciding(now, track_info.decision_period);
				ReferendumInfoFor::<T>::insert(index, ReferendumInfo::Ongoing(status));
				deciding_count.saturating_inc();
				count.saturating_inc();
			} else {
				break
			}
		}
		ensure!(count > 0, Error::<T>::NothingToDo);

		DecidingCount::<T>::insert(track, deciding_count);
		TrackQueue::<T>::insert(track, track_queue);
		Ok(count)
	}

	// TODO: if a vote results in `ayes_in_queue.map_or(false, |v| tally.ayes > v)` then schedule
	// the referendum alarm to update `TrackQueue` - could either update entry's position or move
	// index in.

	/// Applies only to referendums in the `TrackQueue`.
	///
	/// Checks a referendum's aye votes and if above the lowest in its `TrackQueue` or if
	/// `TrackQueue` is below capacity then inserts it into its `TrackQueue`.
	fn do_consider_referendum(index: ReferendumIndex) -> DispatchResult {
		let now = frame_system::Pallet::<T>::block_number();
		let status = Self::ensure_ongoing(index)?;
		if let Some(info) = Self::service_referendum(now, status) {
			if let ReferendumInfo::Ongoing(&status) = info {
				let when = Self::next_referendum_advance(&status).max(now + One::one());
				Self::set_referendum_alarm(index, when);
			}
			ReferendumInfoFor::<T>::insert(index, info);
		}
	}

	// TODO: If a vote results in `ayes_in_queue.map_or(false, |v| tally.ayes < v)` then it must
	// include a reorder of the queue.

	/// Applies only to referendums in the `TrackQueue`.
	///
	/// Updates the referendum's aye votes into `ayes_in_queue` and into `TrackQueue` and then
	/// sort the queue.
	fn do_reconsider_referendum(index: ReferendumIndex) -> DispatchResult {
		let now = frame_system::Pallet::<T>::block_number();
		let status = Self::ensure_ongoing(index)?;
		if let Some(info) = Self::service_referendum(now, status) {
			if let ReferendumInfo::Ongoing(&status) = info {
				let when = Self::next_referendum_advance(&status).max(now + One::one());
				Self::set_referendum_alarm(index, when);
			}
			ReferendumInfoFor::<T>::insert(index, info);
		}
	}

	/// Attempts to advance the referendum. Returns `Ok` if something useful happened.
	fn do_advance_referendum(index: ReferendumIndex) -> DispatchResult {
		let now = frame_system::Pallet::<T>::block_number();
		let status = Self::ensure_ongoing(index)?;
		if let Some(info) = Self::service_referendum(now, status) {
			if let ReferendumInfo::Ongoing(&status) = info {
				let when = Self::next_referendum_advance(&status).max(now + One::one());
				Self::set_referendum_alarm(index, when);
			}
			ReferendumInfoFor::<T>::insert(index, info);
		}
	}

	/// Advance the state of a referendum, which comes down to:
	/// - If it's ready to be decided, start deciding;
	/// - If it's not ready to be decided and non-deciding timeout has passed, fail;
	/// - If it's ongoing and passing, ensure confirming; if at end of confirmation period, pass.
	/// - If it's ongoing and not passing, stop confirning; if it has reached end time, fail.
	///
	/// Weight will be a bit different depending on what it does, but if designed so as not to
	/// differ dramatically. In particular there are no balance operations.
	fn service_referendum(
		now: T::BlockNumber,
		index: ReferendumIndex,
		mut status: ReferendumStatusOf<T>,
	) -> Option<ReferendumInfoOf<T>> {
		// Should it begin being decided?
		let track = Self::track(status.track)?;
		if status.deciding.is_none() && status.decision_deposit.is_some() {
			if now.saturating_sub(status.submitted) >= track.prepare_period {
				Self::ready_for_deciding(now, &track, &mut status);
			}
		}
		if let Some(deciding) = &mut status.deciding {
			let is_passing = status.tally.is_passing(
				now,
				deciding.period,
				T::Currency::total_issuance(),
				track.min_turnout,
				track.min_approvals,
			);
			if let Some(confirming) = deciding.confirming {
				if is_passing && confirming >= now {
					// Passed!
					DecidingCount::<T>::mutate(status.track, |x| x.saturating_dec());
					Self::deposit_event(Event::<T>::Confirmed { index, tally: status.tally });
					return Some(ReferendumInfo::Confirmed(status))
				} else if !is_passing {
					// Move back out of confirming
					deciding.confirming = None;
				}
			}
			if deciding.confirming.is_none() {
				if is_passing {
					// Begin confirming
					deciding.confirming = Some(now.saturating_add(track.confirm_period));
				} else if now >= deciding.ending {
					// Failed!
					DecidingCount::<T>::mutate(status.track, |x| x.saturating_dec());
					Self::deposit_event(Event::<T>::Rejected { index, tally: status.tally });
					return Some(ReferendumInfo::Rejected(status.submission_deposit, status.decision_deposit))
				}
			}
		} else if status.submitted.saturating_add(T::UndecidingTimeout::get()) >= now {
			// Too long without being decided.
			Self::deposit_event(Event::<T>::TimedOut { index, tally: status.tally });
			return Some(ReferendumInfo::TimedOut(status.submission_deposit, status.decision_deposit))
		}
		Some(ReferendumInfo::Ongoing(status))
	}

	/// Reserve a deposit and return the `Deposit` instance.
	fn take_deposit(who: T::AccountId, amount: BalanceOf<T>)
		-> Result<Deposit<T::AccountId, BalanceOf<T>>, DispatchError>
	{
		T::Currency::reserve(&who, amount)?;
		Ok(Deposit { who, amount })
	}

	/// Return a deposit, if `Some`.
	fn refund_deposit(deposit: Option<Deposit<T::AccountId, BalanceOf<T>>>) {
		if let Some(Deposit { who, amount }) = deposit {
			T::Currency::unreserve(&who, amount);
		}
	}

	/// Returns the earliest block that advancing this referendum should do something useful.
	pub fn next_referendum_advance(status: &ReferendumStatusOf<T>) -> T::BlockNumber {
		let now = frame_system::Pallet::<T>::block_number();
		let track = match Self::track(status.track) {
			Some(t) => t,
			None => return now,
		};
		if let Some(deciding) = status.deciding {
			if let Some(confirming) = deciding.confirming {
				confirming
			} else {
				let mut t = deciding.ending;
				let approvals = Perbill::from_rational(status.tally.ayes, status.tally.ayes + status.tally.nays);
				let turnout = Perbill::from_rational(status.tally.turnout, T::Currency::total_issuance());
				let until_approvals = track.min_approvals.delay(approvals) * deciding.period;
				let until_turnout = track.min_turnout.delay(turnout) * deciding.period;
				t.min(until_turnout.max(until_approvals))
			}
		} else {
			if status.decision_deposit.is_some() {
				let prepare_end = status.submitted.saturating_add(track.prepare_period);
				if now < prepare_end {
					prepare_end
				} else {
					// Not yet bumped or too many being decided.
					// Track should already be scheduled for a bump.
					status.submitted + T::UndecidingTimeout::get()
				}
			} else {
				status.submitted + T::UndecidingTimeout::get()
			}
		}
	}

	fn track(id: TrackIdOf<T>) -> Option<&'static TrackInfoOf<T>> {
		let tracks = T::Tracks::tracks();
		let index = tracks.binary_search_by_key(&id, |x| x.0)
    		.unwrap_or_else(|x| x);
		tracks[index].1
	}
}

/*
		/// Vote in a referendum. If `vote.is_aye()`, the vote is to enact the proposal;
		/// otherwise it is a vote to keep the status quo.
		///
		/// The dispatch origin of this call must be _Signed_.
		///
		/// - `ref_index`: The index of the referendum to vote for.
		/// - `vote`: The vote configuration.
		///
		/// Weight: `O(R)` where R is the number of referenda the voter has voted on.
		#[pallet::weight(
			T::WeightInfo::vote_new(T::MaxVotes::get())
				.max(T::WeightInfo::vote_existing(T::MaxVotes::get()))
		)]
		pub fn vote(
			origin: OriginFor<T>,
			#[pallet::compact] ref_index: ReferendumIndex,
			vote: AccountVote<BalanceOf<T>>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			Self::try_vote(&who, ref_index, vote)
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
		/// Weight: `O(R)` where R is the number of referenda the voter delegating to has
		///   voted on. Weight is charged as if maximum votes.
		// NOTE: weight must cover an incorrect voting of origin with max votes, this is ensure
		// because a valid delegation cover decoding a direct voting with max votes.
		#[pallet::weight(T::WeightInfo::delegate(T::MaxVotes::get()))]
		pub fn delegate(
			origin: OriginFor<T>,
			to: T::AccountId,
			conviction: Conviction,
			balance: BalanceOf<T>,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
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
		/// Weight: `O(R)` where R is the number of referenda the voter delegating to has
		///   voted on. Weight is charged as if maximum votes.
		// NOTE: weight must cover an incorrect voting of origin with max votes, this is ensure
		// because a valid delegation cover decoding a direct voting with max votes.
		#[pallet::weight(T::WeightInfo::undelegate(T::MaxVotes::get().into()))]
		pub fn undelegate(origin: OriginFor<T>) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let votes = Self::try_undelegate(who)?;
			Ok(Some(T::WeightInfo::undelegate(votes)).into())
		}

		/// Unlock tokens that have an expired lock.
		///
		/// The dispatch origin of this call must be _Signed_.
		///
		/// - `target`: The account to remove the lock on.
		///
		/// Weight: `O(R)` with R number of vote of target.
		#[pallet::weight(
			T::WeightInfo::unlock_set(T::MaxVotes::get())
				.max(T::WeightInfo::unlock_remove(T::MaxVotes::get()))
		)]
		pub fn unlock(origin: OriginFor<T>, target: T::AccountId) -> DispatchResult {
			ensure_signed(origin)?;
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
		#[pallet::weight(T::WeightInfo::remove_other_vote(T::MaxVotes::get()))]
		pub fn remove_other_vote(
			origin: OriginFor<T>,
			target: T::AccountId,
			index: ReferendumIndex,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;
			let scope = if target == who { UnvoteScope::Any } else { UnvoteScope::OnlyExpired };
			Self::try_remove_vote(&target, index, scope)?;
			Ok(())
		}

impl<T: Config> Pallet<T> {
	/// Actually enact a vote, if legit.
	fn try_vote(
		who: &T::AccountId,
		ref_index: ReferendumIndex,
		vote: AccountVote<BalanceOf<T>>,
	) -> DispatchResult {
		let mut status = Self::referendum_status(ref_index)?;
		ensure!(vote.balance() <= T::Currency::free_balance(who), Error::<T>::InsufficientFunds);
		VotingFor::<T>::try_mutate(who, |voting| -> DispatchResult {
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
						ensure!(
							votes.len() as u32 <= T::MaxVotes::get(),
							Error::<T>::MaxVotesReached
						);
						votes.insert(i, (ref_index, vote));
					},
				}
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
		T::Currency::extend_lock(ASSEMBLY_ID, who, vote.balance(), WithdrawReasons::TRANSFER);
		ReferendumInfoFor::<T>::insert(ref_index, ReferendumInfo::Ongoing(status));
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
		let info = ReferendumInfoFor::<T>::get(ref_index);
		VotingFor::<T>::try_mutate(who, |voting| -> DispatchResult {
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
						ReferendumInfoFor::<T>::insert(ref_index, ReferendumInfo::Ongoing(status));
					},
					Some(ReferendumInfo::Finished { end, approved }) => {
						if let Some((lock_periods, balance)) = votes[i].1.locked_if(approved) {
							let unlock_at = end + T::VoteLockingPeriod::get() * lock_periods.into();
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
		VotingFor::<T>::mutate(who, |voting| match voting {
			Voting::Delegating { delegations, .. } => {
				// We don't support second level delegating, so we don't need to do anything more.
				*delegations = delegations.saturating_add(amount);
				1
			},
			Voting::Direct { votes, delegations, .. } => {
				*delegations = delegations.saturating_add(amount);
				for &(ref_index, account_vote) in votes.iter() {
					if let AccountVote::Standard { vote, .. } = account_vote {
						ReferendumInfoFor::<T>::mutate(ref_index, |maybe_info| {
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
		VotingFor::<T>::mutate(who, |voting| match voting {
			Voting::Delegating { delegations, .. } => {
				// We don't support second level delegating, so we don't need to do anything more.
				*delegations = delegations.saturating_sub(amount);
				1
			},
			Voting::Direct { votes, delegations, .. } => {
				*delegations = delegations.saturating_sub(amount);
				for &(ref_index, account_vote) in votes.iter() {
					if let AccountVote::Standard { vote, .. } = account_vote {
						ReferendumInfoFor::<T>::mutate(ref_index, |maybe_info| {
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
		let votes = VotingFor::<T>::try_mutate(&who, |voting| -> Result<u32, DispatchError> {
			let mut old = Voting::Delegating {
				balance,
				target: target.clone(),
				conviction,
				delegations: Default::default(),
				prior: Default::default(),
			};
			sp_std::mem::swap(&mut old, voting);
			match old {
				Voting::Delegating { balance, target, conviction, delegations, prior, .. } => {
					// remove any delegation votes to our current target.
					Self::reduce_upstream_delegation(&target, conviction.votes(balance));
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
			T::Currency::extend_lock(ASSEMBLY_ID, &who, balance, WithdrawReasons::TRANSFER);
			Ok(votes)
		})?;
		Self::deposit_event(Event::<T>::Delegated(who, target));
		Ok(votes)
	}

	/// Attempt to end the current delegation.
	///
	/// Return the number of votes of upstream.
	fn try_undelegate(who: T::AccountId) -> Result<u32, DispatchError> {
		let votes = VotingFor::<T>::try_mutate(&who, |voting| -> Result<u32, DispatchError> {
			let mut old = Voting::default();
			sp_std::mem::swap(&mut old, voting);
			match old {
				Voting::Delegating { balance, target, conviction, delegations, mut prior } => {
					// remove any delegation votes to our current target.
					let votes =
						Self::reduce_upstream_delegation(&target, conviction.votes(balance));
					let now = frame_system::Pallet::<T>::block_number();
					let lock_periods = conviction.lock_periods().into();
					prior.accumulate(now + T::VoteLockingPeriod::get() * lock_periods, balance);
					voting.set_common(delegations, prior);

					Ok(votes)
				},
				Voting::Direct { .. } => Err(Error::<T>::NotDelegating.into()),
			}
		})?;
		Self::deposit_event(Event::<T>::Undelegated(who));
		Ok(votes)
	}

	/// Rejig the lock on an account. It will never get more stringent (since that would indicate
	/// a security hole) but may be reduced from what they are currently.
	fn update_lock(who: &T::AccountId) {
		let lock_needed = VotingFor::<T>::mutate(who, |voting| {
			voting.rejig(frame_system::Pallet::<T>::block_number());
			voting.locked_balance()
		});
		if lock_needed.is_zero() {
			T::Currency::remove_lock(ASSEMBLY_ID, who);
		} else {
			T::Currency::set_lock(ASSEMBLY_ID, who, lock_needed, WithdrawReasons::TRANSFER);
		}
	}
}
*/