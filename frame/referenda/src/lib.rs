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

//! # Referenda Pallet
//!
//! ## Overview
//!
//! A pallet for executing referenda. No voting logic is present here, and the `Polling` and
//! `PollStatus` traits are used to allow the voting logic (likely in a pallet) to be utilized.
//!
//! A referendum is a vote on whether a proposal should be dispatched from a particular origin. The
//! origin is used to determine which one of several _tracks_ that a referendum happens under.
//! Tracks each have their own configuration which governs the voting process and parameters.
//!
//! A referendum's lifecycle has three main stages: Preparation, deciding and conclusion.
//! Referenda are considered "ongoing" immediately after submission until their eventual
//! conclusion, and votes may be cast throughout.
//!
//! In order to progress from preparating to being decided, three things must be in place:
//! - There must have been a *Decision Deposit* placed, an amount determined by the track. Anyone
//! may place this deposit.
//! - A period must have elapsed since submission of the referendum. This period is known as the
//! *Preparation Period* and is determined by the track.
//! - The track must not already be at capacity with referendum being decided. The maximum number of
//! referenda which may be being decided simultaneously is determined by the track.
//!
//! In order to become concluded, one of three things must happen:
//! - The referendum should remain in an unbroken _Passing_ state for a period of time. This
//! is known as the _Confirmation Period_ and is determined by the track. A referendum is considered
//! _Passing_ when there is a sufficiently high turnout and approval, given the amount of time it
//! has been being decided. Generally the threshold for what counts as being "sufficiently high"
//! will reduce over time. The curves setting these thresholds are determined by the track. In this
//! case, the referendum is considered _Approved_ and the proposal is scheduled for dispatch.
//! - The referendum reaches the end of its deciding phase outside not _Passing_. It ends in
//! rejection and the proposal is not dispatched.
//! - The referendum is cancelled.
//!
//! A general time-out is also in place and referenda which exist in preparation for too long may
//! conclude without ever entering into a deciding stage.
//!
//! Once a referendum is concluded, the decision deposit may be refunded.
//!
//! - [`Config`]
//! - [`Call`]

#![recursion_limit = "256"]
#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Codec, Encode};
use frame_support::{
	ensure,
	traits::{
		schedule::{
			v2::{Anon as ScheduleAnon, Named as ScheduleNamed},
			DispatchTime, MaybeHashed,
		},
		Currency, Get, LockIdentifier, LockableCurrency, OnUnbalanced, OriginTrait, PollStatus,
		Polling, ReservableCurrency, VoteTally,
	},
	BoundedVec,
};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{AtLeast32BitUnsigned, Dispatchable, One, Saturating, Zero},
	DispatchError, Perbill,
};
use sp_std::{fmt::Debug, prelude::*};

mod branch;
mod types;
pub mod weights;
use branch::{BeginDecidingBranch, OneFewerDecidingBranch, ServiceBranch};
pub use pallet::*;
pub use types::{
	AtOrAfter, BalanceOf, CallOf, Curve, DecidingStatus, DecidingStatusOf, Deposit, InsertSorted,
	NegativeImbalanceOf, PalletsOriginOf, ReferendumIndex, ReferendumInfo, ReferendumInfoOf,
	ReferendumStatus, ReferendumStatusOf, ScheduleAddressOf, TallyOf, TrackIdOf, TrackInfo,
	TrackInfoOf, TracksInfo, VotesOf,
};
pub use weights::WeightInfo;

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
pub mod benchmarking;

const ASSEMBLY_ID: LockIdentifier = *b"assembly";

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::{pallet_prelude::*, traits::EnsureOrigin, Parameter};
	use frame_system::pallet_prelude::*;
	use sp_runtime::DispatchResult;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::without_storage_info]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config + Sized {
		// System level stuff.
		type Call: Parameter + Dispatchable<Origin = Self::Origin> + From<Call<Self>>;
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;
		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
		/// The Scheduler.
		type Scheduler: ScheduleAnon<Self::BlockNumber, CallOf<Self>, PalletsOriginOf<Self>, Hash = Self::Hash>
			+ ScheduleNamed<Self::BlockNumber, CallOf<Self>, PalletsOriginOf<Self>, Hash = Self::Hash>;
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
		/// The counting type for votes. Usually just balance.
		type Votes: AtLeast32BitUnsigned + Copy + Parameter + Member;
		/// The tallying type.
		type Tally: VoteTally<Self::Votes> + Default + Clone + Codec + Eq + Debug + TypeInfo;

		// Constants
		/// The minimum amount to be used as a deposit for a public referendum proposal.
		#[pallet::constant]
		type SubmissionDeposit: Get<BalanceOf<Self>>;

		/// Maximum size of the referendum queue for a single track.
		#[pallet::constant]
		type MaxQueued: Get<u32>;

		/// The number of blocks after submission that a referendum must begin being decided by.
		/// Once this passes, then anyone may cancel the referendum.
		#[pallet::constant]
		type UndecidingTimeout: Get<Self::BlockNumber>;

		/// Quantization level for the referendum wakeup scheduler. A higher number will result in
		/// fewer storage reads/writes needed for smaller voters, but also result in delays to the
		/// automatic referendum status changes. Explicit servicing instructions are unaffected.
		#[pallet::constant]
		type AlarmInterval: Get<Self::BlockNumber>;

		// The other stuff.
		/// Information concerning the different referendum tracks.
		type Tracks: TracksInfo<
			BalanceOf<Self>,
			Self::BlockNumber,
			Origin = <Self::Origin as OriginTrait>::PalletsOrigin,
		>;
	}

	/// The next free referendum index, aka the number of referenda started so far.
	#[pallet::storage]
	pub type ReferendumCount<T> = StorageValue<_, ReferendumIndex, ValueQuery>;

	/// Information concerning any given referendum.
	///
	/// TWOX-NOTE: SAFE as indexes are not under an attacker’s control.
	#[pallet::storage]
	pub type ReferendumInfoFor<T: Config> =
		StorageMap<_, Blake2_128Concat, ReferendumIndex, ReferendumInfoOf<T>>;

	/// The sorted list of referenda ready to be decided but not yet being decided, ordered by
	/// conviction-weighted approvals.
	///
	/// This should be empty if `DecidingCount` is less than `TrackInfo::max_deciding`.
	#[pallet::storage]
	pub type TrackQueue<T: Config> = StorageMap<
		_,
		Twox64Concat,
		TrackIdOf<T>,
		BoundedVec<(ReferendumIndex, T::Votes), T::MaxQueued>,
		ValueQuery,
	>;

	/// The number of referenda being decided currently.
	#[pallet::storage]
	pub type DecidingCount<T: Config> = StorageMap<_, Twox64Concat, TrackIdOf<T>, u32, ValueQuery>;

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
		/// The decision deposit has been placed.
		DecisionDepositPlaced {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The account who placed the deposit.
			who: T::AccountId,
			/// The amount placed by the account.
			amount: BalanceOf<T>,
		},
		/// The decision deposit has been refunded.
		DecisionDepositRefunded {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The account who placed the deposit.
			who: T::AccountId,
			/// The amount placed by the account.
			amount: BalanceOf<T>,
		},
		/// A deposit has been slashaed.
		DepositSlashed {
			/// The account who placed the deposit.
			who: T::AccountId,
			/// The amount placed by the account.
			amount: BalanceOf<T>,
		},
		/// A referendum has moved into the deciding phase.
		DecisionStarted {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The track (and by extension proposal dispatch origin) of this referendum.
			track: TrackIdOf<T>,
			/// The hash of the proposal up for referendum.
			proposal_hash: T::Hash,
			/// The current tally of votes in this referendum.
			tally: T::Tally,
		},
		ConfirmStarted {
			/// Index of the referendum.
			index: ReferendumIndex,
		},
		ConfirmAborted {
			/// Index of the referendum.
			index: ReferendumIndex,
		},
		/// A referendum has ended its confirmation phase and is ready for approval.
		Confirmed {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The final tally of votes in this referendum.
			tally: T::Tally,
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
			tally: T::Tally,
		},
		/// A referendum has been timed out without being decided.
		TimedOut {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The final tally of votes in this referendum.
			tally: T::Tally,
		},
		/// A referendum has been cancelled.
		Cancelled {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The final tally of votes in this referendum.
			tally: T::Tally,
		},
		/// A referendum has been killed.
		Killed {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The final tally of votes in this referendum.
			tally: T::Tally,
		},
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Referendum is not ongoing.
		NotOngoing,
		/// Referendum's decision deposit is already paid.
		HaveDeposit,
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
		/// No track exists for the proposal origin.
		NoTrack,
		/// Any deposit cannot be refunded until after the decision is over.
		Unfinished,
		/// The deposit refunder is not the depositor.
		NoPermission,
		/// The deposit cannot be refunded since none was made.
		NoDeposit,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Propose a referendum on a privileged action.
		///
		/// - `origin`: must be `Signed` and the account must have `SubmissionDeposit` funds
		///   available.
		/// - `proposal_origin`: The origin from which the proposal should be executed.
		/// - `proposal_hash`: The hash of the proposal preimage.
		/// - `enactment_moment`: The moment that the proposal should be enacted.
		///
		/// Emits `Submitted`.
		#[pallet::weight(T::WeightInfo::submit())]
		pub fn submit(
			origin: OriginFor<T>,
			proposal_origin: PalletsOriginOf<T>,
			proposal_hash: T::Hash,
			enactment_moment: AtOrAfter<T::BlockNumber>,
		) -> DispatchResult {
			let who = ensure_signed(origin)?;

			let track = T::Tracks::track_for(&proposal_origin).map_err(|_| Error::<T>::NoTrack)?;
			let submission_deposit = Self::take_deposit(who, T::SubmissionDeposit::get())?;
			let index = ReferendumCount::<T>::mutate(|x| {
				let r = *x;
				*x += 1;
				r
			});
			let now = frame_system::Pallet::<T>::block_number();
			let nudge_call = Call::nudge_referendum { index };
			let status = ReferendumStatus {
				track,
				origin: proposal_origin,
				proposal_hash: proposal_hash.clone(),
				enactment: enactment_moment,
				submitted: now,
				submission_deposit,
				decision_deposit: None,
				deciding: None,
				tally: Default::default(),
				in_queue: false,
				alarm: Self::set_alarm(nudge_call, now.saturating_add(T::UndecidingTimeout::get())),
			};
			ReferendumInfoFor::<T>::insert(index, ReferendumInfo::Ongoing(status));

			Self::deposit_event(Event::<T>::Submitted { index, track, proposal_hash });
			Ok(())
		}

		/// Post the Decision Deposit for a referendum.
		///
		/// - `origin`: must be `Signed` and the account must have funds available for the
		///   referendum's track's Decision Deposit.
		/// - `index`: The index of the submitted referendum whose Decision Deposit is yet to be
		///   posted.
		///
		/// Emits `DecisionDepositPlaced`.
		#[pallet::weight(ServiceBranch::max_weight_of_deposit::<T>())]
		pub fn place_decision_deposit(
			origin: OriginFor<T>,
			index: ReferendumIndex,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let mut status = Self::ensure_ongoing(index)?;
			ensure!(status.decision_deposit.is_none(), Error::<T>::HaveDeposit);
			let track = Self::track(status.track).ok_or(Error::<T>::NoTrack)?;
			status.decision_deposit =
				Some(Self::take_deposit(who.clone(), track.decision_deposit)?);
			let now = frame_system::Pallet::<T>::block_number();
			let (info, _, branch) = Self::service_referendum(now, index, status);
			ReferendumInfoFor::<T>::insert(index, info);
			let e =
				Event::<T>::DecisionDepositPlaced { index, who, amount: track.decision_deposit };
			Self::deposit_event(e);
			Ok(branch.weight_of_deposit::<T>().into())
		}

		/// Refund the Decision Deposit for a closed referendum back to the depositor.
		///
		/// - `origin`: must be `Signed` or `Root`.
		/// - `index`: The index of a closed referendum whose Decision Deposit has not yet been
		///   refunded.
		///
		/// Emits `DecisionDepositRefunded`.
		#[pallet::weight(T::WeightInfo::refund_decision_deposit())]
		pub fn refund_decision_deposit(
			origin: OriginFor<T>,
			index: ReferendumIndex,
		) -> DispatchResult {
			ensure_signed_or_root(origin)?;
			let mut info = ReferendumInfoFor::<T>::get(index).ok_or(Error::<T>::BadReferendum)?;
			let deposit = info
				.take_decision_deposit()
				.map_err(|_| Error::<T>::Unfinished)?
				.ok_or(Error::<T>::NoDeposit)?;
			Self::refund_deposit(Some(deposit.clone()));
			ReferendumInfoFor::<T>::insert(index, info);
			let e = Event::<T>::DecisionDepositRefunded {
				index,
				who: deposit.who,
				amount: deposit.amount,
			};
			Self::deposit_event(e);
			Ok(())
		}

		/// Cancel an ongoing referendum.
		///
		/// - `origin`: must be the `CancelOrigin`.
		/// - `index`: The index of the referendum to be cancelled.
		///
		/// Emits `Cancelled`.
		#[pallet::weight(T::WeightInfo::cancel())]
		pub fn cancel(origin: OriginFor<T>, index: ReferendumIndex) -> DispatchResult {
			T::CancelOrigin::ensure_origin(origin)?;
			let status = Self::ensure_ongoing(index)?;
			if let Some((_, last_alarm)) = status.alarm {
				let _ = T::Scheduler::cancel(last_alarm);
			}
			Self::note_one_fewer_deciding(status.track);
			Self::deposit_event(Event::<T>::Cancelled { index, tally: status.tally });
			let info = ReferendumInfo::Cancelled(
				frame_system::Pallet::<T>::block_number(),
				status.submission_deposit,
				status.decision_deposit,
			);
			ReferendumInfoFor::<T>::insert(index, info);
			Ok(())
		}

		/// Cancel an ongoing referendum and slash the deposits.
		///
		/// - `origin`: must be the `KillOrigin`.
		/// - `index`: The index of the referendum to be cancelled.
		///
		/// Emits `Killed` and `DepositSlashed`.
		#[pallet::weight(T::WeightInfo::kill())]
		pub fn kill(origin: OriginFor<T>, index: ReferendumIndex) -> DispatchResult {
			T::KillOrigin::ensure_origin(origin)?;
			let status = Self::ensure_ongoing(index)?;
			if let Some((_, last_alarm)) = status.alarm {
				let _ = T::Scheduler::cancel(last_alarm);
			}
			Self::note_one_fewer_deciding(status.track);
			Self::deposit_event(Event::<T>::Killed { index, tally: status.tally });
			Self::slash_deposit(Some(status.submission_deposit.clone()));
			Self::slash_deposit(status.decision_deposit.clone());
			let info = ReferendumInfo::Killed(frame_system::Pallet::<T>::block_number());
			ReferendumInfoFor::<T>::insert(index, info);
			Ok(())
		}

		/// Advance a referendum onto its next logical state. Only used internally.
		///
		/// - `origin`: must be `Root`.
		/// - `index`: the referendum to be advanced.
		#[pallet::weight(ServiceBranch::max_weight_of_nudge::<T>())]
		pub fn nudge_referendum(
			origin: OriginFor<T>,
			index: ReferendumIndex,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			let now = frame_system::Pallet::<T>::block_number();
			let mut status = Self::ensure_ongoing(index)?;
			// This is our wake-up, so we can disregard the alarm.
			status.alarm = None;
			let (info, dirty, branch) = Self::service_referendum(now, index, status);
			if dirty {
				ReferendumInfoFor::<T>::insert(index, info);
			}
			Ok(Some(branch.weight_of_nudge::<T>()).into())
		}

		/// Advance a track onto its next logical state. Only used internally.
		///
		/// - `origin`: must be `Root`.
		/// - `track`: the track to be advanced.
		///
		/// Action item for when there is now one fewer referendum in the deciding phase and the
		/// `DecidingCount` is not yet updated. This means that we should either:
		/// - begin deciding another referendum (and leave `DecidingCount` alone); or
		/// - decrement `DecidingCount`.
		#[pallet::weight(OneFewerDecidingBranch::max_weight::<T>())]
		pub fn one_fewer_deciding(
			origin: OriginFor<T>,
			track: TrackIdOf<T>,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			let track_info = T::Tracks::info(track).ok_or(Error::<T>::BadTrack)?;
			let mut track_queue = TrackQueue::<T>::get(track);
			let branch =
				if let Some((index, mut status)) = Self::next_for_deciding(&mut track_queue) {
					let now = frame_system::Pallet::<T>::block_number();
					let (maybe_alarm, branch) =
						Self::begin_deciding(&mut status, index, now, track_info);
					if let Some(set_alarm) = maybe_alarm {
						Self::ensure_alarm_at(&mut status, index, set_alarm);
					}
					ReferendumInfoFor::<T>::insert(index, ReferendumInfo::Ongoing(status));
					TrackQueue::<T>::insert(track, track_queue);
					branch.into()
				} else {
					DecidingCount::<T>::mutate(track, |x| x.saturating_dec());
					OneFewerDecidingBranch::QueueEmpty
				};
			Ok(Some(branch.weight::<T>()).into())
		}
	}
}

impl<T: Config> Polling<T::Tally> for Pallet<T> {
	type Index = ReferendumIndex;
	type Votes = VotesOf<T>;
	type Moment = T::BlockNumber;
	type Class = TrackIdOf<T>;

	fn classes() -> Vec<Self::Class> {
		T::Tracks::tracks().iter().map(|x| x.0).collect()
	}

	fn access_poll<R>(
		index: Self::Index,
		f: impl FnOnce(PollStatus<&mut T::Tally, T::BlockNumber, TrackIdOf<T>>) -> R,
	) -> R {
		match ReferendumInfoFor::<T>::get(index) {
			Some(ReferendumInfo::Ongoing(mut status)) => {
				let result = f(PollStatus::Ongoing(&mut status.tally, status.track));
				let now = frame_system::Pallet::<T>::block_number();
				Self::ensure_alarm_at(&mut status, index, now + One::one());
				ReferendumInfoFor::<T>::insert(index, ReferendumInfo::Ongoing(status));
				result
			},
			Some(ReferendumInfo::Approved(end, ..)) => f(PollStatus::Completed(end, true)),
			Some(ReferendumInfo::Rejected(end, ..)) => f(PollStatus::Completed(end, false)),
			_ => f(PollStatus::None),
		}
	}

	fn try_access_poll<R>(
		index: Self::Index,
		f: impl FnOnce(
			PollStatus<&mut T::Tally, T::BlockNumber, TrackIdOf<T>>,
		) -> Result<R, DispatchError>,
	) -> Result<R, DispatchError> {
		match ReferendumInfoFor::<T>::get(index) {
			Some(ReferendumInfo::Ongoing(mut status)) => {
				let result = f(PollStatus::Ongoing(&mut status.tally, status.track))?;
				let now = frame_system::Pallet::<T>::block_number();
				Self::ensure_alarm_at(&mut status, index, now + One::one());
				ReferendumInfoFor::<T>::insert(index, ReferendumInfo::Ongoing(status));
				Ok(result)
			},
			Some(ReferendumInfo::Approved(end, ..)) => f(PollStatus::Completed(end, true)),
			Some(ReferendumInfo::Rejected(end, ..)) => f(PollStatus::Completed(end, false)),
			_ => f(PollStatus::None),
		}
	}

	fn as_ongoing(index: Self::Index) -> Option<(T::Tally, TrackIdOf<T>)> {
		Self::ensure_ongoing(index).ok().map(|x| (x.tally, x.track))
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn create_ongoing(class: Self::Class) -> Result<Self::Index, ()> {
		let index = ReferendumCount::<T>::mutate(|x| {
			let r = *x;
			*x += 1;
			r
		});
		let now = frame_system::Pallet::<T>::block_number();
		let dummy_account_id =
			codec::Decode::decode(&mut sp_runtime::traits::TrailingZeroInput::new(&b"dummy"[..]))
				.expect("infinite length input; no invalid inputs for type; qed");
		let mut status = ReferendumStatusOf::<T> {
			track: class,
			origin: frame_support::dispatch::RawOrigin::Root.into(),
			proposal_hash: <T::Hashing as sp_runtime::traits::Hash>::hash_of(&index),
			enactment: AtOrAfter::After(Zero::zero()),
			submitted: now,
			submission_deposit: Deposit { who: dummy_account_id, amount: Zero::zero() },
			decision_deposit: None,
			deciding: None,
			tally: Default::default(),
			in_queue: false,
			alarm: None,
		};
		Self::ensure_alarm_at(&mut status, index, sp_runtime::traits::Bounded::max_value());
		ReferendumInfoFor::<T>::insert(index, ReferendumInfo::Ongoing(status));
		Ok(index)
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn end_ongoing(index: Self::Index, approved: bool) -> Result<(), ()> {
		let mut status = Self::ensure_ongoing(index).map_err(|_| ())?;
		Self::ensure_no_alarm(&mut status);
		Self::note_one_fewer_deciding(status.track);
		let now = frame_system::Pallet::<T>::block_number();
		let info = if approved {
			ReferendumInfo::Approved(now, status.submission_deposit, status.decision_deposit)
		} else {
			ReferendumInfo::Rejected(now, status.submission_deposit, status.decision_deposit)
		};
		ReferendumInfoFor::<T>::insert(index, info);
		Ok(())
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn max_ongoing() -> (Self::Class, u32) {
		let r = T::Tracks::tracks()
			.iter()
			.max_by_key(|(_, info)| info.max_deciding)
			.expect("Always one class");
		(r.0.clone(), r.1.max_deciding)
	}
}

impl<T: Config> Pallet<T> {
	/// Check that referendum `index` is in the `Ongoing` state and return the `ReferendumStatus`
	/// value, or `Err` otherwise.
	pub fn ensure_ongoing(index: ReferendumIndex) -> Result<ReferendumStatusOf<T>, DispatchError> {
		match ReferendumInfoFor::<T>::get(index) {
			Some(ReferendumInfo::Ongoing(status)) => Ok(status),
			_ => Err(Error::<T>::NotOngoing.into()),
		}
	}

	// Enqueue a proposal from a referendum which has presumably passed.
	fn schedule_enactment(
		index: ReferendumIndex,
		track: &TrackInfoOf<T>,
		desired: AtOrAfter<T::BlockNumber>,
		origin: PalletsOriginOf<T>,
		call_hash: T::Hash,
	) {
		let now = frame_system::Pallet::<T>::block_number();
		let earliest_allowed = now.saturating_add(track.min_enactment_period);
		let desired = desired.evaluate(now);
		let ok = T::Scheduler::schedule_named(
			(ASSEMBLY_ID, "enactment", index).encode(),
			DispatchTime::At(desired.max(earliest_allowed)),
			None,
			63,
			origin,
			MaybeHashed::Hash(call_hash),
		)
		.is_ok();
		debug_assert!(ok, "LOGIC ERROR: bake_referendum/schedule_named failed");
	}

	/// Set an alarm to dispatch `call` at block number `when`.
	fn set_alarm(
		call: impl Into<CallOf<T>>,
		when: T::BlockNumber,
	) -> Option<(T::BlockNumber, ScheduleAddressOf<T>)> {
		let alarm_interval = T::AlarmInterval::get().max(One::one());
		let when = (when + alarm_interval - One::one()) / alarm_interval * alarm_interval;
		let maybe_result = T::Scheduler::schedule(
			DispatchTime::At(when),
			None,
			128u8,
			frame_system::RawOrigin::Root.into(),
			MaybeHashed::Value(call.into()),
		)
		.ok()
		.map(|x| (when, x));
		debug_assert!(
			maybe_result.is_some(),
			"Unable to schedule a new alarm at #{:?} (now: #{:?})?!",
			when,
			frame_system::Pallet::<T>::block_number()
		);
		maybe_result
	}

	/// Mutate a referendum's `status` into the correct deciding state.
	///
	/// - `now` is the current block number.
	/// - `track` is the track info for the referendum.
	///
	/// This will properly set up the `confirming` item.
	fn begin_deciding(
		status: &mut ReferendumStatusOf<T>,
		index: ReferendumIndex,
		now: T::BlockNumber,
		track: &TrackInfoOf<T>,
	) -> (Option<T::BlockNumber>, BeginDecidingBranch) {
		let is_passing = Self::is_passing(
			&status.tally,
			Zero::zero(),
			track.decision_period,
			&track.min_turnout,
			&track.min_approval,
		);
		status.in_queue = false;
		Self::deposit_event(Event::<T>::DecisionStarted {
			index,
			tally: status.tally.clone(),
			proposal_hash: status.proposal_hash.clone(),
			track: status.track.clone(),
		});
		let confirming = if is_passing {
			Self::deposit_event(Event::<T>::ConfirmStarted { index });
			Some(now.saturating_add(track.confirm_period))
		} else {
			None
		};
		let deciding_status = DecidingStatus { since: now, confirming };
		let alarm = Self::decision_time(&deciding_status, &status.tally, track);
		status.deciding = Some(deciding_status);
		let branch =
			if is_passing { BeginDecidingBranch::Passing } else { BeginDecidingBranch::Failing };
		(Some(alarm), branch)
	}

	/// If it returns `Some`, deciding has begun and it needs waking at the given block number. The
	/// second item is the flag for whether it is confirming or not.
	///
	/// If `None`, then it is queued and should be nudged automatically as the queue gets drained.
	fn ready_for_deciding(
		now: T::BlockNumber,
		track: &TrackInfoOf<T>,
		index: ReferendumIndex,
		status: &mut ReferendumStatusOf<T>,
	) -> (Option<T::BlockNumber>, ServiceBranch) {
		let deciding_count = DecidingCount::<T>::get(status.track);
		if deciding_count < track.max_deciding {
			// Begin deciding.
			DecidingCount::<T>::insert(status.track, deciding_count.saturating_add(1));
			let r = Self::begin_deciding(status, index, now, track);
			(r.0, r.1.into())
		} else {
			// Add to queue.
			let item = (index, status.tally.ayes());
			status.in_queue = true;
			TrackQueue::<T>::mutate(status.track, |q| q.insert_sorted_by_key(item, |x| x.1));
			(None, ServiceBranch::Queued)
		}
	}

	/// Grab the index and status for the referendum which is the highest priority of those for the
	/// given track which are ready for being decided.
	fn next_for_deciding(
		track_queue: &mut BoundedVec<(u32, VotesOf<T>), T::MaxQueued>,
	) -> Option<(ReferendumIndex, ReferendumStatusOf<T>)> {
		loop {
			let (index, _) = track_queue.pop()?;
			match Self::ensure_ongoing(index) {
				Ok(s) => return Some((index, s)),
				Err(_) => {}, // referendum already timedout or was cancelled.
			}
		}
	}

	/// Schedule a call to `one_fewer_deciding` function via the dispatchable
	/// `defer_one_fewer_deciding`. We could theoretically call it immediately (and it would be
	/// overall more efficient), however the weights become rather less easy to measure.
	fn note_one_fewer_deciding(track: TrackIdOf<T>) {
		// Set an alarm call for the next block to nudge the track along.
		let now = frame_system::Pallet::<T>::block_number();
		let next_block = now + One::one();
		let alarm_interval = T::AlarmInterval::get().max(One::one());
		let when = (next_block + alarm_interval - One::one()) / alarm_interval * alarm_interval;

		let maybe_result = T::Scheduler::schedule(
			DispatchTime::At(when),
			None,
			128u8,
			frame_system::RawOrigin::Root.into(),
			MaybeHashed::Value(Call::one_fewer_deciding { track }.into()),
		);
		debug_assert!(
			maybe_result.is_ok(),
			"Unable to schedule a new alarm at #{:?} (now: #{:?})?!",
			when,
			now
		);
	}

	/// Ensure that a `service_referendum` alarm happens for the referendum `index` at `alarm`.
	///
	/// This will do nothing if the alarm is already set.
	///
	/// Returns `false` if nothing changed.
	fn ensure_alarm_at(
		status: &mut ReferendumStatusOf<T>,
		index: ReferendumIndex,
		alarm: T::BlockNumber,
	) -> bool {
		if status.alarm.as_ref().map_or(true, |&(when, _)| when != alarm) {
			// Either no alarm or one that was different
			Self::ensure_no_alarm(status);
			status.alarm = Self::set_alarm(Call::nudge_referendum { index }, alarm);
			true
		} else {
			false
		}
	}

	/// Advance the state of a referendum, which comes down to:
	/// - If it's ready to be decided, start deciding;
	/// - If it's not ready to be decided and non-deciding timeout has passed, fail;
	/// - If it's ongoing and passing, ensure confirming; if at end of confirmation period, pass.
	/// - If it's ongoing and not passing, stop confirning; if it has reached end time, fail.
	///
	/// Weight will be a bit different depending on what it does, but it's designed so as not to
	/// differ dramatically, especially if `MaxQueue` is kept small. In particular _there are no
	/// balance operations in here_.
	///
	/// In terms of storage, every call to it is expected to access:
	/// - The scheduler, either to insert, remove or alter an entry;
	/// - `TrackQueue`, which should be a `BoundedVec` with a low limit (8-16).
	/// - `DecidingCount`.
	///
	/// Both of the two storage items will only have as many items as there are different tracks,
	/// perhaps around 10 and should be whitelisted.
	///
	/// The heaviest branch is likely to be when a proposal is placed into, or moved within, the
	/// `TrackQueue`. Basically this happens when a referendum is in the deciding queue and receives
	/// a vote, or when it moves into the deciding queue.
	fn service_referendum(
		now: T::BlockNumber,
		index: ReferendumIndex,
		mut status: ReferendumStatusOf<T>,
	) -> (ReferendumInfoOf<T>, bool, ServiceBranch) {
		let mut dirty = false;
		// Should it begin being decided?
		let track = match Self::track(status.track) {
			Some(x) => x,
			None => return (ReferendumInfo::Ongoing(status), false, ServiceBranch::Fail),
		};
		let timeout = status.submitted + T::UndecidingTimeout::get();
		// Default the alarm to the submission timeout.
		let mut alarm = timeout;
		let branch;
		match &mut status.deciding {
			None => {
				// Are we already queued for deciding?
				if status.in_queue {
					// Does our position in the queue need updating?
					let ayes = status.tally.ayes();
					let mut queue = TrackQueue::<T>::get(status.track);
					let maybe_old_pos = queue.iter().position(|(x, _)| *x == index);
					let new_pos = queue.binary_search_by_key(&ayes, |x| x.1).unwrap_or_else(|x| x);
					branch = if maybe_old_pos.is_none() && new_pos > 0 {
						// Just insert.
						queue.force_insert_keep_right(new_pos, (index, ayes));
						ServiceBranch::RequeuedInsertion
					} else if let Some(old_pos) = maybe_old_pos {
						// We were in the queue - slide into the correct position.
						queue[old_pos].1 = ayes;
						queue.slide(old_pos, new_pos);
						ServiceBranch::RequeuedSlide
					} else {
						ServiceBranch::NotQueued
					};
					TrackQueue::<T>::insert(status.track, queue);
				} else {
					// Are we ready for deciding?
					branch = if status.decision_deposit.is_some() {
						let prepare_end = status.submitted.saturating_add(track.prepare_period);
						if now >= prepare_end {
							let (maybe_alarm, branch) =
								Self::ready_for_deciding(now, &track, index, &mut status);
							if let Some(set_alarm) = maybe_alarm {
								alarm = alarm.min(set_alarm);
							}
							dirty = true;
							branch
						} else {
							alarm = alarm.min(prepare_end);
							ServiceBranch::Preparing
						}
					} else {
						ServiceBranch::NoDeposit
					}
				}
				// If we didn't move into being decided, then check the timeout.
				if status.deciding.is_none() && now >= timeout {
					// Too long without being decided - end it.
					Self::ensure_no_alarm(&mut status);
					Self::deposit_event(Event::<T>::TimedOut { index, tally: status.tally });
					return (
						ReferendumInfo::TimedOut(
							now,
							status.submission_deposit,
							status.decision_deposit,
						),
						true,
						ServiceBranch::TimedOut,
					)
				}
			},
			Some(deciding) => {
				let is_passing = Self::is_passing(
					&status.tally,
					now.saturating_sub(deciding.since),
					track.decision_period,
					&track.min_turnout,
					&track.min_approval,
				);
				branch = if is_passing {
					match deciding.confirming.clone() {
						Some(t) if now >= t => {
							// Passed!
							Self::ensure_no_alarm(&mut status);
							Self::note_one_fewer_deciding(status.track);
							let (desired, call_hash) = (status.enactment, status.proposal_hash);
							Self::schedule_enactment(
								index,
								track,
								desired,
								status.origin,
								call_hash,
							);
							Self::deposit_event(Event::<T>::Confirmed {
								index,
								tally: status.tally,
							});
							return (
								ReferendumInfo::Approved(
									now,
									status.submission_deposit,
									status.decision_deposit,
								),
								true,
								ServiceBranch::Approved,
							)
						},
						Some(_) => ServiceBranch::ContinueConfirming,
						None => {
							// Start confirming
							dirty = true;
							deciding.confirming = Some(now.saturating_add(track.confirm_period));
							Self::deposit_event(Event::<T>::ConfirmStarted { index });
							ServiceBranch::BeginConfirming
						},
					}
				} else {
					if now >= deciding.since.saturating_add(track.decision_period) {
						// Failed!
						Self::ensure_no_alarm(&mut status);
						Self::note_one_fewer_deciding(status.track);
						Self::deposit_event(Event::<T>::Rejected { index, tally: status.tally });
						return (
							ReferendumInfo::Rejected(
								now,
								status.submission_deposit,
								status.decision_deposit,
							),
							true,
							ServiceBranch::Rejected,
						)
					}
					if deciding.confirming.is_some() {
						// Stop confirming
						dirty = true;
						deciding.confirming = None;
						Self::deposit_event(Event::<T>::ConfirmAborted { index });
						ServiceBranch::EndConfirming
					} else {
						ServiceBranch::ContinueNotConfirming
					}
				};
				alarm = Self::decision_time(&deciding, &status.tally, track);
			},
		}

		let dirty_alarm = Self::ensure_alarm_at(&mut status, index, alarm);
		(ReferendumInfo::Ongoing(status), dirty_alarm || dirty, branch)
	}

	/// Determine the point at which a referendum will be accepted, move into confirmation with the
	/// given `tally` or end with rejection (whichever happens sooner).
	fn decision_time(
		deciding: &DecidingStatusOf<T>,
		tally: &T::Tally,
		track: &TrackInfoOf<T>,
	) -> T::BlockNumber {
		deciding.confirming.unwrap_or_else(|| {
			// Set alarm to the point where the current voting would make it pass.
			let approval = tally.approval();
			let turnout = tally.turnout();
			let until_approval = track.min_approval.delay(approval);
			let until_turnout = track.min_turnout.delay(turnout);
			let offset = until_turnout.max(until_approval);
			deciding.since.saturating_add(offset * track.decision_period)
		})
	}

	/// Cancel the alarm in `status`, if one exists.
	fn ensure_no_alarm(status: &mut ReferendumStatusOf<T>) {
		if let Some((_, last_alarm)) = status.alarm.take() {
			// Incorrect alarm - cancel it.
			let _ = T::Scheduler::cancel(last_alarm);
		}
	}

	/// Reserve a deposit and return the `Deposit` instance.
	fn take_deposit(
		who: T::AccountId,
		amount: BalanceOf<T>,
	) -> Result<Deposit<T::AccountId, BalanceOf<T>>, DispatchError> {
		T::Currency::reserve(&who, amount)?;
		Ok(Deposit { who, amount })
	}

	/// Return a deposit, if `Some`.
	fn refund_deposit(deposit: Option<Deposit<T::AccountId, BalanceOf<T>>>) {
		if let Some(Deposit { who, amount }) = deposit {
			T::Currency::unreserve(&who, amount);
		}
	}

	/// Slash a deposit, if `Some`.
	fn slash_deposit(deposit: Option<Deposit<T::AccountId, BalanceOf<T>>>) {
		if let Some(Deposit { who, amount }) = deposit {
			T::Slash::on_unbalanced(T::Currency::slash_reserved(&who, amount).0);
			Self::deposit_event(Event::<T>::DepositSlashed { who, amount });
		}
	}

	/// Get the track info value for the track `id`.
	fn track(id: TrackIdOf<T>) -> Option<&'static TrackInfoOf<T>> {
		let tracks = T::Tracks::tracks();
		let index = tracks.binary_search_by_key(&id, |x| x.0).unwrap_or_else(|x| x);
		Some(&tracks[index].1)
	}

	/// Determine whether the given `tally` would result in a referendum passing at `elapsed` blocks
	/// into a total decision `period`, given the two curves for `turnout_needed` and
	/// `approval_needed`.
	fn is_passing(
		tally: &T::Tally,
		elapsed: T::BlockNumber,
		period: T::BlockNumber,
		turnout_needed: &Curve,
		approval_needed: &Curve,
	) -> bool {
		let x = Perbill::from_rational(elapsed.min(period), period);
		turnout_needed.passing(x, tally.turnout()) && approval_needed.passing(x, tally.approval())
	}
}
