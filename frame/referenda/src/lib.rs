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
//! _Passing_ when there is a sufficiently high support and approval, given the amount of time it
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
//! ## Terms
//! - *Support*: The number of aye-votes, pre-conviction, as a proportion of the total number of
//!   pre-conviction votes able to be cast in the population.
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
			v3::{Anon as ScheduleAnon, Named as ScheduleNamed},
			DispatchTime,
		},
		Currency, LockIdentifier, OnUnbalanced, OriginTrait, PollStatus, Polling, QueryPreimage,
		ReservableCurrency, StorePreimage, VoteTally,
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

use self::branch::{BeginDecidingBranch, OneFewerDecidingBranch, ServiceBranch};
pub use self::{
	pallet::*,
	types::{
		BalanceOf, BoundedCallOf, CallOf, Curve, DecidingStatus, DecidingStatusOf, Deposit,
		InsertSorted, NegativeImbalanceOf, PalletsOriginOf, ReferendumIndex, ReferendumInfo,
		ReferendumInfoOf, ReferendumStatus, ReferendumStatusOf, ScheduleAddressOf, TallyOf,
		TrackIdOf, TrackInfo, TrackInfoOf, TracksInfo, VotesOf,
	},
	weights::WeightInfo,
};

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
pub mod benchmarking;

pub use frame_support::traits::Get;
pub use sp_std::vec::Vec;

#[macro_export]
macro_rules! impl_tracksinfo_get {
	($tracksinfo:ty, $balance:ty, $blocknumber:ty) => {
		impl
			$crate::Get<
				$crate::Vec<(
					<$tracksinfo as $crate::TracksInfo<$balance, $blocknumber>>::Id,
					$crate::TrackInfo<$balance, $blocknumber>,
				)>,
			> for $tracksinfo
		{
			fn get() -> $crate::Vec<(
				<$tracksinfo as $crate::TracksInfo<$balance, $blocknumber>>::Id,
				$crate::TrackInfo<$balance, $blocknumber>,
			)> {
				<$tracksinfo as $crate::TracksInfo<$balance, $blocknumber>>::tracks().to_vec()
			}
		}
	};
}

const ASSEMBLY_ID: LockIdentifier = *b"assembly";

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T, I = ()>(_);

	#[pallet::config]
	pub trait Config<I: 'static = ()>: frame_system::Config + Sized {
		// System level stuff.
		type RuntimeCall: Parameter
			+ Dispatchable<RuntimeOrigin = Self::RuntimeOrigin>
			+ From<Call<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeCall>
			+ From<frame_system::Call<Self>>;
		type RuntimeEvent: From<Event<Self, I>>
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>;
		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;
		/// The Scheduler.
		type Scheduler: ScheduleAnon<Self::BlockNumber, CallOf<Self, I>, PalletsOriginOf<Self>>
			+ ScheduleNamed<Self::BlockNumber, CallOf<Self, I>, PalletsOriginOf<Self>>;
		/// Currency type for this pallet.
		type Currency: ReservableCurrency<Self::AccountId>;
		// Origins and unbalances.
		/// Origin from which proposals may be submitted.
		type SubmitOrigin: EnsureOrigin<Self::RuntimeOrigin, Success = Self::AccountId>;
		/// Origin from which any vote may be cancelled.
		type CancelOrigin: EnsureOrigin<Self::RuntimeOrigin>;
		/// Origin from which any vote may be killed.
		type KillOrigin: EnsureOrigin<Self::RuntimeOrigin>;
		/// Handler for the unbalanced reduction when slashing a preimage deposit.
		type Slash: OnUnbalanced<NegativeImbalanceOf<Self, I>>;
		/// The counting type for votes. Usually just balance.
		type Votes: AtLeast32BitUnsigned + Copy + Parameter + Member + MaxEncodedLen;
		/// The tallying type.
		type Tally: VoteTally<Self::Votes, TrackIdOf<Self, I>>
			+ Clone
			+ Codec
			+ Eq
			+ Debug
			+ TypeInfo
			+ MaxEncodedLen;

		// Constants
		/// The minimum amount to be used as a deposit for a public referendum proposal.
		#[pallet::constant]
		type SubmissionDeposit: Get<BalanceOf<Self, I>>;

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
		#[pallet::constant]
		type Tracks: Get<
				Vec<(
					<Self::Tracks as TracksInfo<BalanceOf<Self, I>, Self::BlockNumber>>::Id,
					TrackInfo<BalanceOf<Self, I>, Self::BlockNumber>,
				)>,
			> + TracksInfo<
				BalanceOf<Self, I>,
				Self::BlockNumber,
				RuntimeOrigin = <Self::RuntimeOrigin as OriginTrait>::PalletsOrigin,
			>;

		/// The preimage provider.
		type Preimages: QueryPreimage + StorePreimage;
	}

	/// The next free referendum index, aka the number of referenda started so far.
	#[pallet::storage]
	pub type ReferendumCount<T, I = ()> = StorageValue<_, ReferendumIndex, ValueQuery>;

	/// Information concerning any given referendum.
	#[pallet::storage]
	pub type ReferendumInfoFor<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Blake2_128Concat, ReferendumIndex, ReferendumInfoOf<T, I>>;

	/// The sorted list of referenda ready to be decided but not yet being decided, ordered by
	/// conviction-weighted approvals.
	///
	/// This should be empty if `DecidingCount` is less than `TrackInfo::max_deciding`.
	#[pallet::storage]
	pub type TrackQueue<T: Config<I>, I: 'static = ()> = StorageMap<
		_,
		Twox64Concat,
		TrackIdOf<T, I>,
		BoundedVec<(ReferendumIndex, T::Votes), T::MaxQueued>,
		ValueQuery,
	>;

	/// The number of referenda being decided currently.
	#[pallet::storage]
	pub type DecidingCount<T: Config<I>, I: 'static = ()> =
		StorageMap<_, Twox64Concat, TrackIdOf<T, I>, u32, ValueQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config<I>, I: 'static = ()> {
		/// A referendum has been submitted.
		Submitted {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The track (and by extension proposal dispatch origin) of this referendum.
			track: TrackIdOf<T, I>,
			/// The proposal for the referendum.
			proposal: BoundedCallOf<T, I>,
		},
		/// The decision deposit has been placed.
		DecisionDepositPlaced {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The account who placed the deposit.
			who: T::AccountId,
			/// The amount placed by the account.
			amount: BalanceOf<T, I>,
		},
		/// The decision deposit has been refunded.
		DecisionDepositRefunded {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The account who placed the deposit.
			who: T::AccountId,
			/// The amount placed by the account.
			amount: BalanceOf<T, I>,
		},
		/// A deposit has been slashaed.
		DepositSlashed {
			/// The account who placed the deposit.
			who: T::AccountId,
			/// The amount placed by the account.
			amount: BalanceOf<T, I>,
		},
		/// A referendum has moved into the deciding phase.
		DecisionStarted {
			/// Index of the referendum.
			index: ReferendumIndex,
			/// The track (and by extension proposal dispatch origin) of this referendum.
			track: TrackIdOf<T, I>,
			/// The proposal for the referendum.
			proposal: BoundedCallOf<T, I>,
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
	pub enum Error<T, I = ()> {
		/// Referendum is not ongoing.
		NotOngoing,
		/// Referendum's decision deposit is already paid.
		HasDeposit,
		/// The track identifier given was invalid.
		BadTrack,
		/// There are already a full complement of referenda in progress for this track.
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
	impl<T: Config<I>, I: 'static> Pallet<T, I> {
		/// Propose a referendum on a privileged action.
		///
		/// - `origin`: must be `SubmitOrigin` and the account must have `SubmissionDeposit` funds
		///   available.
		/// - `proposal_origin`: The origin from which the proposal should be executed.
		/// - `proposal`: The proposal.
		/// - `enactment_moment`: The moment that the proposal should be enacted.
		///
		/// Emits `Submitted`.
		#[pallet::weight(T::WeightInfo::submit())]
		pub fn submit(
			origin: OriginFor<T>,
			proposal_origin: Box<PalletsOriginOf<T>>,
			proposal: BoundedCallOf<T, I>,
			enactment_moment: DispatchTime<T::BlockNumber>,
		) -> DispatchResult {
			let who = T::SubmitOrigin::ensure_origin(origin)?;

			let track =
				T::Tracks::track_for(&proposal_origin).map_err(|_| Error::<T, I>::NoTrack)?;
			let submission_deposit = Self::take_deposit(who, T::SubmissionDeposit::get())?;
			let index = ReferendumCount::<T, I>::mutate(|x| {
				let r = *x;
				*x += 1;
				r
			});
			let now = frame_system::Pallet::<T>::block_number();
			let nudge_call =
				T::Preimages::bound(CallOf::<T, I>::from(Call::nudge_referendum { index }))?;
			let status = ReferendumStatus {
				track,
				origin: *proposal_origin,
				proposal: proposal.clone(),
				enactment: enactment_moment,
				submitted: now,
				submission_deposit,
				decision_deposit: None,
				deciding: None,
				tally: TallyOf::<T, I>::new(track),
				in_queue: false,
				alarm: Self::set_alarm(nudge_call, now.saturating_add(T::UndecidingTimeout::get())),
			};
			ReferendumInfoFor::<T, I>::insert(index, ReferendumInfo::Ongoing(status));

			Self::deposit_event(Event::<T, I>::Submitted { index, track, proposal });
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
		#[pallet::weight(ServiceBranch::max_weight_of_deposit::<T, I>())]
		pub fn place_decision_deposit(
			origin: OriginFor<T>,
			index: ReferendumIndex,
		) -> DispatchResultWithPostInfo {
			let who = ensure_signed(origin)?;
			let mut status = Self::ensure_ongoing(index)?;
			ensure!(status.decision_deposit.is_none(), Error::<T, I>::HasDeposit);
			let track = Self::track(status.track).ok_or(Error::<T, I>::NoTrack)?;
			status.decision_deposit =
				Some(Self::take_deposit(who.clone(), track.decision_deposit)?);
			let now = frame_system::Pallet::<T>::block_number();
			let (info, _, branch) = Self::service_referendum(now, index, status);
			ReferendumInfoFor::<T, I>::insert(index, info);
			let e =
				Event::<T, I>::DecisionDepositPlaced { index, who, amount: track.decision_deposit };
			Self::deposit_event(e);
			Ok(branch.weight_of_deposit::<T, I>().into())
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
			let mut info =
				ReferendumInfoFor::<T, I>::get(index).ok_or(Error::<T, I>::BadReferendum)?;
			let deposit = info
				.take_decision_deposit()
				.map_err(|_| Error::<T, I>::Unfinished)?
				.ok_or(Error::<T, I>::NoDeposit)?;
			Self::refund_deposit(Some(deposit.clone()));
			ReferendumInfoFor::<T, I>::insert(index, info);
			let e = Event::<T, I>::DecisionDepositRefunded {
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
			Self::deposit_event(Event::<T, I>::Cancelled { index, tally: status.tally });
			let info = ReferendumInfo::Cancelled(
				frame_system::Pallet::<T>::block_number(),
				status.submission_deposit,
				status.decision_deposit,
			);
			ReferendumInfoFor::<T, I>::insert(index, info);
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
			Self::deposit_event(Event::<T, I>::Killed { index, tally: status.tally });
			Self::slash_deposit(Some(status.submission_deposit.clone()));
			Self::slash_deposit(status.decision_deposit.clone());
			let info = ReferendumInfo::Killed(frame_system::Pallet::<T>::block_number());
			ReferendumInfoFor::<T, I>::insert(index, info);
			Ok(())
		}

		/// Advance a referendum onto its next logical state. Only used internally.
		///
		/// - `origin`: must be `Root`.
		/// - `index`: the referendum to be advanced.
		#[pallet::weight(ServiceBranch::max_weight_of_nudge::<T, I>())]
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
				ReferendumInfoFor::<T, I>::insert(index, info);
			}
			Ok(Some(branch.weight_of_nudge::<T, I>()).into())
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
		#[pallet::weight(OneFewerDecidingBranch::max_weight::<T, I>())]
		pub fn one_fewer_deciding(
			origin: OriginFor<T>,
			track: TrackIdOf<T, I>,
		) -> DispatchResultWithPostInfo {
			ensure_root(origin)?;
			let track_info = T::Tracks::info(track).ok_or(Error::<T, I>::BadTrack)?;
			let mut track_queue = TrackQueue::<T, I>::get(track);
			let branch =
				if let Some((index, mut status)) = Self::next_for_deciding(&mut track_queue) {
					let now = frame_system::Pallet::<T>::block_number();
					let (maybe_alarm, branch) =
						Self::begin_deciding(&mut status, index, now, track_info);
					if let Some(set_alarm) = maybe_alarm {
						Self::ensure_alarm_at(&mut status, index, set_alarm);
					}
					ReferendumInfoFor::<T, I>::insert(index, ReferendumInfo::Ongoing(status));
					TrackQueue::<T, I>::insert(track, track_queue);
					branch.into()
				} else {
					DecidingCount::<T, I>::mutate(track, |x| x.saturating_dec());
					OneFewerDecidingBranch::QueueEmpty
				};
			Ok(Some(branch.weight::<T, I>()).into())
		}
	}
}

impl<T: Config<I>, I: 'static> Polling<T::Tally> for Pallet<T, I> {
	type Index = ReferendumIndex;
	type Votes = VotesOf<T, I>;
	type Moment = T::BlockNumber;
	type Class = TrackIdOf<T, I>;

	fn classes() -> Vec<Self::Class> {
		T::Tracks::tracks().iter().map(|x| x.0).collect()
	}

	fn access_poll<R>(
		index: Self::Index,
		f: impl FnOnce(PollStatus<&mut T::Tally, T::BlockNumber, TrackIdOf<T, I>>) -> R,
	) -> R {
		match ReferendumInfoFor::<T, I>::get(index) {
			Some(ReferendumInfo::Ongoing(mut status)) => {
				let result = f(PollStatus::Ongoing(&mut status.tally, status.track));
				let now = frame_system::Pallet::<T>::block_number();
				Self::ensure_alarm_at(&mut status, index, now + One::one());
				ReferendumInfoFor::<T, I>::insert(index, ReferendumInfo::Ongoing(status));
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
			PollStatus<&mut T::Tally, T::BlockNumber, TrackIdOf<T, I>>,
		) -> Result<R, DispatchError>,
	) -> Result<R, DispatchError> {
		match ReferendumInfoFor::<T, I>::get(index) {
			Some(ReferendumInfo::Ongoing(mut status)) => {
				let result = f(PollStatus::Ongoing(&mut status.tally, status.track))?;
				let now = frame_system::Pallet::<T>::block_number();
				Self::ensure_alarm_at(&mut status, index, now + One::one());
				ReferendumInfoFor::<T, I>::insert(index, ReferendumInfo::Ongoing(status));
				Ok(result)
			},
			Some(ReferendumInfo::Approved(end, ..)) => f(PollStatus::Completed(end, true)),
			Some(ReferendumInfo::Rejected(end, ..)) => f(PollStatus::Completed(end, false)),
			_ => f(PollStatus::None),
		}
	}

	fn as_ongoing(index: Self::Index) -> Option<(T::Tally, TrackIdOf<T, I>)> {
		Self::ensure_ongoing(index).ok().map(|x| (x.tally, x.track))
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn create_ongoing(class: Self::Class) -> Result<Self::Index, ()> {
		let index = ReferendumCount::<T, I>::mutate(|x| {
			let r = *x;
			*x += 1;
			r
		});
		let now = frame_system::Pallet::<T>::block_number();
		let dummy_account_id =
			codec::Decode::decode(&mut sp_runtime::traits::TrailingZeroInput::new(&b"dummy"[..]))
				.expect("infinite length input; no invalid inputs for type; qed");
		let mut status = ReferendumStatusOf::<T, I> {
			track: class,
			origin: frame_support::dispatch::RawOrigin::Root.into(),
			proposal: T::Preimages::bound(CallOf::<T, I>::from(Call::nudge_referendum { index }))
				.map_err(|_| ())?,
			enactment: DispatchTime::After(Zero::zero()),
			submitted: now,
			submission_deposit: Deposit { who: dummy_account_id, amount: Zero::zero() },
			decision_deposit: None,
			deciding: None,
			tally: TallyOf::<T, I>::new(class),
			in_queue: false,
			alarm: None,
		};
		Self::ensure_alarm_at(&mut status, index, sp_runtime::traits::Bounded::max_value());
		ReferendumInfoFor::<T, I>::insert(index, ReferendumInfo::Ongoing(status));
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
		ReferendumInfoFor::<T, I>::insert(index, info);
		Ok(())
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn max_ongoing() -> (Self::Class, u32) {
		let r = T::Tracks::tracks()
			.iter()
			.max_by_key(|(_, info)| info.max_deciding)
			.expect("Always one class");
		(r.0, r.1.max_deciding)
	}
}

impl<T: Config<I>, I: 'static> Pallet<T, I> {
	/// Check that referendum `index` is in the `Ongoing` state and return the `ReferendumStatus`
	/// value, or `Err` otherwise.
	pub fn ensure_ongoing(
		index: ReferendumIndex,
	) -> Result<ReferendumStatusOf<T, I>, DispatchError> {
		match ReferendumInfoFor::<T, I>::get(index) {
			Some(ReferendumInfo::Ongoing(status)) => Ok(status),
			_ => Err(Error::<T, I>::NotOngoing.into()),
		}
	}

	/// Returns whether the referendum is passing.
	/// Referendum must be ongoing and its track must exist.
	pub fn is_referendum_passing(ref_index: ReferendumIndex) -> Result<bool, DispatchError> {
		let info = ReferendumInfoFor::<T, I>::get(ref_index).ok_or(Error::<T, I>::BadReferendum)?;
		match info {
			ReferendumInfo::Ongoing(status) => {
				let track = Self::track(status.track).ok_or(Error::<T, I>::NoTrack)?;
				let elapsed = if let Some(deciding) = status.deciding {
					frame_system::Pallet::<T>::block_number().saturating_sub(deciding.since)
				} else {
					Zero::zero()
				};
				Ok(Self::is_passing(
					&status.tally,
					elapsed,
					track.decision_period,
					&track.min_support,
					&track.min_approval,
					status.track,
				))
			},
			_ => Err(Error::<T, I>::NotOngoing.into()),
		}
	}

	// Enqueue a proposal from a referendum which has presumably passed.
	fn schedule_enactment(
		index: ReferendumIndex,
		track: &TrackInfoOf<T, I>,
		desired: DispatchTime<T::BlockNumber>,
		origin: PalletsOriginOf<T>,
		call: BoundedCallOf<T, I>,
	) {
		let now = frame_system::Pallet::<T>::block_number();
		let earliest_allowed = now.saturating_add(track.min_enactment_period);
		let desired = desired.evaluate(now);
		let ok = T::Scheduler::schedule_named(
			(ASSEMBLY_ID, "enactment", index).using_encoded(sp_io::hashing::blake2_256),
			DispatchTime::At(desired.max(earliest_allowed)),
			None,
			63,
			origin,
			call,
		)
		.is_ok();
		debug_assert!(ok, "LOGIC ERROR: bake_referendum/schedule_named failed");
	}

	/// Set an alarm to dispatch `call` at block number `when`.
	fn set_alarm(
		call: BoundedCallOf<T, I>,
		when: T::BlockNumber,
	) -> Option<(T::BlockNumber, ScheduleAddressOf<T, I>)> {
		let alarm_interval = T::AlarmInterval::get().max(One::one());
		let when = when.saturating_add(alarm_interval).saturating_sub(One::one()) /
			(alarm_interval.saturating_mul(alarm_interval)).max(One::one());
		let maybe_result = T::Scheduler::schedule(
			DispatchTime::At(when),
			None,
			128u8,
			frame_system::RawOrigin::Root.into(),
			call,
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
		status: &mut ReferendumStatusOf<T, I>,
		index: ReferendumIndex,
		now: T::BlockNumber,
		track: &TrackInfoOf<T, I>,
	) -> (Option<T::BlockNumber>, BeginDecidingBranch) {
		let is_passing = Self::is_passing(
			&status.tally,
			Zero::zero(),
			track.decision_period,
			&track.min_support,
			&track.min_approval,
			status.track,
		);
		status.in_queue = false;
		Self::deposit_event(Event::<T, I>::DecisionStarted {
			index,
			tally: status.tally.clone(),
			proposal: status.proposal.clone(),
			track: status.track,
		});
		let confirming = if is_passing {
			Self::deposit_event(Event::<T, I>::ConfirmStarted { index });
			Some(now.saturating_add(track.confirm_period))
		} else {
			None
		};
		let deciding_status = DecidingStatus { since: now, confirming };
		let alarm = Self::decision_time(&deciding_status, &status.tally, status.track, track)
			.max(now.saturating_add(One::one()));
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
		track: &TrackInfoOf<T, I>,
		index: ReferendumIndex,
		status: &mut ReferendumStatusOf<T, I>,
	) -> (Option<T::BlockNumber>, ServiceBranch) {
		let deciding_count = DecidingCount::<T, I>::get(status.track);
		if deciding_count < track.max_deciding {
			// Begin deciding.
			DecidingCount::<T, I>::insert(status.track, deciding_count.saturating_add(1));
			let r = Self::begin_deciding(status, index, now, track);
			(r.0, r.1.into())
		} else {
			// Add to queue.
			let item = (index, status.tally.ayes(status.track));
			status.in_queue = true;
			TrackQueue::<T, I>::mutate(status.track, |q| q.insert_sorted_by_key(item, |x| x.1));
			(None, ServiceBranch::Queued)
		}
	}

	/// Grab the index and status for the referendum which is the highest priority of those for the
	/// given track which are ready for being decided.
	fn next_for_deciding(
		track_queue: &mut BoundedVec<(u32, VotesOf<T, I>), T::MaxQueued>,
	) -> Option<(ReferendumIndex, ReferendumStatusOf<T, I>)> {
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
	fn note_one_fewer_deciding(track: TrackIdOf<T, I>) {
		// Set an alarm call for the next block to nudge the track along.
		let now = frame_system::Pallet::<T>::block_number();
		let next_block = now + One::one();
		let alarm_interval = T::AlarmInterval::get().max(One::one());
		let when = (next_block + alarm_interval - One::one()) / alarm_interval * alarm_interval;

		let call = match T::Preimages::bound(CallOf::<T, I>::from(Call::one_fewer_deciding {
			track,
		})) {
			Ok(c) => c,
			Err(_) => {
				debug_assert!(false, "Unable to create a bounded call from `one_fewer_deciding`??",);
				return
			},
		};
		let maybe_result = T::Scheduler::schedule(
			DispatchTime::At(when),
			None,
			128u8,
			frame_system::RawOrigin::Root.into(),
			call,
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
		status: &mut ReferendumStatusOf<T, I>,
		index: ReferendumIndex,
		alarm: T::BlockNumber,
	) -> bool {
		if status.alarm.as_ref().map_or(true, |&(when, _)| when != alarm) {
			// Either no alarm or one that was different
			Self::ensure_no_alarm(status);
			let call =
				match T::Preimages::bound(CallOf::<T, I>::from(Call::nudge_referendum { index })) {
					Ok(c) => c,
					Err(_) => {
						debug_assert!(
							false,
							"Unable to create a bounded call from `nudge_referendum`??",
						);
						return false
					},
				};
			status.alarm = Self::set_alarm(call, alarm);
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
	/// - `TrackQueue`, which should be a `BoundedVec` with a low limit (8-16);
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
		mut status: ReferendumStatusOf<T, I>,
	) -> (ReferendumInfoOf<T, I>, bool, ServiceBranch) {
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
					let ayes = status.tally.ayes(status.track);
					let mut queue = TrackQueue::<T, I>::get(status.track);
					let maybe_old_pos = queue.iter().position(|(x, _)| *x == index);
					let new_pos = queue.binary_search_by_key(&ayes, |x| x.1).unwrap_or_else(|x| x);
					branch = if maybe_old_pos.is_none() && new_pos > 0 {
						// Just insert.
						let _ = queue.force_insert_keep_right(new_pos, (index, ayes));
						ServiceBranch::RequeuedInsertion
					} else if let Some(old_pos) = maybe_old_pos {
						// We were in the queue - slide into the correct position.
						queue[old_pos].1 = ayes;
						queue.slide(old_pos, new_pos);
						ServiceBranch::RequeuedSlide
					} else {
						ServiceBranch::NotQueued
					};
					TrackQueue::<T, I>::insert(status.track, queue);
				} else {
					// Are we ready for deciding?
					branch = if status.decision_deposit.is_some() {
						let prepare_end = status.submitted.saturating_add(track.prepare_period);
						if now >= prepare_end {
							let (maybe_alarm, branch) =
								Self::ready_for_deciding(now, track, index, &mut status);
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
					Self::deposit_event(Event::<T, I>::TimedOut { index, tally: status.tally });
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
					&track.min_support,
					&track.min_approval,
					status.track,
				);
				branch = if is_passing {
					match deciding.confirming {
						Some(t) if now >= t => {
							// Passed!
							Self::ensure_no_alarm(&mut status);
							Self::note_one_fewer_deciding(status.track);
							let (desired, call) = (status.enactment, status.proposal);
							Self::schedule_enactment(index, track, desired, status.origin, call);
							Self::deposit_event(Event::<T, I>::Confirmed {
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
							Self::deposit_event(Event::<T, I>::ConfirmStarted { index });
							ServiceBranch::BeginConfirming
						},
					}
				} else {
					if now >= deciding.since.saturating_add(track.decision_period) {
						// Failed!
						Self::ensure_no_alarm(&mut status);
						Self::note_one_fewer_deciding(status.track);
						Self::deposit_event(Event::<T, I>::Rejected { index, tally: status.tally });
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
						Self::deposit_event(Event::<T, I>::ConfirmAborted { index });
						ServiceBranch::EndConfirming
					} else {
						ServiceBranch::ContinueNotConfirming
					}
				};
				alarm = Self::decision_time(deciding, &status.tally, status.track, track);
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
		track_id: TrackIdOf<T, I>,
		track: &TrackInfoOf<T, I>,
	) -> T::BlockNumber {
		deciding.confirming.unwrap_or_else(|| {
			// Set alarm to the point where the current voting would make it pass.
			let approval = tally.approval(track_id);
			let support = tally.support(track_id);
			let until_approval = track.min_approval.delay(approval);
			let until_support = track.min_support.delay(support);
			let offset = until_support.max(until_approval);
			deciding.since.saturating_add(offset * track.decision_period)
		})
	}

	/// Cancel the alarm in `status`, if one exists.
	fn ensure_no_alarm(status: &mut ReferendumStatusOf<T, I>) {
		if let Some((_, last_alarm)) = status.alarm.take() {
			// Incorrect alarm - cancel it.
			let _ = T::Scheduler::cancel(last_alarm);
		}
	}

	/// Reserve a deposit and return the `Deposit` instance.
	fn take_deposit(
		who: T::AccountId,
		amount: BalanceOf<T, I>,
	) -> Result<Deposit<T::AccountId, BalanceOf<T, I>>, DispatchError> {
		T::Currency::reserve(&who, amount)?;
		Ok(Deposit { who, amount })
	}

	/// Return a deposit, if `Some`.
	fn refund_deposit(deposit: Option<Deposit<T::AccountId, BalanceOf<T, I>>>) {
		if let Some(Deposit { who, amount }) = deposit {
			T::Currency::unreserve(&who, amount);
		}
	}

	/// Slash a deposit, if `Some`.
	fn slash_deposit(deposit: Option<Deposit<T::AccountId, BalanceOf<T, I>>>) {
		if let Some(Deposit { who, amount }) = deposit {
			T::Slash::on_unbalanced(T::Currency::slash_reserved(&who, amount).0);
			Self::deposit_event(Event::<T, I>::DepositSlashed { who, amount });
		}
	}

	/// Get the track info value for the track `id`.
	fn track(id: TrackIdOf<T, I>) -> Option<&'static TrackInfoOf<T, I>> {
		let tracks = T::Tracks::tracks();
		let index = tracks.binary_search_by_key(&id, |x| x.0).unwrap_or_else(|x| x);
		Some(&tracks[index].1)
	}

	/// Determine whether the given `tally` would result in a referendum passing at `elapsed` blocks
	/// into a total decision `period`, given the two curves for `support_needed` and
	/// `approval_needed`.
	fn is_passing(
		tally: &T::Tally,
		elapsed: T::BlockNumber,
		period: T::BlockNumber,
		support_needed: &Curve,
		approval_needed: &Curve,
		id: TrackIdOf<T, I>,
	) -> bool {
		let x = Perbill::from_rational(elapsed.min(period), period);
		support_needed.passing(x, tally.support(id)) &&
			approval_needed.passing(x, tally.approval(id))
	}
}
