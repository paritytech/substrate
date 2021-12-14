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

//! # Referenda Pallet
//!
//! - [`Config`]
//! - [`Call`]
//!
//! ## Overview
//!
//! The Referenda pallet handles the administration of general stakeholder voting.

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
		Polls, ReservableCurrency, VoteTally,
	},
	BoundedVec,
};
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{AtLeast32BitUnsigned, Dispatchable, One, Saturating},
	DispatchError, DispatchResult, Perbill,
};
use sp_std::{fmt::Debug, prelude::*};

mod types;
pub mod weights;
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

//#[cfg(feature = "runtime-benchmarks")]
//pub mod benchmarking;

const ASSEMBLY_ID: LockIdentifier = *b"assembly";

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::{pallet_prelude::*, traits::EnsureOrigin, weights::Pays, Parameter};
	use frame_system::pallet_prelude::*;
	use sp_runtime::DispatchResult;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
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
			tally: T::Tally,
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
		/// The dispatch origin of this call must be _Signed_ and the sender must
		/// have funds to cover the deposit.
		///
		/// - `proposal_origin`: The origin from which the proposal should be executed.
		/// - `proposal_hash`: The hash of the proposal preimage.
		/// - `enactment_moment`: The moment that the proposal should be enacted.
		///
		/// Emits `Submitted`.
		#[pallet::weight(0)]
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
				ayes_in_queue: None,
				alarm: Self::set_alarm(nudge_call, now + T::UndecidingTimeout::get()),
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
			let mut status = Self::ensure_ongoing(index)?;
			ensure!(status.decision_deposit.is_none(), Error::<T>::HaveDeposit);
			let track = Self::track(status.track).ok_or(Error::<T>::NoTrack)?;
			status.decision_deposit = Some(Self::take_deposit(who, track.decision_deposit)?);
			let now = frame_system::Pallet::<T>::block_number();
			let info = Self::service_referendum(now, index, status).0;
			ReferendumInfoFor::<T>::insert(index, info);
			Ok(())
		}

		#[pallet::weight(0)]
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
			Self::refund_deposit(Some(deposit));
			ReferendumInfoFor::<T>::insert(index, info);
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn cancel(origin: OriginFor<T>, index: ReferendumIndex) -> DispatchResult {
			T::CancelOrigin::ensure_origin(origin)?;
			let status = Self::ensure_ongoing(index)?;
			let track = Self::track(status.track).ok_or(Error::<T>::BadTrack)?;
			if let Some((_, last_alarm)) = status.alarm {
				let _ = T::Scheduler::cancel(last_alarm);
			}
			Self::note_one_fewer_deciding(status.track, track);
			Self::deposit_event(Event::<T>::Cancelled { index, tally: status.tally });
			let info = ReferendumInfo::Cancelled(
				frame_system::Pallet::<T>::block_number(),
				status.submission_deposit,
				status.decision_deposit,
			);
			ReferendumInfoFor::<T>::insert(index, info);
			Ok(())
		}

		#[pallet::weight(0)]
		pub fn kill(origin: OriginFor<T>, index: ReferendumIndex) -> DispatchResult {
			T::KillOrigin::ensure_origin(origin)?;
			let status = Self::ensure_ongoing(index)?;
			let track = Self::track(status.track).ok_or(Error::<T>::BadTrack)?;
			if let Some((_, last_alarm)) = status.alarm {
				let _ = T::Scheduler::cancel(last_alarm);
			}
			Self::note_one_fewer_deciding(status.track, track);
			Self::deposit_event(Event::<T>::Killed { index, tally: status.tally });
			Self::slash_deposit(Some(status.submission_deposit));
			Self::slash_deposit(status.decision_deposit);
			let info = ReferendumInfo::Killed(frame_system::Pallet::<T>::block_number());
			ReferendumInfoFor::<T>::insert(index, info);
			Ok(())
		}

		/// Advance a referendum onto its next logical state. This should happen automaically,
		/// but this exists in order to allow it to happen manaully in case it is needed.
		#[pallet::weight(0)]
		pub fn nudge_referendum(origin: OriginFor<T>, index: ReferendumIndex) -> DispatchResult {
			ensure_signed_or_root(origin)?;
			Self::advance_referendum(index)?;
			Ok(())
		}

		/// Advance a track onto its next logical state. This should happen automaically,
		/// but this exists in order to allow it to happen manaully in case it is needed.
		#[pallet::weight(0)]
		pub fn nudge_track(
			origin: OriginFor<T>,
			track: TrackIdOf<T>,
		) -> DispatchResultWithPostInfo {
			ensure_signed_or_root(origin)?;
			Self::advance_track(track)?;
			Ok(Pays::No.into())
		}
	}
}

impl<T: Config> Polls<T::Tally> for Pallet<T> {
	type Index = ReferendumIndex;
	type Votes = VotesOf<T>;
	type Moment = T::BlockNumber;
	type Class = TrackIdOf<T>;

	fn access_poll<R>(
		index: Self::Index,
		f: impl FnOnce(PollStatus<&mut T::Tally, T::BlockNumber>) -> R,
	) -> R {
		match ReferendumInfoFor::<T>::get(index) {
			Some(ReferendumInfo::Ongoing(mut status)) => {
				let result = f(PollStatus::Ongoing(&mut status.tally));
				let now = frame_system::Pallet::<T>::block_number();
				let (info, _) = Self::service_referendum(now, index, status);
				ReferendumInfoFor::<T>::insert(index, info);
				result
			},
			Some(ReferendumInfo::Approved(end, ..)) => f(PollStatus::Completed(end, true)),
			Some(ReferendumInfo::Rejected(end, ..)) => f(PollStatus::Completed(end, false)),
			_ => f(PollStatus::None),
		}
	}

	fn try_access_poll<R>(
		index: Self::Index,
		f: impl FnOnce(PollStatus<&mut T::Tally, T::BlockNumber>) -> Result<R, DispatchError>,
	) -> Result<R, DispatchError> {
		match ReferendumInfoFor::<T>::get(index) {
			Some(ReferendumInfo::Ongoing(mut status)) => {
				let result = f(PollStatus::Ongoing(&mut status.tally))?;
				let now = frame_system::Pallet::<T>::block_number();
				let (info, _) = Self::service_referendum(now, index, status);
				ReferendumInfoFor::<T>::insert(index, info);
				Ok(result)
			},
			Some(ReferendumInfo::Approved(end, ..)) => f(PollStatus::Completed(end, true)),
			Some(ReferendumInfo::Rejected(end, ..)) => f(PollStatus::Completed(end, false)),
			_ => f(PollStatus::None),
		}
	}

	fn tally<R>(index: Self::Index) -> Option<T::Tally> {
		Some(Self::ensure_ongoing(index).ok()?.tally)
	}

	fn is_active(index: Self::Index) -> Option<TrackIdOf<T>> {
		Self::ensure_ongoing(index).ok().map(|e| e.track)
	}
}

impl<T: Config> Pallet<T> {
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

	/// Set an alarm.
	fn set_alarm(call: impl Into<CallOf<T>>, when: T::BlockNumber) -> Option<(T::BlockNumber, ScheduleAddressOf<T>)> {
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
			"Unable to schedule a new referendum at #{} (now: #{})?!",
			when,
			frame_system::Pallet::<T>::block_number()
		);
		maybe_result
	}

	fn ready_for_deciding(
		now: T::BlockNumber,
		track: &TrackInfoOf<T>,
		index: ReferendumIndex,
		status: &mut ReferendumStatusOf<T>,
	) {
		println!("ready_for_deciding ref #{:?}", index);
		let deciding_count = DecidingCount::<T>::get(status.track);
		if deciding_count < track.max_deciding {
			// Begin deciding.
			println!("Beginning deciding...");
			status.begin_deciding(now, track.decision_period);
			DecidingCount::<T>::insert(status.track, deciding_count.saturating_add(1));
		} else {
			// Add to queue.
			println!("Queuing for decision.");
			let item = (index, status.tally.ayes());
			status.ayes_in_queue = Some(status.tally.ayes());
			TrackQueue::<T>::mutate(status.track, |q| q.insert_sorted_by_key(item, |x| x.1));
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
				Err(_) => debug_assert!(false, "Queued referendum not ongoing?!"),
			}
		}
	}

	/// Advance a track - this dequeues one or more referenda from the from the `TrackQueue` of
	/// referenda which are ready to be decided until the `DecidingCount` is equal to the track's
	/// `max_deciding`.
	///
	/// This should never be needed, since referenda should automatically begin when others end.
	fn advance_track(track: TrackIdOf<T>) -> Result<u32, DispatchError> {
		let track_info = Self::track(track).ok_or(Error::<T>::BadTrack)?;
		let mut deciding_count = DecidingCount::<T>::get(track);
		let mut track_queue = TrackQueue::<T>::get(track);
		let mut count = 0;
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

	/// Attempts to advance the referendum. Returns `Ok` if something useful happened.
	fn advance_referendum(index: ReferendumIndex) -> DispatchResult {
		let now = frame_system::Pallet::<T>::block_number();
		let status = Self::ensure_ongoing(index)?;
		let (info, dirty) = Self::service_referendum(now, index, status);
		if dirty {
			ReferendumInfoFor::<T>::insert(index, info);
		}
		Ok(())
	}

	/// Action item for when there is now one fewer referendum in the deciding phase and the
	/// `DecidingCount` is not yet updated. This means that we should either:
	/// - begin deciding another referendum (and leave `DecidingCount` alone); or
	/// - decrement `DecidingCount`.
	fn note_one_fewer_deciding(track: TrackIdOf<T>, track_info: &TrackInfoOf<T>) {
		let mut track_queue = TrackQueue::<T>::get(track);
		if let Some((index, mut status)) = Self::next_for_deciding(&mut track_queue) {
			let now = frame_system::Pallet::<T>::block_number();
			status.begin_deciding(now, track_info.decision_period);
			ReferendumInfoFor::<T>::insert(index, ReferendumInfo::Ongoing(status));
			TrackQueue::<T>::insert(track, track_queue);
		} else {
			DecidingCount::<T>::mutate(track, |x| x.saturating_dec());
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
	) -> (ReferendumInfoOf<T>, bool) {
		println!("#{:?}: Servicing #{:?}", now, index);
		let mut dirty = false;
		// Should it begin being decided?
		let track = match Self::track(status.track) {
			Some(x) => x,
			None => return (ReferendumInfo::Ongoing(status), false),
		};
		let timeout = status.submitted + T::UndecidingTimeout::get();
		// Default the alarm to the submission timeout.
		let mut alarm = timeout;
		if status.deciding.is_none() {
			// Are we already queued for deciding?
			if let Some(_) = status.ayes_in_queue.as_ref() {
				println!("Already queued...");
				// Does our position in the queue need updating?
				let ayes = status.tally.ayes();
				let mut queue = TrackQueue::<T>::get(status.track);
				let maybe_old_pos = queue.iter().position(|(x, _)| *x == index);
				let new_pos = queue.binary_search_by_key(&ayes, |x| x.1).unwrap_or_else(|x| x);
				if maybe_old_pos.is_none() && new_pos < queue.len() {
					// Just insert.
					queue.force_insert(new_pos, (index, ayes));
				} else if let Some(old_pos) = maybe_old_pos {
					// We were in the queue - just update and sort.
					queue[old_pos].1 = ayes;
					if new_pos < old_pos {
						queue[new_pos..=old_pos].rotate_right(1);
					} else if old_pos < new_pos {
						queue[old_pos..=new_pos].rotate_left(1);
					}
				}
				TrackQueue::<T>::insert(status.track, queue);
			} else {
				// Are we ready for deciding?
				if status.decision_deposit.is_some() {
					let prepare_end = status.submitted.saturating_add(track.prepare_period);
					if now >= prepare_end {
						Self::ready_for_deciding(now, &track, index, &mut status);
						dirty = true;
					} else {
						println!("Not deciding, have DD, within PP: Setting alarm to end of PP");
						alarm = alarm.min(prepare_end);
					}
				}
			}
		}
		if let Some(deciding) = &mut status.deciding {
			let is_passing = Self::is_passing(
				&status.tally,
				now,
				deciding.period,
				&track.min_turnout,
				&track.min_approval,
			);
			if is_passing {
				if deciding.confirming.map_or(false, |c| now >= c) {
					// Passed!
					Self::kill_alarm(&mut status);
					Self::note_one_fewer_deciding(status.track, track);
					let (desired, call_hash) = (status.enactment, status.proposal_hash);
					Self::schedule_enactment(index, track, desired, status.origin, call_hash);
					Self::deposit_event(Event::<T>::Confirmed { index, tally: status.tally });
					return (
						ReferendumInfo::Approved(
							now,
							status.submission_deposit,
							status.decision_deposit,
						),
						true,
					)
				}
				dirty = dirty || deciding.confirming.is_none();
				let confirmation =
					deciding.confirming.unwrap_or_else(|| now.saturating_add(track.confirm_period));
				deciding.confirming = Some(confirmation);
				alarm = confirmation;
			} else {
				if now >= deciding.ending {
					// Failed!
					Self::kill_alarm(&mut status);
					Self::note_one_fewer_deciding(status.track, track);
					Self::deposit_event(Event::<T>::Rejected { index, tally: status.tally });
					return (
						ReferendumInfo::Rejected(
							now,
							status.submission_deposit,
							status.decision_deposit,
						),
						true,
					)
				}
				// Cannot be confirming
				dirty = dirty || deciding.confirming.is_some();
				deciding.confirming = None;
				let decision_time = Self::decision_time(&deciding, &status.tally, track);
				alarm = decision_time;
			}
		} else if now >= timeout {
			// Too long without being decided - end it.
			Self::kill_alarm(&mut status);
			Self::deposit_event(Event::<T>::TimedOut { index, tally: status.tally });
			return (
				ReferendumInfo::TimedOut(now, status.submission_deposit, status.decision_deposit),
				true,
			)
		}

		if !status.alarm.as_ref().map_or(false, |&(when, _)| when == alarm) {
			println!("Setting alarm at block #{:?} for ref {:?}", alarm, index);
			// Either no alarm or one that was different
			Self::kill_alarm(&mut status);
			status.alarm = Self::set_alarm(Call::nudge_referendum { index }, alarm);
			dirty = true;
		} else {
			println!("Keeping alarm at block #{:?} for ref {:?}", alarm, index);
		}
		(ReferendumInfo::Ongoing(status), dirty)
	}

	fn decision_time(
		deciding: &DecidingStatusOf<T>,
		tally: &T::Tally,
		track: &TrackInfoOf<T>,
	) -> T::BlockNumber {
		// Set alarm to the point where the current voting would make it pass.
		let approval = tally.approval();
		let turnout = tally.turnout();
		let until_approval = track.min_approval.delay(approval);
		let until_turnout = track.min_turnout.delay(turnout);
		let offset = until_turnout.max(until_approval);
		deciding
			.ending
			.saturating_sub(deciding.period)
			.saturating_add(offset * deciding.period)
	}

	fn kill_alarm(status: &mut ReferendumStatusOf<T>) {
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
		}
	}

	fn track(id: TrackIdOf<T>) -> Option<&'static TrackInfoOf<T>> {
		let tracks = T::Tracks::tracks();
		let index = tracks.binary_search_by_key(&id, |x| x.0).unwrap_or_else(|x| x);
		Some(&tracks[index].1)
	}

	fn is_passing(
		tally: &T::Tally,
		now: T::BlockNumber,
		period: T::BlockNumber,
		turnout_needed: &Curve,
		approval_needed: &Curve,
	) -> bool {
		let x = Perbill::from_rational(now.min(period), period);
		turnout_needed.passing(x, tally.turnout()) && approval_needed.passing(x, tally.approval())
	}
}
