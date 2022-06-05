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

//! # Scheduler
//! A Pallet for scheduling dispatches.
//!
//! - [`Config`]
//! - [`Call`]
//! - [`Pallet`]
//!
//! ## Overview
//!
//! This Pallet exposes capabilities for scheduling dispatches to occur at a
//! specified block number or at a specified period. These scheduled dispatches
//! may be named or anonymous and may be canceled.
//!
//! **NOTE:** The scheduled calls will be dispatched with the default filter
//! for the origin: namely `frame_system::Config::BaseCallFilter` for all origin
//! except root which will get no filter. And not the filter contained in origin
//! use to call `fn schedule`.
//!
//! If a call is scheduled using proxy or whatever mecanism which adds filter,
//! then those filter will not be used when dispatching the schedule call.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! * `schedule` - schedule a dispatch, which may be periodic, to occur at a specified block and
//!   with a specified priority.
//! * `cancel` - cancel a scheduled dispatch, specified by block number and index.
//! * `schedule_named` - augments the `schedule` interface with an additional `Vec<u8>` parameter
//!   that can be used for identification.
//! * `cancel_named` - the named complement to the cancel function.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;
#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;
pub mod weights;

use codec::{Codec, Decode, Encode};
use derivative::Derivative;
use frame_support::{
	dispatch::{DispatchError, DispatchResult, Dispatchable, Parameter},
	pallet_prelude::MaxEncodedLen,
	traits::{
		defensive_prelude::*,
		schedule::{self, DispatchTime, MaybeHashed},
		EnsureOrigin, Get, IsType, OriginTrait, PalletInfoAccess, PrivilegeCmp, StorageVersion,
	},
	weights::{GetDispatchInfo, Weight},
	BoundedVec,
};
use frame_system::{self as system, ensure_signed};
pub use pallet::*;
use scale_info::TypeInfo;
use sp_runtime::{
	traits::{BadOrigin, One, Saturating, Zero},
	RuntimeDebug,
};
use sp_std::{cmp::Ordering, marker::PhantomData, prelude::*};
pub use weights::WeightInfo;

/// Just a simple index for naming period tasks.
pub type PeriodicIndex = u32;
/// The location of a scheduled task that can be used to remove it.
pub type TaskAddress<BlockNumber> = (BlockNumber, u32);

/// Wraps a `CallOrHashOf` to make it compatible with MaxEncodedLen
/// since a `Call` is otherwise not encodable with limited length.
#[derive(MaxEncodedLen, Debug, Decode, Clone, Encode, PartialEq, Eq, scale_info::TypeInfo)]
#[codec(mel_bound(T: Config))]
#[scale_info(skip_type_params(T))]
pub struct EncodedCallOrHashOf<T: Config>(pub BoundedVec<u8, <T as Config>::MaxCallLen>);

pub type CallOrHashOf<T> = MaybeHashed<<T as Config>::Call, <T as frame_system::Config>::Hash>;

impl<T: Config> EncodedCallOrHashOf<T> {
	/// Creates a new `Self` from the given `CallOrHashOf`.
	pub fn new(inner: CallOrHashOf<T>) -> Result<Self, crate::Error<T>> {
		let encoded: BoundedVec<u8, <T as Config>::MaxCallLen> =
			inner.encode().try_into().map_err(|_| crate::Error::CallTooLong)?;
		Ok(Self(encoded))
	}

	/// Creates a new `Self` from the given `Call`.
	pub fn from_call(call: <T as Config>::Call) -> Result<Self, crate::Error<T>> {
		Self::new(call.into())
	}

	/// Returns the wrapped `CallOrHashOf`.
	pub fn into_inner(self) -> CallOrHashOf<T> {
		CallOrHashOf::<T>::decode(&mut &self.0[..]).expect("Must decode")
	}
}

#[cfg_attr(any(feature = "std", test), derive(PartialEq, Eq))]
#[derive(Clone, RuntimeDebug, Encode, Decode)]
struct ScheduledV1<Call, BlockNumber> {
	maybe_id: Option<Vec<u8>>,
	priority: schedule::Priority,
	call: Call,
	maybe_periodic: Option<schedule::Period<BlockNumber>>,
}

// NOTE: use `Derivative` here until <https://github.com/rust-lang/rust/issues/26925> is fixed.
// The problem is that `#[derive(Clone)]` requires `Clone` for ALL its generic types,
// which does not make sense for `Get<>`.
#[derive(Derivative)]
#[derivative(Clone(bound = "T: Clone"), PartialEq(bound = "T: PartialEq"), Eq(bound = "T: Eq"))]
#[derive(Debug, Decode, Encode, scale_info::TypeInfo)]
#[scale_info(skip_type_params(S))]
pub struct BoundedCodecWrapper<T, S: Get<u32>>(pub BoundedVec<u8, S>, PhantomData<T>);

impl<T, S> MaxEncodedLen for BoundedCodecWrapper<T, S>
where
	S: Get<u32>,
{
	fn max_encoded_len() -> usize {
		S::get() as usize
	}
}

impl<T, S> BoundedCodecWrapper<T, S>
where
	T: codec::Encode + codec::Decode,
	S: Get<u32>,
{
	/// Creates a new `Self` from the given `T`.
	//
	// NOTE: No `TryFrom/TryInto` possible until <https://github.com/rust-lang/rust/issues/50133>.
	pub fn try_from(inner: T) -> Result<Self, ()> {
		let encoded: BoundedVec<u8, S> = inner.encode().try_into().map_err(|_| ())?;
		Ok(Self(encoded, PhantomData::<T>::default()))
	}

	/// Returns the wrapped `CallOrHashOf`.
	pub fn try_into_inner(self) -> Result<T, ()> {
		Decode::decode(&mut &self.0[..]).map_err(|_| ())
	}
}

/// Information regarding an item to be executed in the future.
#[cfg_attr(any(feature = "std", test), derive(PartialEq, Eq))]
#[derive(Clone, RuntimeDebug, Encode, Decode, TypeInfo, MaxEncodedLen)]
pub struct ScheduledV3<Call, BlockNumber, PalletsOrigin, AccountId, ID> {
	/// The unique identity for this task, if there is one.
	maybe_id: Option<ID>,
	/// This task's priority.
	priority: schedule::Priority,
	/// The call to be dispatched.
	call: Call,
	/// If the call is periodic, then this points to the information concerning that.
	maybe_periodic: Option<schedule::Period<BlockNumber>>,
	/// The origin to dispatch the call.
	origin: PalletsOrigin,
	_phantom: PhantomData<AccountId>,
}

// V3 can be re-used for V4 and V2.
#[allow(unused_imports)]
use crate::{ScheduledV3 as ScheduledV4, ScheduledV3 as ScheduledV2};

pub type ScheduledV2Of<T> = ScheduledV3<
	<T as Config>::Call,
	<T as frame_system::Config>::BlockNumber,
	<T as Config>::PalletsOrigin,
	<T as frame_system::Config>::AccountId,
	Vec<u8>,
>;

pub type ScheduledV3Of<T> = ScheduledV3<
	CallOrHashOf<T>,
	<T as frame_system::Config>::BlockNumber,
	<T as Config>::PalletsOrigin,
	<T as frame_system::Config>::AccountId,
	Vec<u8>,
>;

pub type ScheduledV4Of<T> = ScheduledV3<
	EncodedCallOrHashOf<T>,
	<T as frame_system::Config>::BlockNumber,
	BoundedCodecWrapper<<T as Config>::PalletsOrigin, <T as Config>::MaxPalletsOriginLen>,
	<T as frame_system::Config>::AccountId,
	ScheduleIdOf<T>,
>;

pub type ScheduledOf<T> = ScheduledV4Of<T>;
pub type ScheduleIdOf<T> = BoundedVec<u8, <T as Config>::MaxScheduleIdLen>;

/// The current version of Scheduled struct. Can also be V2 or V3 since its the same struct.
pub type Scheduled<Call, BlockNumber, PalletsOrigin, AccountId, ID> =
	ScheduledV4<Call, BlockNumber, PalletsOrigin, AccountId, ID>;

#[cfg(feature = "runtime-benchmarks")]
mod preimage_provider {
	use frame_support::traits::PreimageRecipient;
	pub trait PreimageProviderAndMaybeRecipient<H>: PreimageRecipient<H> {}
	impl<H, T: PreimageRecipient<H>> PreimageProviderAndMaybeRecipient<H> for T {}
}

#[cfg(not(feature = "runtime-benchmarks"))]
mod preimage_provider {
	use frame_support::traits::PreimageProvider;
	pub trait PreimageProviderAndMaybeRecipient<H>: PreimageProvider<H> {}
	impl<H, T: PreimageProvider<H>> PreimageProviderAndMaybeRecipient<H> for T {}
}

pub use preimage_provider::PreimageProviderAndMaybeRecipient;

pub(crate) trait MarginalWeightInfo: WeightInfo {
	fn item(periodic: bool, named: bool, resolved: Option<bool>) -> Weight {
		match (periodic, named, resolved) {
			(_, false, None) => Self::on_initialize_aborted(2) - Self::on_initialize_aborted(1),
			(_, true, None) =>
				Self::on_initialize_named_aborted(2) - Self::on_initialize_named_aborted(1),
			(false, false, Some(false)) => Self::on_initialize(2) - Self::on_initialize(1),
			(false, true, Some(false)) =>
				Self::on_initialize_named(2) - Self::on_initialize_named(1),
			(true, false, Some(false)) =>
				Self::on_initialize_periodic(2) - Self::on_initialize_periodic(1),
			(true, true, Some(false)) =>
				Self::on_initialize_periodic_named(2) - Self::on_initialize_periodic_named(1),
			(false, false, Some(true)) =>
				Self::on_initialize_resolved(2) - Self::on_initialize_resolved(1),
			(false, true, Some(true)) =>
				Self::on_initialize_named_resolved(2) - Self::on_initialize_named_resolved(1),
			(true, false, Some(true)) =>
				Self::on_initialize_periodic_resolved(2) - Self::on_initialize_periodic_resolved(1),
			(true, true, Some(true)) =>
				Self::on_initialize_periodic_named_resolved(2) -
					Self::on_initialize_periodic_named_resolved(1),
		}
	}
}
impl<T: WeightInfo> MarginalWeightInfo for T {}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::{
		dispatch::PostDispatchInfo,
		pallet_prelude::*,
		traits::{schedule::LookupError, PreimageProvider},
	};
	use frame_system::pallet_prelude::*;

	/// The current storage version.
	const STORAGE_VERSION: StorageVersion = StorageVersion::new(4);

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	/// `system::Config` should always be included in our implied traits.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;

		/// The aggregated origin which the dispatch will take.
		type Origin: OriginTrait<PalletsOrigin = Self::PalletsOrigin>
			+ From<Self::PalletsOrigin>
			+ IsType<<Self as system::Config>::Origin>;

		/// The caller origin, overarching type of all pallets origins.
		type PalletsOrigin: From<system::RawOrigin<Self::AccountId>> + Codec + Clone + Eq + TypeInfo;

		/// The aggregated call type.
		type Call: Parameter
			+ Dispatchable<Origin = <Self as Config>::Origin, PostInfo = PostDispatchInfo>
			+ GetDispatchInfo
			+ From<system::Call<Self>>;

		/// The maximum weight that may be scheduled per block for any dispatchables of less
		/// priority than `schedule::HARD_DEADLINE`.
		#[pallet::constant]
		type MaximumWeight: Get<Weight>;

		/// Required origin to schedule or cancel calls.
		type ScheduleOrigin: EnsureOrigin<<Self as system::Config>::Origin>;

		/// Compare the privileges of origins.
		///
		/// This will be used when canceling a task, to ensure that the origin that tries
		/// to cancel has greater or equal privileges as the origin that created the scheduled task.
		///
		/// For simplicity the [`EqualPrivilegeOnly`](frame_support::traits::EqualPrivilegeOnly) can
		/// be used. This will only check if two given origins are equal.
		type OriginPrivilegeCmp: PrivilegeCmp<Self::PalletsOrigin>;

		/// Maximum number of tasks that an be scheduled in total.
		///
		/// Should be at least `MaxScheduledPerBlock` * `MaxAgendas`.
		#[pallet::constant]
		type MaxSchedules: Get<Option<u32>>;

		/// The maximum number of scheduled calls in the queue for a single block.
		/// Is strictly enforced and rejects scheduling more than this number of calls per block.
		///
		/// Must be at most `MaxSchedules`.
		#[pallet::constant]
		type MaxScheduledPerBlock: Get<u32>;

		/// Maximum length of a schedule ID.
		#[pallet::constant]
		type MaxScheduleIdLen: Get<u32>;

		/// Maximum number of agendas that can be scheduled.
		///
		/// Should be at most `MaxSchedules`.
		#[pallet::constant]
		type MaxAgendas: Get<Option<u32>>;

		/// Maximum length of a [`Self::Call`].
		#[pallet::constant]
		type MaxCallLen: Get<u32>;

		/// Maximum length of an encoded [`Self::PalletsOrigin`].
		#[pallet::constant]
		type MaxPalletsOriginLen: Get<u32>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// The preimage provider with which we look up call hashes to get the call.
		type PreimageProvider: PreimageProviderAndMaybeRecipient<Self::Hash>;

		/// If `Some` then the number of blocks to postpone execution for when the item is delayed.
		type NoPreimagePostponement: Get<Option<Self::BlockNumber>>;
	}

	/// Items to be executed, indexed by the block number that they should be executed on.
	#[pallet::storage]
	pub type Agenda<T: Config> = StorageMap<
		Hasher = Twox64Concat,
		Key = T::BlockNumber,
		Value = BoundedVec<ScheduledV4Of<T>, T::MaxScheduledPerBlock>,
		QueryKind = ValueQuery,
		MaxValues = T::MaxAgendas,
	>;

	/// Lookup from identity to the block number and index of the task.
	#[pallet::storage]
	pub(crate) type Lookup<T: Config> = StorageMap<
		Hasher = Twox64Concat,
		Key = ScheduleIdOf<T>,
		Value = TaskAddress<T::BlockNumber>,
		MaxValues = T::MaxSchedules,
	>;

	/// Events type.
	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Scheduled some task.
		Scheduled { when: T::BlockNumber, index: u32 },
		/// Canceled some task.
		Canceled { when: T::BlockNumber, index: u32 },
		/// Dispatched some task.
		Dispatched {
			task: TaskAddress<T::BlockNumber>,
			id: Option<ScheduleIdOf<T>>,
			result: DispatchResult,
		},
		/// The call for the provided hash was not found so the task has been aborted.
		CallLookupFailed {
			task: TaskAddress<T::BlockNumber>,
			id: Option<Vec<u8>>,
			error: LookupError,
		},
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Failed to schedule a call
		FailedToSchedule,
		/// Cannot find the scheduled call.
		NotFound,
		/// Given target block number is in the past.
		TargetBlockNumberInPast,
		/// Reschedule failed because it does not change scheduled time.
		RescheduleNoChange,
		/// The ID of a schedule was too long.
		ScheduleIdTooLong,
		/// The maximum number of agendas was reached.
		TooManyAgendas,
		CallTooLong,
		PalletsOriginTooLong,

		// Note: Defensive only - should never happen.
		CodecError,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		/// Execute the scheduled calls
		fn on_initialize(now: T::BlockNumber) -> Weight {
			let limit = T::MaximumWeight::get();

			let mut queued = Agenda::<T>::take(now).into_iter().enumerate().collect::<Vec<_>>();

			queued.sort_by_key(|(_, s)| s.priority);

			let next = now + One::one();

			let mut total_weight: Weight = T::WeightInfo::on_initialize(0);
			for (order, (index, mut s)) in queued.into_iter().enumerate() {
				let named = if let Some(ref id) = s.maybe_id {
					Lookup::<T>::remove(id);
					true
				} else {
					false
				};

				let (call, maybe_completed) = s.call.into_inner().resolved::<T::PreimageProvider>();
				let encoded_call = match EncodedCallOrHashOf::<T>::new(call.clone()).defensive_ok()
				{
					Some(encoded) => encoded,
					None => continue, // This is a defensive failure and should never happen.
				};
				s.call = encoded_call;

				let resolved = if let Some(completed) = maybe_completed {
					T::PreimageProvider::unrequest_preimage(&completed);
					true
				} else {
					false
				};

				//let call = s.call.clone().into_inner();
				let call = match call {
					MaybeHashed::Value(c) => c,
					MaybeHashed::Hash(hash) => {
						// Preimage not available - postpone until some block.
						total_weight.saturating_accrue(T::WeightInfo::item(false, named, None));
						if let Some(delay) = T::NoPreimagePostponement::get() {
							let until = now.saturating_add(delay);
							if let Some(ref id) = s.maybe_id {
								let index = Agenda::<T>::decode_len(until).unwrap_or(0);
								Lookup::<T>::insert(id, (until, index as u32));
							}

							if Agenda::<T>::try_append(until, s).is_err() {
								// There is not enough room in the future block where the call
								// should be re-scheduled. Nothing that we can do about it.

								T::PreimageProvider::unrequest_preimage(&hash);
							}
						}
						continue
					},
				};

				let periodic = s.maybe_periodic.is_some();
				let call_weight = call.get_dispatch_info().weight;
				let mut item_weight = T::WeightInfo::item(periodic, named, Some(resolved));
				let decoded_origin = s
					.origin
					.clone()
					.try_into_inner()
					.expect("The call was encoded successfully and must therefore decode; qed");
				let origin =
					<<T as Config>::Origin as From<T::PalletsOrigin>>::from(decoded_origin.clone())
						.into();
				if ensure_signed(origin).is_ok() {
					// Weights of Signed dispatches expect their signing account to be whitelisted.
					item_weight.saturating_accrue(T::DbWeight::get().reads_writes(1, 1));
				}

				// We allow a scheduled call if any is true:
				// - It's priority is `HARD_DEADLINE`
				// - It does not push the weight past the limit.
				// - It is the first item in the schedule
				let hard_deadline = s.priority <= schedule::HARD_DEADLINE;
				let test_weight =
					total_weight.saturating_add(call_weight).saturating_add(item_weight);
				if !hard_deadline && order > 0 && test_weight > limit {
					// Cannot be scheduled this block - postpone until next.
					total_weight.saturating_accrue(T::WeightInfo::item(false, named, None));
					if let Some(ref id) = s.maybe_id {
						// NOTE: We could reasonably not do this (in which case there would be one
						// block where the named and delayed item could not be referenced by name),
						// but we will do it anyway since it should be mostly free in terms of
						// weight and it is slightly cleaner.
						let index = Agenda::<T>::decode_len(next).unwrap_or(0);
						Lookup::<T>::insert(id, (next, index as u32));
					}
					Agenda::<T>::try_append(next, s)
						.map_err(|_| Error::<T>::TooManyAgendas)
						.expect("TODO Failed to schedule future block");
					continue
				}

				let dispatch_origin = decoded_origin.into();
				let (maybe_actual_call_weight, result) = match call.dispatch(dispatch_origin) {
					Ok(post_info) => (post_info.actual_weight, Ok(())),
					Err(error_and_info) =>
						(error_and_info.post_info.actual_weight, Err(error_and_info.error)),
				};
				let actual_call_weight = maybe_actual_call_weight.unwrap_or(call_weight);
				total_weight.saturating_accrue(item_weight);
				total_weight.saturating_accrue(actual_call_weight);

				Self::deposit_event(Event::Dispatched {
					task: (now, index as u32),
					id: s.maybe_id.clone(),
					result,
				});

				if let &Some((period, count)) = &s.maybe_periodic {
					if count > 1 {
						s.maybe_periodic = Some((period, count - 1));
					} else {
						s.maybe_periodic = None;
					}
					let wake = now + period;
					// If scheduled is named, place its information in `Lookup`
					if let Some(ref id) = s.maybe_id {
						let wake_index = Agenda::<T>::decode_len(wake).unwrap_or(0);
						Lookup::<T>::insert(id, (wake, wake_index as u32));
					}
					Agenda::<T>::try_append(wake, s)
						.map_err(|_| Error::<T>::TooManyAgendas)
						.expect("TODO Failed to schedule future block");
				}
			}
			total_weight
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Anonymously schedule a task.
		#[pallet::weight(<T as Config>::WeightInfo::schedule(T::MaxScheduledPerBlock::get()))]
		pub fn schedule(
			origin: OriginFor<T>,
			when: T::BlockNumber,
			maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
			priority: schedule::Priority,
			call: Box<CallOrHashOf<T>>,
		) -> DispatchResult {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Config>::Origin::from(origin);
			Self::do_schedule(
				DispatchTime::At(when),
				maybe_periodic,
				priority,
				origin.caller().clone(),
				*call,
			)?;
			Ok(())
		}

		/// Cancel an anonymously scheduled task.
		#[pallet::weight(<T as Config>::WeightInfo::cancel(T::MaxScheduledPerBlock::get()))]
		pub fn cancel(origin: OriginFor<T>, when: T::BlockNumber, index: u32) -> DispatchResult {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Config>::Origin::from(origin);
			Self::do_cancel(Some(origin.caller().clone()), (when, index))?;
			Ok(())
		}

		/// Schedule a named task.
		#[pallet::weight(<T as Config>::WeightInfo::schedule_named(T::MaxScheduledPerBlock::get()))]
		pub fn schedule_named(
			origin: OriginFor<T>,
			id: Vec<u8>,
			when: T::BlockNumber,
			maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
			priority: schedule::Priority,
			call: Box<CallOrHashOf<T>>,
		) -> DispatchResult {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Config>::Origin::from(origin);
			let id: ScheduleIdOf<T> =
				id.clone().try_into().map_err(|_| Error::<T>::ScheduleIdTooLong)?;

			Self::do_schedule_named(
				id,
				DispatchTime::At(when),
				maybe_periodic,
				priority,
				origin.caller().clone(),
				*call,
			)?;
			Ok(())
		}

		/// Cancel a named scheduled task.
		#[pallet::weight(<T as Config>::WeightInfo::cancel_named(T::MaxScheduledPerBlock::get()))]
		pub fn cancel_named(origin: OriginFor<T>, id: Vec<u8>) -> DispatchResult {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Config>::Origin::from(origin);
			let id: ScheduleIdOf<T> =
				id.clone().try_into().map_err(|_| Error::<T>::ScheduleIdTooLong)?;

			Self::do_cancel_named(Some(origin.caller().clone()), id)?;
			Ok(())
		}

		/// Anonymously schedule a task after a delay.
		///
		/// # <weight>
		/// Same as [`schedule`].
		/// # </weight>
		#[pallet::weight(<T as Config>::WeightInfo::schedule(T::MaxScheduledPerBlock::get()))]
		pub fn schedule_after(
			origin: OriginFor<T>,
			after: T::BlockNumber,
			maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
			priority: schedule::Priority,
			call: Box<CallOrHashOf<T>>,
		) -> DispatchResult {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Config>::Origin::from(origin);
			Self::do_schedule(
				DispatchTime::After(after),
				maybe_periodic,
				priority,
				origin.caller().clone(),
				*call,
			)?;
			Ok(())
		}

		/// Schedule a named task after a delay.
		///
		/// # <weight>
		/// Same as [`schedule_named`](Self::schedule_named).
		/// # </weight>
		#[pallet::weight(<T as Config>::WeightInfo::schedule_named(T::MaxScheduledPerBlock::get()))]
		pub fn schedule_named_after(
			origin: OriginFor<T>,
			id: Vec<u8>,
			after: T::BlockNumber,
			maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
			priority: schedule::Priority,
			call: Box<CallOrHashOf<T>>,
		) -> DispatchResult {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Config>::Origin::from(origin);
			let id: ScheduleIdOf<T> =
				id.clone().try_into().map_err(|_| Error::<T>::ScheduleIdTooLong)?;

			Self::do_schedule_named(
				id,
				DispatchTime::After(after),
				maybe_periodic,
				priority,
				origin.caller().clone(),
				*call,
			)?;
			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Migrate storage format from V1 to V4.
	///
	/// Returns the weight consumed by this migration.
	pub fn migrate_v1_to_v4() -> Weight {
		let mut weight = T::DbWeight::get().reads_writes(1, 1);

		Agenda::<T>::translate::<Vec<Option<ScheduledV1<<T as Config>::Call, T::BlockNumber>>>, _>(
			|_, agenda| {
				Some(
					agenda
						.into_iter()
						.filter_map(|s| s)
						.map(|schedule| {
							weight.saturating_accrue(T::DbWeight::get().reads_writes(1, 1));

							let call = EncodedCallOrHashOf::<T>::from_call(schedule.call)
								.expect("Expected to encode call into V4 format");
							let id = schedule.maybe_id.map(|id| {
								id.try_into()
									.expect("ID too long, cannot migrate. Try to increase ")
							});

							ScheduledV4Of::<T> {
								maybe_id: id,
								priority: schedule.priority,
								call: call.into(),
								maybe_periodic: schedule.maybe_periodic,
								origin: BoundedCodecWrapper::try_from(
									system::RawOrigin::Root.into(),
								)
								.expect("Cannot encode origin. Increase `MaxPalletsOriginLen`."),
								_phantom: Default::default(),
							}
						})
						.collect::<Vec<_>>()
						.try_into()
						.expect("V1 schedules fit in storage; Therefore V3 fit in storage; qed"),
				)
			},
		);

		#[allow(deprecated)]
		frame_support::storage::migration::remove_storage_prefix(
			Self::name().as_bytes(),
			b"StorageVersion",
			&[],
		);

		StorageVersion::new(4).put::<Self>();

		weight + T::DbWeight::get().writes(2)
	}

	/// Migrate storage format from V3 to V4.
	///
	/// Returns the weight consumed by this migration.
	pub fn migrate_v3_to_v4() -> Weight {
		let mut weight = T::DbWeight::get().reads_writes(1, 1);

		Agenda::<T>::translate::<Vec<Option<ScheduledV3Of<T>>>, _>(|_, agenda| {
			Some(
				agenda
					.into_iter()
					.filter_map(|s| s)
					.map(|schedule| {
						weight.saturating_accrue(T::DbWeight::get().reads_writes(1, 1));
							let call = EncodedCallOrHashOf::<T>::new(schedule.call).expect("TODO");
							let id = schedule.maybe_id.map(|id|
								id.try_into().expect("ID too long")
							);

							ScheduledV4Of::<T> {
							maybe_id: id,
							priority: schedule.priority,
							call: call.into(),
							maybe_periodic: schedule.maybe_periodic,
							origin: BoundedCodecWrapper::try_from(schedule.origin).expect("Cannot encode origin. Increase `MaxPalletsOriginLen`."),
							_phantom: Default::default(),
						}
					})
					.collect::<Vec<_>>()
					.try_into()
					.expect("V1 schedules fit in storage; The number of V3 schedules is the same as V1; Therefore V3 fit in storage; qed"),
			)
		});

		#[allow(deprecated)]
		frame_support::storage::migration::remove_storage_prefix(
			Self::name().as_bytes(),
			b"StorageVersion",
			&[],
		);

		StorageVersion::new(4).put::<Self>();

		weight + T::DbWeight::get().writes(2)
	}

	/// Migrate storage format from V2 to V4.
	///
	/// Returns the weight consumed by this migration.
	pub fn migrate_v2_to_v4() -> Weight {
		let mut weight = T::DbWeight::get().reads_writes(1, 1);

		Agenda::<T>::translate::<Vec<Option<ScheduledV2Of<T>>>, _>(|_, agenda| {
			Some(
				agenda
					.into_iter()
					.filter_map(|s| s)
					.map(|schedule| {
						weight.saturating_accrue(T::DbWeight::get().reads_writes(1, 1));
							let call = EncodedCallOrHashOf::<T>::from_call(schedule.call).expect("TODO");
							let id = schedule.maybe_id.map(|id|
								id.try_into().expect("ID too long")
							);

							ScheduledV4Of::<T> {
							maybe_id: id,
							priority: schedule.priority,
							call: call.into(),
							maybe_periodic: schedule.maybe_periodic,
							origin: BoundedCodecWrapper::try_from(schedule.origin).expect("Cannot encode origin. Increase `MaxPalletsOriginLen`."),
							_phantom: Default::default(),
						}
					})
					.collect::<Vec<_>>()
					.try_into()
					.expect("V1 schedules fit in storage; The number of V3 schedules is the same as V1; Therefore V3 fit in storage; qed"),
			)
		});

		#[allow(deprecated)]
		frame_support::storage::migration::remove_storage_prefix(
			Self::name().as_bytes(),
			b"StorageVersion",
			&[],
		);

		StorageVersion::new(4).put::<Self>();

		weight + T::DbWeight::get().writes(2)
	}

	#[cfg(feature = "try-runtime")]
	pub fn pre_migrate_to_v4() -> Result<(), &'static str> {
		assert!(<P as GetStorageVersion>::on_chain_storage_version() < 4, "Cannot downgrade");
		Ok(())
	}

	#[cfg(feature = "try-runtime")]
	pub fn post_migrate_to_v4() -> Result<(), &'static str> {
		use frame_support::dispatch::GetStorageVersion;

		assert!(Self::current_storage_version() == 4);
		assert!(Self::on_chain_storage_version() == StorageVersion::new(4));
		for k in Agenda::<T>::iter_keys() {
			let _ = Agenda::<T>::try_get(k).map_err(|()| "Invalid item in Agenda")?;
		}
		Ok(())
	}

	/// Helper to migrate scheduler when the pallet origin type has changed.
	pub fn migrate_origin<OldOrigin: Into<T::PalletsOrigin> + codec::Decode>() {
		Agenda::<T>::translate::<
			Vec<
				Scheduled<
					EncodedCallOrHashOf<T>,
					T::BlockNumber,
					OldOrigin,
					T::AccountId,
					ScheduleIdOf<T>,
				>,
			>,
			_,
		>(|_, agenda| {
			Some(
				agenda
					.into_iter()
					.map(|schedule| Scheduled {
						maybe_id: schedule.maybe_id,
						priority: schedule.priority,
						call: schedule.call.into(),
						maybe_periodic: schedule.maybe_periodic,
						origin: BoundedCodecWrapper::try_from(schedule.origin.into())
							.expect("Cannot encode origin. Increase `MaxPalletsOriginLen`."),
						_phantom: Default::default(),
					})
					.collect::<Vec<_>>()
					.try_into()
					.expect("The number of elements does not change from translate; qed"),
			)
		});
	}

	fn resolve_time(when: DispatchTime<T::BlockNumber>) -> Result<T::BlockNumber, DispatchError> {
		let now = frame_system::Pallet::<T>::block_number();

		let when = match when {
			DispatchTime::At(x) => x,
			// The current block has already completed it's scheduled tasks, so
			// Schedule the task at lest one block after this current block.
			DispatchTime::After(x) => now.saturating_add(x).saturating_add(One::one()),
		};

		if when <= now {
			return Err(Error::<T>::TargetBlockNumberInPast.into())
		}

		Ok(when)
	}

	fn do_schedule(
		when: DispatchTime<T::BlockNumber>,
		maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
		priority: schedule::Priority,
		origin: T::PalletsOrigin,
		call: CallOrHashOf<T>,
	) -> Result<TaskAddress<T::BlockNumber>, DispatchError> {
		let when = Self::resolve_time(when)?;
		call.ensure_requested::<T::PreimageProvider>();
		let call = EncodedCallOrHashOf::<T>::new(call)?;

		// sanitize maybe_periodic
		let maybe_periodic = maybe_periodic
			.filter(|p| p.1 > 1 && !p.0.is_zero())
			// Remove one from the number of repetitions since we will schedule one now.
			.map(|(p, c)| (p, c - 1));
		let s = Scheduled {
			maybe_id: None,
			priority,
			call,
			maybe_periodic,
			origin: BoundedCodecWrapper::try_from(origin)
				.map_err(|_| Error::<T>::PalletsOriginTooLong)?,
			_phantom: PhantomData::<T::AccountId>::default(),
		};
		Agenda::<T>::try_append(when, s).map_err(|_| Error::<T>::TooManyAgendas)?;
		let index = Agenda::<T>::decode_len(when).unwrap_or(1) as u32 - 1;
		Self::deposit_event(Event::Scheduled { when, index });

		Ok((when, index))
	}

	fn do_cancel(
		origin: Option<T::PalletsOrigin>,
		(when, index): TaskAddress<T::BlockNumber>,
	) -> Result<(), DispatchError> {
		let mut agenda = Agenda::<T>::try_get(when).map_err(|_| Error::<T>::NotFound)?;
		let schedule = agenda.get(index as usize).ok_or(Error::<T>::NotFound)?.clone();
		let decoded_origin = schedule.origin.clone().try_into_inner().expect("TODO");

		if let Some(ref o) = origin {
			if matches!(
				T::OriginPrivilegeCmp::cmp_privilege(o, &decoded_origin,),
				Some(Ordering::Less) | None
			) {
				return Err(BadOrigin.into())
			}
		}
		agenda.remove(index as usize);

		if agenda.is_empty() {
			Agenda::<T>::remove(when);
		} else {
			Agenda::<T>::insert(when, agenda);
		}

		schedule.call.into_inner().ensure_unrequested::<T::PreimageProvider>();
		if let Some(id) = schedule.maybe_id {
			Lookup::<T>::remove(id);
		}
		Self::deposit_event(Event::Canceled { when, index });
		Ok(())
	}

	fn do_reschedule(
		(when, index): TaskAddress<T::BlockNumber>,
		new_time: DispatchTime<T::BlockNumber>,
	) -> Result<TaskAddress<T::BlockNumber>, DispatchError> {
		let new_time = Self::resolve_time(new_time)?;

		if new_time == when {
			return Err(Error::<T>::RescheduleNoChange.into())
		}

		Agenda::<T>::try_mutate(when, |agenda| -> DispatchResult {
			let task = agenda.get(index as usize).ok_or(Error::<T>::NotFound)?.clone();
			agenda.remove(index as usize);
			Agenda::<T>::try_append(new_time, task).map_err(|_| Error::<T>::TooManyAgendas.into())
		})?;

		let new_index = Agenda::<T>::decode_len(new_time).unwrap_or(1) as u32 - 1;
		Self::deposit_event(Event::Canceled { when, index });
		Self::deposit_event(Event::Scheduled { when: new_time, index: new_index });

		Ok((new_time, new_index))
	}

	fn do_schedule_named(
		id: ScheduleIdOf<T>,
		when: DispatchTime<T::BlockNumber>,
		maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
		priority: schedule::Priority,
		origin: T::PalletsOrigin,
		call: CallOrHashOf<T>,
	) -> Result<TaskAddress<T::BlockNumber>, DispatchError> {
		// ensure id it is unique
		if Lookup::<T>::contains_key(&id) {
			return Err(Error::<T>::FailedToSchedule.into())
		}

		let when = Self::resolve_time(when)?;

		call.ensure_requested::<T::PreimageProvider>();
		let call = EncodedCallOrHashOf::<T>::new(call)?;

		// sanitize maybe_periodic
		let maybe_periodic = maybe_periodic
			.filter(|p| p.1 > 1 && !p.0.is_zero())
			// Remove one from the number of repetitions since we will schedule one now.
			.map(|(p, c)| (p, c - 1));

		let s = Scheduled {
			maybe_id: Some(id.clone()),
			priority,
			call,
			maybe_periodic,
			origin: BoundedCodecWrapper::try_from(origin)
				.map_err(|_| Error::<T>::PalletsOriginTooLong)?,
			_phantom: Default::default(),
		};
		Agenda::<T>::try_append(when, s).map_err(|_| Error::<T>::TooManyAgendas)?;
		let index = Agenda::<T>::decode_len(when).unwrap_or(1) as u32 - 1;
		let address = (when, index);
		Lookup::<T>::insert(&id, &address);
		Self::deposit_event(Event::Scheduled { when, index });

		Ok(address)
	}

	fn do_cancel_named(origin: Option<T::PalletsOrigin>, id: ScheduleIdOf<T>) -> DispatchResult {
		Lookup::<T>::try_mutate_exists(id, |lookup| -> DispatchResult {
			if let Some((when, index)) = lookup.take() {
				Self::do_cancel(origin, (when, index))
			} else {
				return Err(Error::<T>::NotFound.into())
			}
		})
	}

	fn do_reschedule_named(
		id: ScheduleIdOf<T>,
		new_time: DispatchTime<T::BlockNumber>,
	) -> Result<TaskAddress<T::BlockNumber>, DispatchError> {
		let id: ScheduleIdOf<T> =
			id.clone().try_into().map_err(|_| Error::<T>::ScheduleIdTooLong)?;
		let new_time = Self::resolve_time(new_time)?;

		Lookup::<T>::try_mutate_exists(
			id,
			|lookup| -> Result<TaskAddress<T::BlockNumber>, DispatchError> {
				let (when, index) = lookup.ok_or(Error::<T>::NotFound)?;

				if new_time == when {
					return Err(Error::<T>::RescheduleNoChange.into())
				}

				Agenda::<T>::try_mutate(when, |agenda| -> DispatchResult {
					let task = agenda.get(index as usize).ok_or(Error::<T>::NotFound)?.clone();
					agenda.remove(index as usize);
					Agenda::<T>::try_append(new_time, task)
						.map_err(|_| Error::<T>::TooManyAgendas.into())
				})?;

				let new_index = Agenda::<T>::decode_len(new_time).unwrap_or(1) as u32 - 1;
				Self::deposit_event(Event::Canceled { when, index });
				Self::deposit_event(Event::Scheduled { when: new_time, index: new_index });

				*lookup = Some((new_time, new_index));

				Ok((new_time, new_index))
			},
		)
	}
}

impl<T: Config> schedule::v2::Anon<T::BlockNumber, <T as Config>::Call, T::PalletsOrigin>
	for Pallet<T>
{
	type Address = TaskAddress<T::BlockNumber>;
	type Hash = T::Hash;

	fn schedule(
		when: DispatchTime<T::BlockNumber>,
		maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
		priority: schedule::Priority,
		origin: T::PalletsOrigin,
		call: CallOrHashOf<T>,
	) -> Result<Self::Address, DispatchError> {
		Self::do_schedule(when, maybe_periodic, priority, origin, call)
	}

	fn cancel((when, index): Self::Address) -> Result<(), ()> {
		Self::do_cancel(None, (when, index)).map_err(|_| ())
	}

	fn reschedule(
		address: Self::Address,
		when: DispatchTime<T::BlockNumber>,
	) -> Result<Self::Address, DispatchError> {
		Self::do_reschedule(address, when)
	}

	fn next_dispatch_time((when, index): Self::Address) -> Result<T::BlockNumber, ()> {
		Agenda::<T>::get(when).get(index as usize).ok_or(()).map(|_| when)
	}
}

impl<T: Config> schedule::v2::Named<T::BlockNumber, <T as Config>::Call, T::PalletsOrigin>
	for Pallet<T>
{
	type Address = TaskAddress<T::BlockNumber>;
	type Hash = T::Hash;

	fn schedule_named(
		id: Vec<u8>,
		when: DispatchTime<T::BlockNumber>,
		maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
		priority: schedule::Priority,
		origin: T::PalletsOrigin,
		call: CallOrHashOf<T>,
	) -> Result<Self::Address, ()> {
		let id: ScheduleIdOf<T> = id.clone().try_into().map_err(|_| ())?;

		Self::do_schedule_named(id, when, maybe_periodic, priority, origin, call).map_err(|_| ())
	}

	fn cancel_named(id: Vec<u8>) -> Result<(), ()> {
		let id: ScheduleIdOf<T> = id.clone().try_into().map_err(|_| ())?;

		Self::do_cancel_named(None, id).map_err(|_| ())
	}

	fn reschedule_named(
		id: Vec<u8>,
		when: DispatchTime<T::BlockNumber>,
	) -> Result<Self::Address, DispatchError> {
		let id: ScheduleIdOf<T> =
			id.clone().try_into().map_err(|_| Error::<T>::ScheduleIdTooLong)?;

		Self::do_reschedule_named(id, when)
	}

	fn next_dispatch_time(id: Vec<u8>) -> Result<T::BlockNumber, ()> {
		let id: ScheduleIdOf<T> = id.clone().try_into().map_err(|_| ())?;

		Lookup::<T>::get(id)
			.and_then(|(when, index)| Agenda::<T>::get(when).get(index as usize).map(|_| when))
			.ok_or(())
	}
}
