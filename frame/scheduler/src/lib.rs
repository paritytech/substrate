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

use codec::{Codec, Decode, Encode, MaxEncodedLen};
use frame_support::{
	dispatch::{DispatchError, DispatchResult, Dispatchable, Parameter},
	ensure,
	traits::{
		schedule::{self, DispatchTime, MaybeHashed},
		Bounded, EnsureOrigin, Get, Hash as PreimageHash, IsType, OriginTrait, PalletInfoAccess,
		PrivilegeCmp, QueryPreimage, StorageVersion, StorePreimage,
	},
	weights::{GetDispatchInfo, Weight},
};
use frame_system::{self as system, ensure_signed};
pub use pallet::*;
use scale_info::TypeInfo;
use sp_io::hashing::blake2_256;
use sp_runtime::{
	traits::{BadOrigin, One, Saturating, Zero},
	BoundedVec, RuntimeDebug,
};
use sp_std::{borrow::Borrow, cmp::Ordering, marker::PhantomData, prelude::*};
pub use weights::WeightInfo;

/// Just a simple index for naming period tasks.
pub type PeriodicIndex = u32;
/// The location of a scheduled task that can be used to remove it.
pub type TaskAddress<BlockNumber> = (BlockNumber, u32);

pub type CallOrHashOf<T> = MaybeHashed<<T as Config>::Call, <T as frame_system::Config>::Hash>;

#[cfg_attr(any(feature = "std", test), derive(PartialEq, Eq))]
#[derive(Clone, RuntimeDebug, Encode, Decode)]
struct ScheduledV1<Call, BlockNumber> {
	maybe_id: Option<Vec<u8>>,
	priority: schedule::Priority,
	call: Call,
	maybe_periodic: Option<schedule::Period<BlockNumber>>,
}

/// Information regarding an item to be executed in the future.
#[cfg_attr(any(feature = "std", test), derive(PartialEq, Eq))]
#[derive(Clone, RuntimeDebug, Encode, Decode, MaxEncodedLen, TypeInfo)]
pub struct Scheduled<Call, BlockNumber, PalletsOrigin, AccountId> {
	/// The unique identity for this task, if there is one.
	maybe_id: Option<[u8; 32]>,
	/// This task's priority.
	priority: schedule::Priority,
	/// The call to be dispatched.
	call: Call,
	/// If the call is periodic, then this points to the information concerning that.
	maybe_periodic: Option<schedule::Period<BlockNumber>>,
	/// The origin with which to dispatch the call.
	origin: PalletsOrigin,
	_phantom: PhantomData<AccountId>,
}

use crate::{Scheduled as ScheduledV3, Scheduled as ScheduledV2};

pub type ScheduledV2Of<T> = ScheduledV2<
	<T as Config>::Call,
	<T as frame_system::Config>::BlockNumber,
	<T as Config>::PalletsOrigin,
	<T as frame_system::Config>::AccountId,
>;

pub type ScheduledV3Of<T> = ScheduledV3<
	CallOrHashOf<T>,
	<T as frame_system::Config>::BlockNumber,
	<T as Config>::PalletsOrigin,
	<T as frame_system::Config>::AccountId,
>;

pub type ScheduledOf<T> = Scheduled<
	Bounded<<T as Config>::Call>,
	<T as frame_system::Config>::BlockNumber,
	<T as Config>::PalletsOrigin,
	<T as frame_system::Config>::AccountId,
>;

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
		dispatch::PostDispatchInfo, pallet_prelude::*, storage_alias, traits::schedule::LookupError,
	};
	use frame_system::pallet_prelude::*;

	/// The current storage version.
	const STORAGE_VERSION: StorageVersion = StorageVersion::new(3);

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::storage_version(STORAGE_VERSION)]
	#[pallet::without_storage_info]
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

		/// The maximum number of scheduled calls in the queue for a single block.
		/// Not strictly enforced, but used for weight estimation.
		#[pallet::constant]
		type MaxScheduledPerBlock: Get<u32>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// The preimage provider with which we look up call hashes to get the call.
		type Preimages: QueryPreimage + StorePreimage;
	}

	#[pallet::storage]
	pub type IncompleteSince<T: Config> = StorageValue<_, T::BlockNumber>;

	/// Items to be executed, indexed by the block number that they should be executed on.
	#[pallet::storage]
	pub type Agenda<T: Config> = StorageMap<
		_,
		Twox64Concat,
		T::BlockNumber,
		BoundedVec<Option<ScheduledOf<T>>, T::MaxScheduledPerBlock>,
		ValueQuery,
	>;

	/// Lookup from a name to the block number and index of the task.
	///
	/// For v3 -> v4 the previously unbounded identities are Blake2-256 hashed to form the v4
	/// identities.
	#[pallet::storage]
	pub(crate) type Lookup<T: Config> =
		StorageMap<_, Twox64Concat, TaskName, TaskAddress<T::BlockNumber>>;

	#[storage_alias]
	pub(crate) type LookupV1<T: Config> = StorageMap<
		Pallet<T>,
		Twox64Concat,
		Vec<u8>,
		TaskAddress<<T as frame_system::Config>::BlockNumber>,
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
			id: Option<[u8; 32]>,
			result: DispatchResult,
		},
		/// The call for the provided hash was not found so the task has been aborted.
		CallLookupFailed {
			task: TaskAddress<T::BlockNumber>,
			id: Option<[u8; 32]>,
			error: LookupError,
		},
		/// The given task was unable to be renewed since the agenda is full at that block.
		PeriodicFailed { task: TaskAddress<T::BlockNumber>, id: Option<[u8; 32]> },
		/// The given task was unable to be renewed since the agenda is full at that block.
		PermanentlyOverweight { task: TaskAddress<T::BlockNumber>, id: Option<[u8; 32]> },
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
		/// Attempt to use a non-named function on a named task.
		Named,
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		/// Execute the scheduled calls
		fn on_initialize(now: T::BlockNumber) -> Weight {
			let mut total_weight: Weight = 0;
			let limit = T::MaximumWeight::get();

			let mut incomplete_since = now + One::one();
			let mut when = IncompleteSince::<T>::take().unwrap_or(now);
			let mut executed = 0;

			while when <= now &&
				total_weight.saturating_add(T::WeightInfo::on_initialize(0)) < limit
			{
				total_weight.saturating_accrue(T::WeightInfo::on_initialize(0));

				let mut agenda = Agenda::<T>::take(when);
				let mut ordered = agenda
					.iter()
					.enumerate()
					.filter_map(|(index, maybe_item)| {
						maybe_item.as_ref().map(|item| (index as u32, item.priority))
					})
					.collect::<Vec<_>>();
				ordered.sort_by_key(|k| k.1);

				let mut skipped = 0;
				let mut unavailable = 0;
				for (order, (agenda_index, _priority)) in ordered.into_iter().enumerate() {
					let mut task = match agenda[agenda_index as usize].take() {
						Some(t) => t,
						None => continue,
					};

					let named = if let Some(ref id) = task.maybe_id {
						Lookup::<T>::remove(id);
						true
					} else {
						false
					};

					if task.call.lookup_needed() {
						let _len = task.call.len();
						// TODO: introduce a new weight checkpoint here which will be based on len
						// T::WeightInfo::decode_item(periodic, named, Some(call));
					}

					let call = match T::Preimages::peek(&task.call) {
						Ok(call) => call,
						Err(_) => {
							// Preimage not available.
							total_weight.saturating_accrue(T::WeightInfo::item(false, named, None));
							unavailable += 1;
							continue
						},
					};

					let periodic = task.maybe_periodic.is_some();
					let call_weight = call.get_dispatch_info().weight;
					// TODO: we no longer need the resolved argument - the call is guaranteed here
					// by now.
					let mut item_weight = T::WeightInfo::item(periodic, named, Some(false));
					let origin = <<T as Config>::Origin as From<T::PalletsOrigin>>::from(
						task.origin.clone(),
					)
					.into();
					if ensure_signed(origin).is_ok() {
						// Weights of Signed dispatches expect their signing account to be
						// whitelisted.
						item_weight.saturating_accrue(T::DbWeight::get().reads_writes(1, 1));
					}

					// We allow a scheduled call if any is true:
					// - It's priority is `HARD_DEADLINE`
					// - It does not push the weight past the limit.
					// - It is the first item in the schedule
					let hard_deadline = task.priority <= schedule::HARD_DEADLINE;
					let test_weight =
						total_weight.saturating_add(call_weight).saturating_add(item_weight);
					if !hard_deadline && order > 0 && test_weight > limit {
						// Cannot be scheduled this block...
						total_weight.saturating_accrue(T::WeightInfo::item(false, named, None));
						if executed > 0 {
							// ...postpone until next
							agenda[agenda_index as usize] = Some(task);
							skipped += 1;
						} else {
							// ...will never be executable as this is the first. discard.
							Self::deposit_event(Event::PermanentlyOverweight {
								task: (when, agenda_index),
								id: task.maybe_id.clone(),
							});
						}
						continue
					}

					executed += 1;
					let dispatch_origin = task.origin.clone().into();
					let (maybe_actual_call_weight, result) = match call.dispatch(dispatch_origin) {
						Ok(post_info) => (post_info.actual_weight, Ok(())),
						Err(error_and_info) =>
							(error_and_info.post_info.actual_weight, Err(error_and_info.error)),
					};
					let actual_call_weight = maybe_actual_call_weight.unwrap_or(call_weight);
					total_weight.saturating_accrue(item_weight);
					total_weight.saturating_accrue(actual_call_weight);

					Self::deposit_event(Event::Dispatched {
						task: (when, agenda_index),
						id: task.maybe_id.clone(),
						result,
					});

					if let &Some((period, count)) = &task.maybe_periodic {
						if count > 1 {
							task.maybe_periodic = Some((period, count - 1));
						} else {
							task.maybe_periodic = None;
						}
						let wake = now + period;
						// If scheduled is named, place its information in `Lookup`
						match Self::place_task(wake, task) {
							Ok(_) => {},
							Err((_, task)) => {
								// TODO: Leave task in storage for it to be rescheduled manually.
								T::Preimages::drop(&task.call);
								Self::deposit_event(Event::PeriodicFailed {
									task: (when, agenda_index),
									id: task.maybe_id.clone(),
								});
							},
						}
					} else {
						T::Preimages::drop(&task.call);
					}
				}
				if skipped > 0 || unavailable > 0 {
					Agenda::<T>::insert(when, agenda);
				}
				if skipped > 0 {
					incomplete_since = incomplete_since.min(when);
				}
				when.saturating_inc();
			}
			incomplete_since = incomplete_since.min(when);
			if incomplete_since <= now {
				IncompleteSince::<T>::put(incomplete_since);
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
			call: Box<<T as Config>::Call>,
		) -> DispatchResult {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Config>::Origin::from(origin);
			Self::do_schedule(
				DispatchTime::At(when),
				maybe_periodic,
				priority,
				origin.caller().clone(),
				T::Preimages::bound(*call)?,
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
			id: TaskName,
			when: T::BlockNumber,
			maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
			priority: schedule::Priority,
			call: Box<<T as Config>::Call>,
		) -> DispatchResult {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Config>::Origin::from(origin);
			Self::do_schedule_named(
				id,
				DispatchTime::At(when),
				maybe_periodic,
				priority,
				origin.caller().clone(),
				T::Preimages::bound(*call)?,
			)?;
			Ok(())
		}

		/// Cancel a named scheduled task.
		#[pallet::weight(<T as Config>::WeightInfo::cancel_named(T::MaxScheduledPerBlock::get()))]
		pub fn cancel_named(origin: OriginFor<T>, id: TaskName) -> DispatchResult {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Config>::Origin::from(origin);
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
			call: Box<<T as Config>::Call>,
		) -> DispatchResult {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Config>::Origin::from(origin);
			Self::do_schedule(
				DispatchTime::After(after),
				maybe_periodic,
				priority,
				origin.caller().clone(),
				T::Preimages::bound(*call)?,
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
			id: TaskName,
			after: T::BlockNumber,
			maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
			priority: schedule::Priority,
			call: Box<<T as Config>::Call>,
		) -> DispatchResult {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Config>::Origin::from(origin);
			Self::do_schedule_named(
				id,
				DispatchTime::After(after),
				maybe_periodic,
				priority,
				origin.caller().clone(),
				T::Preimages::bound(*call)?,
			)?;
			Ok(())
		}
	}
}

impl<T: Config<Hash = PreimageHash>> Pallet<T> {
	/// Migrate storage format from V1 to V4.
	///
	/// Returns the weight consumed by this migration.
	pub fn migrate_v1_to_v4() -> Weight {
		let mut weight = T::DbWeight::get().reads_writes(1, 1);

		Agenda::<T>::translate::<Vec<Option<ScheduledV1<<T as Config>::Call, T::BlockNumber>>>, _>(
			|_, agenda| {
				Some(BoundedVec::truncate_from(
					agenda
						.into_iter()
						.map(|schedule| {
							weight.saturating_accrue(T::DbWeight::get().reads_writes(1, 1));

							schedule.and_then(|schedule| {
								if let Some(id) = schedule.maybe_id.as_ref() {
									let name = blake2_256(id);
									if let Some(item) = LookupV1::<T>::take(id) {
										Lookup::<T>::insert(name, item);
									}
									weight.saturating_accrue(T::DbWeight::get().reads_writes(2, 2));
								}

								let call = T::Preimages::bound(schedule.call).ok()?;

								if call.lookup_needed() {
									weight.saturating_accrue(T::DbWeight::get().reads_writes(0, 1));
								}

								Some(Scheduled {
									maybe_id: schedule.maybe_id.map(|x| blake2_256(&x[..])),
									priority: schedule.priority,
									call,
									maybe_periodic: schedule.maybe_periodic,
									origin: system::RawOrigin::Root.into(),
									_phantom: Default::default(),
								})
							})
						})
						.collect::<Vec<_>>(),
				))
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

	/// Migrate storage format from V2 to V4.
	///
	/// Returns the weight consumed by this migration.
	pub fn migrate_v2_to_v4() -> Weight {
		let mut weight = T::DbWeight::get().reads_writes(1, 1);

		Agenda::<T>::translate::<Vec<Option<ScheduledV2Of<T>>>, _>(|_, agenda| {
			Some(BoundedVec::truncate_from(
				agenda
					.into_iter()
					.map(|schedule| {
						weight.saturating_accrue(T::DbWeight::get().reads_writes(1, 1));
						schedule.and_then(|schedule| {
							if let Some(id) = schedule.maybe_id.as_ref() {
								let name = blake2_256(id);
								if let Some(item) = Lookup::<T>::take(id) {
									Lookup::<T>::insert(name, item);
								}
								weight.saturating_accrue(T::DbWeight::get().reads_writes(2, 2));
							}

							let call = T::Preimages::bound(schedule.call).ok()?;
							if call.lookup_needed() {
								weight.saturating_accrue(T::DbWeight::get().reads_writes(0, 1));
							}

							Some(Scheduled {
								maybe_id: schedule.maybe_id.map(|x| blake2_256(&x[..])),
								priority: schedule.priority,
								call,
								maybe_periodic: schedule.maybe_periodic,
								origin: schedule.origin,
								_phantom: Default::default(),
							})
						})
					})
					.collect::<Vec<_>>(),
			))
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

	/// Migrate storage format from V3 to V4.
	///
	/// Returns the weight consumed by this migration.
	#[allow(deprecated)]
	pub fn migrate_v3_to_v4() -> Weight {
		let mut weight = T::DbWeight::get().reads_writes(1, 1);

		Agenda::<T>::translate::<Vec<Option<ScheduledV3Of<T>>>, _>(|_, agenda| {
			Some(BoundedVec::truncate_from(
				agenda
					.into_iter()
					.map(|schedule| {
						weight.saturating_accrue(T::DbWeight::get().reads_writes(1, 1));
						schedule.and_then(|schedule| {
							if let Some(id) = schedule.maybe_id.as_ref() {
								let name = blake2_256(id);
								if let Some(item) = Lookup::<T>::take(id) {
									Lookup::<T>::insert(name, item);
								}
								weight.saturating_accrue(T::DbWeight::get().reads_writes(2, 2));
							}

							let call = match schedule.call {
								MaybeHashed::Hash(h) => Bounded::from_legacy_hash(h),
								MaybeHashed::Value(v) => {
									let call = T::Preimages::bound(v).ok()?;
									if call.lookup_needed() {
										weight.saturating_accrue(
											T::DbWeight::get().reads_writes(0, 1),
										);
									}
									call
								},
							};

							Some(Scheduled {
								maybe_id: schedule.maybe_id.map(|x| blake2_256(&x[..])),
								priority: schedule.priority,
								call,
								maybe_periodic: schedule.maybe_periodic,
								origin: schedule.origin,
								_phantom: Default::default(),
							})
						})
					})
					.collect::<Vec<_>>(),
			))
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
		Ok(())
	}

	#[cfg(feature = "try-runtime")]
	pub fn post_migrate_to_v4() -> Result<(), &'static str> {
		use frame_support::dispatch::GetStorageVersion;

		assert!(Self::current_storage_version() == 3);
		for k in Agenda::<T>::iter_keys() {
			let _ = Agenda::<T>::try_get(k).map_err(|()| "Invalid item in Agenda")?;
		}
		Ok(())
	}
}

impl<T: Config> Pallet<T> {
	/// Helper to migrate scheduler when the pallet origin type has changed.
	pub fn migrate_origin<OldOrigin: Into<T::PalletsOrigin> + codec::Decode>() {
		Agenda::<T>::translate::<
			Vec<
				Option<
					Scheduled<
						Bounded<<T as Config>::Call>,
						T::BlockNumber,
						OldOrigin,
						T::AccountId,
					>,
				>,
			>,
			_,
		>(|_, agenda| {
			Some(BoundedVec::truncate_from(
				agenda
					.into_iter()
					.map(|schedule| {
						schedule.map(|schedule| Scheduled {
							maybe_id: schedule.maybe_id,
							priority: schedule.priority,
							call: schedule.call,
							maybe_periodic: schedule.maybe_periodic,
							origin: schedule.origin.into(),
							_phantom: Default::default(),
						})
					})
					.collect::<Vec<_>>(),
			))
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

	fn place_task(
		when: T::BlockNumber,
		what: ScheduledOf<T>,
	) -> Result<TaskAddress<T::BlockNumber>, (DispatchError, ScheduledOf<T>)> {
		let maybe_name = what.maybe_id.clone();
		let index = Self::push_to_agenda(when, what)?;
		let address = (when, index);
		if let Some(name) = maybe_name {
			Lookup::<T>::insert(name, address)
		}
		Self::deposit_event(Event::Scheduled { when: address.0, index: address.1 });
		Ok(address)
	}

	fn push_to_agenda(
		when: T::BlockNumber,
		what: ScheduledOf<T>,
	) -> Result<u32, (DispatchError, ScheduledOf<T>)> {
		let mut agenda = Agenda::<T>::get(when);
		let index = if (agenda.len() as u32) < T::MaxScheduledPerBlock::get() {
			// will always succeed due to the above check.
			let _ = agenda.try_push(Some(what));
			agenda.len() as u32 - 1
		} else {
			if let Some(hole_index) = agenda.iter().position(|i| i.is_none()) {
				agenda[hole_index] = Some(what);
				hole_index as u32
			} else {
				return Err((DispatchError::Exhausted, what))
			}
		};
		Agenda::<T>::insert(when, agenda);
		Ok(index)
	}

	fn do_schedule(
		when: DispatchTime<T::BlockNumber>,
		maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
		priority: schedule::Priority,
		origin: T::PalletsOrigin,
		call: Bounded<<T as Config>::Call>,
	) -> Result<TaskAddress<T::BlockNumber>, DispatchError> {
		let when = Self::resolve_time(when)?;

		// sanitize maybe_periodic
		let maybe_periodic = maybe_periodic
			.filter(|p| p.1 > 1 && !p.0.is_zero())
			// Remove one from the number of repetitions since we will schedule one now.
			.map(|(p, c)| (p, c - 1));
		let task = Scheduled {
			maybe_id: None,
			priority,
			call,
			maybe_periodic,
			origin,
			_phantom: PhantomData,
		};
		Self::place_task(when, task).map_err(|x| x.0)
	}

	fn do_cancel(
		origin: Option<T::PalletsOrigin>,
		(when, index): TaskAddress<T::BlockNumber>,
	) -> Result<(), DispatchError> {
		let scheduled = Agenda::<T>::try_mutate(when, |agenda| {
			agenda.get_mut(index as usize).map_or(
				Ok(None),
				|s| -> Result<Option<Scheduled<_, _, _, _>>, DispatchError> {
					if let (Some(ref o), Some(ref s)) = (origin, s.borrow()) {
						if matches!(
							T::OriginPrivilegeCmp::cmp_privilege(o, &s.origin),
							Some(Ordering::Less) | None
						) {
							return Err(BadOrigin.into())
						}
					};
					Ok(s.take())
				},
			)
		})?;
		if let Some(s) = scheduled {
			T::Preimages::drop(&s.call);
			if let Some(id) = s.maybe_id {
				Lookup::<T>::remove(id);
			}
			Self::deposit_event(Event::Canceled { when, index });
			Ok(())
		} else {
			return Err(Error::<T>::NotFound.into())
		}
	}

	fn do_reschedule(
		(when, index): TaskAddress<T::BlockNumber>,
		new_time: DispatchTime<T::BlockNumber>,
	) -> Result<TaskAddress<T::BlockNumber>, DispatchError> {
		let new_time = Self::resolve_time(new_time)?;

		if new_time == when {
			return Err(Error::<T>::RescheduleNoChange.into())
		}

		let task = Agenda::<T>::try_mutate(when, |agenda| {
			let task = agenda.get_mut(index as usize).ok_or(Error::<T>::NotFound)?;
			ensure!(!matches!(task, Some(Scheduled { maybe_id: Some(_), .. })), Error::<T>::Named);
			task.take().ok_or(Error::<T>::NotFound)
		})?;
		Self::deposit_event(Event::Canceled { when, index });

		Self::place_task(new_time, task).map_err(|x| x.0)
	}

	fn do_schedule_named(
		id: TaskName,
		when: DispatchTime<T::BlockNumber>,
		maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
		priority: schedule::Priority,
		origin: T::PalletsOrigin,
		call: Bounded<<T as Config>::Call>,
	) -> Result<TaskAddress<T::BlockNumber>, DispatchError> {
		// ensure id it is unique
		if Lookup::<T>::contains_key(&id) {
			return Err(Error::<T>::FailedToSchedule.into())
		}

		let when = Self::resolve_time(when)?;

		// sanitize maybe_periodic
		let maybe_periodic = maybe_periodic
			.filter(|p| p.1 > 1 && !p.0.is_zero())
			// Remove one from the number of repetitions since we will schedule one now.
			.map(|(p, c)| (p, c - 1));

		let task = Scheduled {
			maybe_id: Some(id),
			priority,
			call,
			maybe_periodic,
			origin,
			_phantom: Default::default(),
		};
		Self::place_task(when, task).map_err(|x| x.0)
	}

	fn do_cancel_named(origin: Option<T::PalletsOrigin>, id: TaskName) -> DispatchResult {
		Lookup::<T>::try_mutate_exists(id, |lookup| -> DispatchResult {
			if let Some((when, index)) = lookup.take() {
				let i = index as usize;
				Agenda::<T>::try_mutate(when, |agenda| -> DispatchResult {
					if let Some(s) = agenda.get_mut(i) {
						if let (Some(ref o), Some(ref s)) = (origin, s.borrow()) {
							if matches!(
								T::OriginPrivilegeCmp::cmp_privilege(o, &s.origin),
								Some(Ordering::Less) | None
							) {
								return Err(BadOrigin.into())
							}
							T::Preimages::drop(&s.call);
						}
						*s = None;
					}
					Ok(())
				})?;
				Self::deposit_event(Event::Canceled { when, index });
				Ok(())
			} else {
				return Err(Error::<T>::NotFound.into())
			}
		})
	}

	fn do_reschedule_named(
		id: TaskName,
		new_time: DispatchTime<T::BlockNumber>,
	) -> Result<TaskAddress<T::BlockNumber>, DispatchError> {
		let new_time = Self::resolve_time(new_time)?;

		let lookup = Lookup::<T>::get(id);
		let (when, index) = lookup.ok_or(Error::<T>::NotFound)?;

		if new_time == when {
			return Err(Error::<T>::RescheduleNoChange.into())
		}

		let task = Agenda::<T>::try_mutate(when, |agenda| {
			let task = agenda.get_mut(index as usize).ok_or(Error::<T>::NotFound)?;
			task.take().ok_or(Error::<T>::NotFound)
		})?;
		Self::deposit_event(Event::Canceled { when, index });
		Self::place_task(new_time, task).map_err(|x| x.0)
	}
}

impl<T: Config<Hash = PreimageHash>>
	schedule::v2::Anon<T::BlockNumber, <T as Config>::Call, T::PalletsOrigin> for Pallet<T>
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
		let call = call.as_value().ok_or(DispatchError::CannotLookup)?;
		let call = T::Preimages::bound(call)?.transmute();
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

impl<T: Config<Hash = PreimageHash>>
	schedule::v2::Named<T::BlockNumber, <T as Config>::Call, T::PalletsOrigin> for Pallet<T>
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
		let call = call.as_value().ok_or(())?;
		let call = T::Preimages::bound(call).map_err(|_| ())?.transmute();
		let name = blake2_256(&id[..]);
		Self::do_schedule_named(name, when, maybe_periodic, priority, origin, call).map_err(|_| ())
	}

	fn cancel_named(id: Vec<u8>) -> Result<(), ()> {
		let name = blake2_256(&id[..]);
		Self::do_cancel_named(None, name).map_err(|_| ())
	}

	fn reschedule_named(
		id: Vec<u8>,
		when: DispatchTime<T::BlockNumber>,
	) -> Result<Self::Address, DispatchError> {
		let name = blake2_256(&id[..]);
		Self::do_reschedule_named(name, when)
	}

	fn next_dispatch_time(id: Vec<u8>) -> Result<T::BlockNumber, ()> {
		let name = blake2_256(&id[..]);
		Lookup::<T>::get(name)
			.and_then(|(when, index)| Agenda::<T>::get(when).get(index as usize).map(|_| when))
			.ok_or(())
	}
}

impl<T: Config> schedule::v3::Anon<T::BlockNumber, <T as Config>::Call, T::PalletsOrigin>
	for Pallet<T>
{
	type Address = TaskAddress<T::BlockNumber>;

	fn schedule(
		when: DispatchTime<T::BlockNumber>,
		maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
		priority: schedule::Priority,
		origin: T::PalletsOrigin,
		call: Bounded<<T as Config>::Call>,
	) -> Result<Self::Address, DispatchError> {
		Self::do_schedule(when, maybe_periodic, priority, origin, call)
	}

	fn cancel((when, index): Self::Address) -> Result<(), DispatchError> {
		Self::do_cancel(None, (when, index))
	}

	fn reschedule(
		address: Self::Address,
		when: DispatchTime<T::BlockNumber>,
	) -> Result<Self::Address, DispatchError> {
		Self::do_reschedule(address, when)
	}

	fn next_dispatch_time((when, index): Self::Address) -> Result<T::BlockNumber, DispatchError> {
		Agenda::<T>::get(when)
			.get(index as usize)
			.ok_or(DispatchError::Unavailable)
			.map(|_| when)
	}
}

use schedule::v3::TaskName;

impl<T: Config> schedule::v3::Named<T::BlockNumber, <T as Config>::Call, T::PalletsOrigin>
	for Pallet<T>
{
	type Address = TaskAddress<T::BlockNumber>;

	fn schedule_named(
		id: TaskName,
		when: DispatchTime<T::BlockNumber>,
		maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
		priority: schedule::Priority,
		origin: T::PalletsOrigin,
		call: Bounded<<T as Config>::Call>,
	) -> Result<Self::Address, DispatchError> {
		Self::do_schedule_named(id, when, maybe_periodic, priority, origin, call)
	}

	fn cancel_named(id: TaskName) -> Result<(), DispatchError> {
		Self::do_cancel_named(None, id)
	}

	fn reschedule_named(
		id: TaskName,
		when: DispatchTime<T::BlockNumber>,
	) -> Result<Self::Address, DispatchError> {
		Self::do_reschedule_named(id, when)
	}

	fn next_dispatch_time(id: TaskName) -> Result<T::BlockNumber, DispatchError> {
		Lookup::<T>::get(id)
			.and_then(|(when, index)| Agenda::<T>::get(when).get(index as usize).map(|_| when))
			.ok_or(DispatchError::Unavailable)
	}
}
