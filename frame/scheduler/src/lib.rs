// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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
//! A module for scheduling dispatches.
//!
//! - [`scheduler::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Overview
//!
//! This module exposes capabilities for scheduling dispatches to occur at a
//! specified block number or at a specified period. These scheduled dispatches
//! may be named or anonymous and may be canceled.
//!
//! **NOTE:** The scheduled calls will be dispatched with the default filter
//! for the origin: namely `frame_system::Trait::BaseCallFilter` for all origin
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
//! * `schedule` - schedule a dispatch, which may be periodic, to occur at a
//!   specified block and with a specified priority.
//! * `cancel` - cancel a scheduled dispatch, specified by block number and
//!   index.
//! * `schedule_named` - augments the `schedule` interface with an additional
//!   `Vec<u8>` parameter that can be used for identification.
//! * `cancel_named` - the named complement to the cancel function.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

mod benchmarking;

use sp_std::{prelude::*, marker::PhantomData, borrow::Borrow};
use codec::{Encode, Decode, Codec};
use sp_runtime::{RuntimeDebug, traits::{Zero, One, BadOrigin, Saturating}};
use frame_support::{
	decl_module, decl_storage, decl_event, decl_error, IterableStorageMap,
	dispatch::{Dispatchable, DispatchError, DispatchResult, Parameter},
	traits::{Get, schedule::{self, DispatchTime}, OriginTrait, EnsureOrigin, IsType},
	weights::{GetDispatchInfo, Weight},
};
use frame_system::{self as system};

pub trait WeightInfo {
	fn schedule(s: u32, ) -> Weight;
	fn cancel(s: u32, ) -> Weight;
	fn schedule_named(s: u32, ) -> Weight;
	fn cancel_named(s: u32, ) -> Weight;
	fn on_initialize(s: u32, ) -> Weight;
}

impl WeightInfo for () {
	fn schedule(_s: u32, ) -> Weight { 1_000_000_000 }
	fn cancel(_s: u32, ) -> Weight { 1_000_000_000 }
	fn schedule_named(_s: u32, ) -> Weight { 1_000_000_000 }
	fn cancel_named(_s: u32, ) -> Weight { 1_000_000_000 }
	fn on_initialize(_s: u32, ) -> Weight { 1_000_000_000 }
}

/// Our pallet's configuration trait. All our types and constants go in here. If the
/// pallet is dependent on specific other pallets, then their configuration traits
/// should be added to our implied traits list.
///
/// `system::Trait` should always be included in our implied traits.
pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// The aggregated origin which the dispatch will take.
	type Origin: OriginTrait<PalletsOrigin =
		Self::PalletsOrigin> + From<Self::PalletsOrigin> + IsType<<Self as system::Trait>::Origin>;

	/// The caller origin, overarching type of all pallets origins.
	type PalletsOrigin: From<system::RawOrigin<Self::AccountId>> + Codec + Clone + Eq;

	/// The aggregated call type.
	type Call: Parameter + Dispatchable<Origin=<Self as Trait>::Origin> + GetDispatchInfo + From<system::Call<Self>>;

	/// The maximum weight that may be scheduled per block for any dispatchables of less priority
	/// than `schedule::HARD_DEADLINE`.
	type MaximumWeight: Get<Weight>;

	/// Required origin to schedule or cancel calls.
	type ScheduleOrigin: EnsureOrigin<<Self as system::Trait>::Origin>;

	/// Weight information for extrinsics in this pallet.
	type WeightInfo: WeightInfo;
}

/// Just a simple index for naming period tasks.
pub type PeriodicIndex = u32;
/// The location of a scheduled task that can be used to remove it.
pub type TaskAddress<BlockNumber> = (BlockNumber, u32);

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
#[derive(Clone, RuntimeDebug, Encode, Decode)]
pub struct ScheduledV2<Call, BlockNumber, PalletsOrigin, AccountId> {
	/// The unique identity for this task, if there is one.
	maybe_id: Option<Vec<u8>>,
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

/// The current version of Scheduled struct.
pub type Scheduled<Call, BlockNumber, PalletsOrigin, AccountId> = ScheduledV2<Call, BlockNumber, PalletsOrigin, AccountId>;

// A value placed in storage that represents the current version of the Scheduler storage.
// This value is used by the `on_runtime_upgrade` logic to determine whether we run
// storage migration logic.
#[derive(Encode, Decode, Clone, Copy, PartialEq, Eq, RuntimeDebug)]
enum Releases {
	V1,
	V2,
}

impl Default for Releases {
	fn default() -> Self {
		Releases::V1
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as Scheduler {
		/// Items to be executed, indexed by the block number that they should be executed on.
		pub Agenda: map hasher(twox_64_concat) T::BlockNumber
			=> Vec<Option<Scheduled<<T as Trait>::Call, T::BlockNumber, T::PalletsOrigin, T::AccountId>>>;

		/// Lookup from identity to the block number and index of the task.
		Lookup: map hasher(twox_64_concat) Vec<u8> => Option<TaskAddress<T::BlockNumber>>;

		/// Storage version of the pallet.
		///
		/// New networks start with last version.
		StorageVersion build(|_| Releases::V2): Releases;
	}
}

decl_event!(
	pub enum Event<T> where <T as system::Trait>::BlockNumber {
		/// Scheduled some task. [when, index]
		Scheduled(BlockNumber, u32),
		/// Canceled some task. [when, index]
		Canceled(BlockNumber, u32),
		/// Dispatched some task. [task, id, result]
		Dispatched(TaskAddress<BlockNumber>, Option<Vec<u8>>, DispatchResult),
	}
);

decl_error! {
	pub enum Error for Module<T: Trait> {
		/// Failed to schedule a call
		FailedToSchedule,
		/// Cannot find the scheduled call.
		NotFound,
		/// Given target block number is in the past.
		TargetBlockNumberInPast,
	}
}

decl_module! {
	/// Scheduler module declaration.
	pub struct Module<T: Trait> for enum Call where origin: <T as system::Trait>::Origin {
		type Error = Error<T>;
		fn deposit_event() = default;

		/// Anonymously schedule a task.
		///
		/// # <weight>
		/// - S = Number of already scheduled calls
		/// - Base Weight: 22.29 + .126 * S µs
		/// - DB Weight:
		///     - Read: Agenda
		///     - Write: Agenda
		/// - Will use base weight of 25 which should be good for up to 30 scheduled calls
		/// # </weight>
		#[weight = 25_000_000 + T::DbWeight::get().reads_writes(1, 1)]
		fn schedule(origin,
			when: T::BlockNumber,
			maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
			priority: schedule::Priority,
			call: Box<<T as Trait>::Call>,
		) {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Trait>::Origin::from(origin);
			Self::do_schedule(DispatchTime::At(when), maybe_periodic, priority, origin.caller().clone(), *call)?;
		}

		/// Cancel an anonymously scheduled task.
		///
		/// # <weight>
		/// - S = Number of already scheduled calls
		/// - Base Weight: 22.15 + 2.869 * S µs
		/// - DB Weight:
		///     - Read: Agenda
		///     - Write: Agenda, Lookup
		/// - Will use base weight of 100 which should be good for up to 30 scheduled calls
		/// # </weight>
		#[weight = 100_000_000 + T::DbWeight::get().reads_writes(1, 2)]
		fn cancel(origin, when: T::BlockNumber, index: u32) {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Trait>::Origin::from(origin);
			Self::do_cancel(Some(origin.caller().clone()), (when, index))?;
		}

		/// Schedule a named task.
		///
		/// # <weight>
		/// - S = Number of already scheduled calls
		/// - Base Weight: 29.6 + .159 * S µs
		/// - DB Weight:
		///     - Read: Agenda, Lookup
		///     - Write: Agenda, Lookup
		/// - Will use base weight of 35 which should be good for more than 30 scheduled calls
		/// # </weight>
		#[weight = 35_000_000 + T::DbWeight::get().reads_writes(2, 2)]
		fn schedule_named(origin,
			id: Vec<u8>,
			when: T::BlockNumber,
			maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
			priority: schedule::Priority,
			call: Box<<T as Trait>::Call>,
		) {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Trait>::Origin::from(origin);
			Self::do_schedule_named(
				id, DispatchTime::At(when), maybe_periodic, priority, origin.caller().clone(), *call
			)?;
		}

		/// Cancel a named scheduled task.
		///
		/// # <weight>
		/// - S = Number of already scheduled calls
		/// - Base Weight: 24.91 + 2.907 * S µs
		/// - DB Weight:
		///     - Read: Agenda, Lookup
		///     - Write: Agenda, Lookup
		/// - Will use base weight of 100 which should be good for up to 30 scheduled calls
		/// # </weight>
		#[weight = 100_000_000 + T::DbWeight::get().reads_writes(2, 2)]
		fn cancel_named(origin, id: Vec<u8>) {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Trait>::Origin::from(origin);
			Self::do_cancel_named(Some(origin.caller().clone()), id)?;
		}

		/// Anonymously schedule a task after a delay.
		///
		/// # <weight>
		/// Same as [`schedule`].
		/// # </weight>
		#[weight = 25_000_000 + T::DbWeight::get().reads_writes(1, 1)]
		fn schedule_after(origin,
			after: T::BlockNumber,
			maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
			priority: schedule::Priority,
			call: Box<<T as Trait>::Call>,
		) {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Trait>::Origin::from(origin);
			Self::do_schedule(
				DispatchTime::After(after), maybe_periodic, priority, origin.caller().clone(), *call
			)?;
		}

		/// Schedule a named task after a delay.
		///
		/// # <weight>
		/// Same as [`schedule_named`].
		/// # </weight>
		#[weight = 35_000_000 + T::DbWeight::get().reads_writes(2, 2)]
		fn schedule_named_after(origin,
			id: Vec<u8>,
			after: T::BlockNumber,
			maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
			priority: schedule::Priority,
			call: Box<<T as Trait>::Call>,
		) {
			T::ScheduleOrigin::ensure_origin(origin.clone())?;
			let origin = <T as Trait>::Origin::from(origin);
			Self::do_schedule_named(
				id, DispatchTime::After(after), maybe_periodic, priority, origin.caller().clone(), *call
			)?;
		}

		/// Execute the scheduled calls
		///
		/// # <weight>
		/// - S = Number of already scheduled calls
		/// - N = Named scheduled calls
		/// - P = Periodic Calls
		/// - Base Weight: 9.243 + 23.45 * S µs
		/// - DB Weight:
		///     - Read: Agenda + Lookup * N + Agenda(Future) * P
		///     - Write: Agenda + Lookup * N  + Agenda(future) * P
		/// # </weight>
		fn on_initialize(now: T::BlockNumber) -> Weight {
			let limit = T::MaximumWeight::get();
			let mut queued = Agenda::<T>::take(now).into_iter()
				.enumerate()
				.filter_map(|(index, s)| s.map(|inner| (index as u32, inner)))
				.collect::<Vec<_>>();
			queued.sort_by_key(|(_, s)| s.priority);
			let base_weight: Weight = T::DbWeight::get().reads_writes(1, 2) // Agenda + Agenda(next)
				.saturating_add(10_000_000); // Base Weight
			let mut total_weight: Weight = 0;
			queued.into_iter()
				.enumerate()
				.scan(base_weight, |cumulative_weight, (order, (index, s))| {
					*cumulative_weight = cumulative_weight
						.saturating_add(s.call.get_dispatch_info().weight)
						.saturating_add(25_000_000); // Base multiplier

					if s.maybe_id.is_some() {
						// Remove/Modify Lookup
						*cumulative_weight = cumulative_weight.saturating_add(T::DbWeight::get().writes(1));
					}
					if s.maybe_periodic.is_some() {
						// Read/Write Agenda for future block
						*cumulative_weight = cumulative_weight.saturating_add(T::DbWeight::get().reads_writes(1, 1));
					}

					Some((order, index, *cumulative_weight, s))
				})
				.filter_map(|(order, index, cumulative_weight, mut s)| {
					// We allow a scheduled call if any is true:
					// - It's priority is `HARD_DEADLINE`
					// - It does not push the weight past the limit.
					// - It is the first item in the schedule
					if s.priority <= schedule::HARD_DEADLINE || cumulative_weight <= limit || order == 0 {
						let r = s.call.clone().dispatch(s.origin.clone().into());
						let maybe_id = s.maybe_id.clone();
						if let &Some((period, count)) = &s.maybe_periodic {
							if count > 1 {
								s.maybe_periodic = Some((period, count - 1));
							} else {
								s.maybe_periodic = None;
							}
							let next = now + period;
							// If scheduled is named, place it's information in `Lookup`
							if let Some(ref id) = s.maybe_id {
								let next_index = Agenda::<T>::decode_len(now + period).unwrap_or(0);
								Lookup::<T>::insert(id, (next, next_index as u32));
							}
							Agenda::<T>::append(next, Some(s));
						} else {
							if let Some(ref id) = s.maybe_id {
								Lookup::<T>::remove(id);
							}
						}
						Self::deposit_event(RawEvent::Dispatched(
							(now, index),
							maybe_id,
							r.map(|_| ()).map_err(|e| e.error)
						));
						total_weight = cumulative_weight;
						None
					} else {
						Some(Some(s))
					}
				})
				.for_each(|unused| {
					let next = now + One::one();
					Agenda::<T>::append(next, unused);
				});

			total_weight
		}
	}
}

impl<T: Trait> Module<T> {
	/// Migrate storage format from V1 to V2.
	/// Return true if migration is performed.
	pub fn migrate_v1_to_t2() -> bool {
		if StorageVersion::get() == Releases::V1 {
			StorageVersion::put(Releases::V2);

			Agenda::<T>::translate::<
				Vec<Option<ScheduledV1<<T as Trait>::Call, T::BlockNumber>>>, _
			>(|_, agenda| Some(
				agenda
					.into_iter()
					.map(|schedule| schedule.map(|schedule| ScheduledV2 {
						maybe_id: schedule.maybe_id,
						priority: schedule.priority,
						call: schedule.call,
						maybe_periodic: schedule.maybe_periodic,
						origin: system::RawOrigin::Root.into(),
						_phantom: Default::default(),
					}))
					.collect::<Vec<_>>()
			));

			true
		} else {
			false
		}
	}

	fn resolve_time(when: DispatchTime<T::BlockNumber>) -> Result<T::BlockNumber, DispatchError> {
		let now = frame_system::Module::<T>::block_number();

		let when = match when {
			DispatchTime::At(x) => x,
			DispatchTime::After(x) => now.saturating_add(x)
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
		call: <T as Trait>::Call
	) -> Result<TaskAddress<T::BlockNumber>, DispatchError> {
		let when = Self::resolve_time(when)?;

		// sanitize maybe_periodic
		let maybe_periodic = maybe_periodic
			.filter(|p| p.1 > 1 && !p.0.is_zero())
			// Remove one from the number of repetitions since we will schedule one now.
			.map(|(p, c)| (p, c - 1));
		let s = Some(Scheduled {
			maybe_id: None, priority, call, maybe_periodic, origin, _phantom: PhantomData::<T::AccountId>::default(),
		});
		Agenda::<T>::append(when, s);
		let index = Agenda::<T>::decode_len(when).unwrap_or(1) as u32 - 1;
		Self::deposit_event(RawEvent::Scheduled(when, index));

		Ok((when, index))
	}

	fn do_cancel(
		origin: Option<T::PalletsOrigin>,
		(when, index): TaskAddress<T::BlockNumber>
	) -> Result<(), DispatchError> {
		let scheduled = Agenda::<T>::try_mutate(
			when,
			|agenda| {
				agenda.get_mut(index as usize)
					.map_or(Ok(None), |s| -> Result<Option<Scheduled<_, _, _, _>>, DispatchError> {
						if let (Some(ref o), Some(ref s)) = (origin, s.borrow()) {
							if *o != s.origin {
								return Err(BadOrigin.into());
							}
						};
						Ok(s.take())
					})
			},
		)?;
		if let Some(s) = scheduled {
			if let Some(id) = s.maybe_id {
				Lookup::<T>::remove(id);
			}
			Self::deposit_event(RawEvent::Canceled(when, index));
			Ok(())
		} else {
			Err(Error::<T>::NotFound)?
		}
	}

	fn do_reschedule(
		(when, index): TaskAddress<T::BlockNumber>,
		new_time: DispatchTime<T::BlockNumber>,
	) -> Result<TaskAddress<T::BlockNumber>, DispatchError> {
		let new_time = Self::resolve_time(new_time)?;

		Agenda::<T>::try_mutate(when, |agenda| -> DispatchResult {
			let task = agenda.get_mut(index as usize).ok_or(Error::<T>::NotFound)?;
			let task = task.take().ok_or(Error::<T>::NotFound)?;
			Agenda::<T>::append(new_time, Some(task));
			Ok(())
		})?;

		let new_index = Agenda::<T>::decode_len(new_time).unwrap_or(1) as u32 - 1;
		Self::deposit_event(RawEvent::Canceled(when, index));
		Self::deposit_event(RawEvent::Scheduled(new_time, new_index));

		Ok((new_time, new_index))
	}

	fn do_schedule_named(
		id: Vec<u8>,
		when: DispatchTime<T::BlockNumber>,
		maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
		priority: schedule::Priority,
		origin: T::PalletsOrigin,
		call: <T as Trait>::Call,
	) -> Result<TaskAddress<T::BlockNumber>, DispatchError> {
		// ensure id it is unique
		if Lookup::<T>::contains_key(&id) {
			return Err(Error::<T>::FailedToSchedule)?
		}

		let when = Self::resolve_time(when)?;

		// sanitize maybe_periodic
		let maybe_periodic = maybe_periodic
			.filter(|p| p.1 > 1 && !p.0.is_zero())
			// Remove one from the number of repetitions since we will schedule one now.
			.map(|(p, c)| (p, c - 1));

		let s = Scheduled {
			maybe_id: Some(id.clone()), priority, call, maybe_periodic, origin, _phantom: Default::default()
		};
		Agenda::<T>::append(when, Some(s));
		let index = Agenda::<T>::decode_len(when).unwrap_or(1) as u32 - 1;
		let address = (when, index);
		Lookup::<T>::insert(&id, &address);
		Self::deposit_event(RawEvent::Scheduled(when, index));

		Ok(address)
	}

	fn do_cancel_named(origin: Option<T::PalletsOrigin>, id: Vec<u8>) -> DispatchResult {
		Lookup::<T>::try_mutate_exists(id, |lookup| -> DispatchResult {
			if let Some((when, index)) = lookup.take() {
				let i = index as usize;
				Agenda::<T>::try_mutate(when, |agenda| -> DispatchResult {
					if let Some(s) = agenda.get_mut(i) {
						if let (Some(ref o), Some(ref s)) = (origin, s.borrow()) {
							if *o != s.origin {
								return Err(BadOrigin.into());
							}
						}
						*s = None;
					}
					Ok(())
				})?;
				Self::deposit_event(RawEvent::Canceled(when, index));
				Ok(())
			} else {
				Err(Error::<T>::NotFound)?
			}
		})
	}

	fn do_reschedule_named(
		id: Vec<u8>,
		new_time: DispatchTime<T::BlockNumber>,
	) -> Result<TaskAddress<T::BlockNumber>, DispatchError> {
		let new_time = Self::resolve_time(new_time)?;

		Lookup::<T>::try_mutate_exists(id, |lookup| -> Result<TaskAddress<T::BlockNumber>, DispatchError> {
			let (when, index) = lookup.ok_or(Error::<T>::NotFound)?;
			Agenda::<T>::try_mutate(when, |agenda| -> DispatchResult {
				let task = agenda.get_mut(index as usize).ok_or(Error::<T>::NotFound)?;
				let task = task.take().ok_or(Error::<T>::NotFound)?;
				Agenda::<T>::append(new_time, Some(task));

				Ok(())
			})?;

			let new_index = Agenda::<T>::decode_len(new_time).unwrap_or(1) as u32 - 1;
			Self::deposit_event(RawEvent::Canceled(when, index));
			Self::deposit_event(RawEvent::Scheduled(new_time, new_index));

			*lookup = Some((new_time, new_index));

			Ok((new_time, new_index))
		})
	}
}

impl<T: Trait> schedule::Anon<T::BlockNumber, <T as Trait>::Call, T::PalletsOrigin> for Module<T> {
	type Address = TaskAddress<T::BlockNumber>;

	fn schedule(
		when: DispatchTime<T::BlockNumber>,
		maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
		priority: schedule::Priority,
		origin: T::PalletsOrigin,
		call: <T as Trait>::Call
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

impl<T: Trait> schedule::Named<T::BlockNumber, <T as Trait>::Call, T::PalletsOrigin> for Module<T> {
	type Address = TaskAddress<T::BlockNumber>;

	fn schedule_named(
		id: Vec<u8>,
		when: DispatchTime<T::BlockNumber>,
		maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
		priority: schedule::Priority,
		origin: T::PalletsOrigin,
		call: <T as Trait>::Call,
	) -> Result<Self::Address, ()> {
		Self::do_schedule_named(id, when, maybe_periodic, priority, origin, call).map_err(|_| ())
	}

	fn cancel_named(id: Vec<u8>) -> Result<(), ()> {
		Self::do_cancel_named(None, id).map_err(|_| ())
	}

	fn reschedule_named(
		id: Vec<u8>,
		when: DispatchTime<T::BlockNumber>,
	) -> Result<Self::Address, DispatchError> {
		Self::do_reschedule_named(id, when)
	}

	fn next_dispatch_time(id: Vec<u8>) -> Result<T::BlockNumber, ()> {
		Lookup::<T>::get(id).and_then(|(when, index)| Agenda::<T>::get(when).get(index as usize).map(|_| when)).ok_or(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use frame_support::{
		impl_outer_event, impl_outer_origin, impl_outer_dispatch, parameter_types, assert_ok, ord_parameter_types,
		assert_noop, assert_err, Hashable,
		traits::{OnInitialize, OnFinalize, Filter},
		weights::constants::RocksDbWeight,
	};
	use sp_core::H256;
	use sp_runtime::{
		Perbill,
		testing::Header,
		traits::{BlakeTwo256, IdentityLookup},
	};
	use frame_system::{EnsureOneOf, EnsureRoot, EnsureSignedBy};
	use crate as scheduler;

	mod logger {
		use super::*;
		use std::cell::RefCell;

		thread_local! {
			static LOG: RefCell<Vec<(OriginCaller, u32)>> = RefCell::new(Vec::new());
		}
		pub fn log() -> Vec<(OriginCaller, u32)> {
			LOG.with(|log| log.borrow().clone())
		}
		pub trait Trait: system::Trait {
			type Event: From<Event> + Into<<Self as system::Trait>::Event>;
		}
		decl_event! {
			pub enum Event {
				Logged(u32, Weight),
			}
		}
		decl_module! {
			pub struct Module<T: Trait> for enum Call
			where
				origin: <T as system::Trait>::Origin,
				<T as system::Trait>::Origin: OriginTrait<PalletsOrigin = OriginCaller>
			{
				fn deposit_event() = default;

				#[weight = *weight]
				fn log(origin, i: u32, weight: Weight) {
					Self::deposit_event(Event::Logged(i, weight));
					LOG.with(|log| {
						log.borrow_mut().push((origin.caller().clone(), i));
					})
				}

				#[weight = *weight]
				fn log_without_filter(origin, i: u32, weight: Weight) {
					Self::deposit_event(Event::Logged(i, weight));
					LOG.with(|log| {
						log.borrow_mut().push((origin.caller().clone(), i));
					})
				}
			}
		}
	}

	impl_outer_origin! {
		pub enum Origin for Test where system = frame_system {}
	}

	impl_outer_dispatch! {
		pub enum Call for Test where origin: Origin {
			system::System,
			logger::Logger,
		}
	}

	impl_outer_event! {
		pub enum Event for Test {
			system<T>,
			logger,
			scheduler<T>,
		}
	}

	// Scheduler must dispatch with root and no filter, this tests base filter is indeed not used.
	pub struct BaseFilter;
	impl Filter<Call> for BaseFilter {
		fn filter(call: &Call) -> bool {
			!matches!(call, Call::Logger(logger::Call::log(_, _)))
		}
	}

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 2_000_000_000_000;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl system::Trait for Test {
		type BaseCallFilter = BaseFilter;
		type Origin = Origin;
		type Call = Call;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type DbWeight = RocksDbWeight;
		type BlockExecutionWeight = ();
		type ExtrinsicBaseWeight = ();
		type MaximumExtrinsicWeight = MaximumBlockWeight;
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
		type ModuleToIndex = ();
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
	}
	impl logger::Trait for Test {
		type Event = ();
	}
	parameter_types! {
		pub MaximumSchedulerWeight: Weight = Perbill::from_percent(80) * MaximumBlockWeight::get();
	}
	ord_parameter_types! {
		pub const One: u64 = 1;
	}

	impl Trait for Test {
		type Event = ();
		type Origin = Origin;
		type PalletsOrigin = OriginCaller;
		type Call = Call;
		type MaximumWeight = MaximumSchedulerWeight;
		type ScheduleOrigin = EnsureOneOf<u64, EnsureRoot<u64>, EnsureSignedBy<One, u64>>;
		type WeightInfo = ();
	}
	type System = system::Module<Test>;
	type Logger = logger::Module<Test>;
	type Scheduler = Module<Test>;

	pub fn new_test_ext() -> sp_io::TestExternalities {
		let t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		t.into()
	}

	fn run_to_block(n: u64) {
		while System::block_number() < n {
			Scheduler::on_finalize(System::block_number());
			System::set_block_number(System::block_number() + 1);
			Scheduler::on_initialize(System::block_number());
		}
	}

	fn root() -> OriginCaller {
		system::RawOrigin::Root.into()
	}

	#[test]
	fn basic_scheduling_works() {
		new_test_ext().execute_with(|| {
			let call = Call::Logger(logger::Call::log(42, 1000));
			assert!(!<Test as frame_system::Trait>::BaseCallFilter::filter(&call));
			let _ = Scheduler::do_schedule(DispatchTime::At(4), None, 127, root(), call);
			run_to_block(3);
			assert!(logger::log().is_empty());
			run_to_block(4);
			assert_eq!(logger::log(), vec![(root(), 42u32)]);
			run_to_block(100);
			assert_eq!(logger::log(), vec![(root(), 42u32)]);
		});
	}

	#[test]
	fn schedule_after_works() {
		new_test_ext().execute_with(|| {
			run_to_block(2);
			let call = Call::Logger(logger::Call::log(42, 1000));
			assert!(!<Test as frame_system::Trait>::BaseCallFilter::filter(&call));
			let _ = Scheduler::do_schedule(DispatchTime::After(3), None, 127, root(), call);
			run_to_block(4);
			assert!(logger::log().is_empty());
			run_to_block(5);
			assert_eq!(logger::log(), vec![(root(), 42u32)]);
			run_to_block(100);
			assert_eq!(logger::log(), vec![(root(), 42u32)]);
		});
	}

	#[test]
	fn periodic_scheduling_works() {
		new_test_ext().execute_with(|| {
			// at #4, every 3 blocks, 3 times.
			let _ = Scheduler::do_schedule(
				DispatchTime::At(4), Some((3, 3)), 127, root(), Call::Logger(logger::Call::log(42, 1000))
			);
			run_to_block(3);
			assert!(logger::log().is_empty());
			run_to_block(4);
			assert_eq!(logger::log(), vec![(root(), 42u32)]);
			run_to_block(6);
			assert_eq!(logger::log(), vec![(root(), 42u32)]);
			run_to_block(7);
			assert_eq!(logger::log(), vec![(root(), 42u32), (root(), 42u32)]);
			run_to_block(9);
			assert_eq!(logger::log(), vec![(root(), 42u32), (root(), 42u32)]);
			run_to_block(10);
			assert_eq!(logger::log(), vec![(root(), 42u32), (root(), 42u32), (root(), 42u32)]);
			run_to_block(100);
			assert_eq!(logger::log(), vec![(root(), 42u32), (root(), 42u32), (root(), 42u32)]);
		});
	}

	#[test]
	fn reschedule_works() {
		new_test_ext().execute_with(|| {
			let call = Call::Logger(logger::Call::log(42, 1000));
			assert!(!<Test as frame_system::Trait>::BaseCallFilter::filter(&call));
			assert_eq!(Scheduler::do_schedule(DispatchTime::At(4), None, 127, root(), call).unwrap(), (4, 0));

			run_to_block(3);
			assert!(logger::log().is_empty());

			assert_eq!(Scheduler::do_reschedule((4, 0), DispatchTime::At(6)).unwrap(), (6, 0));

			run_to_block(4);
			assert!(logger::log().is_empty());

			run_to_block(6);
			assert_eq!(logger::log(), vec![(root(), 42u32)]);

			run_to_block(100);
			assert_eq!(logger::log(), vec![(root(), 42u32)]);
		});
	}

	#[test]
	fn reschedule_named_works() {
		new_test_ext().execute_with(|| {
			let call = Call::Logger(logger::Call::log(42, 1000));
			assert!(!<Test as frame_system::Trait>::BaseCallFilter::filter(&call));
			assert_eq!(Scheduler::do_schedule_named(
				1u32.encode(), DispatchTime::At(4), None, 127, root(), call
			).unwrap(), (4, 0));

			run_to_block(3);
			assert!(logger::log().is_empty());

			assert_eq!(Scheduler::do_reschedule_named(1u32.encode(), DispatchTime::At(6)).unwrap(), (6, 0));

			run_to_block(4);
			assert!(logger::log().is_empty());

			run_to_block(6);
			assert_eq!(logger::log(), vec![(root(), 42u32)]);

			run_to_block(100);
			assert_eq!(logger::log(), vec![(root(), 42u32)]);
		});
	}

	#[test]
	fn reschedule_named_perodic_works() {
		new_test_ext().execute_with(|| {
			let call = Call::Logger(logger::Call::log(42, 1000));
			assert!(!<Test as frame_system::Trait>::BaseCallFilter::filter(&call));
			assert_eq!(Scheduler::do_schedule_named(
				1u32.encode(), DispatchTime::At(4), Some((3, 3)), 127, root(), call
			).unwrap(), (4, 0));

			run_to_block(3);
			assert!(logger::log().is_empty());

			assert_eq!(Scheduler::do_reschedule_named(1u32.encode(), DispatchTime::At(6)).unwrap(), (6, 0));

			run_to_block(4);
			assert!(logger::log().is_empty());

			run_to_block(6);
			assert_eq!(logger::log(), vec![(root(), 42u32)]);

			assert_eq!(Scheduler::do_reschedule_named(1u32.encode(), DispatchTime::At(10)).unwrap(), (10, 0));

			run_to_block(9);
			assert_eq!(logger::log(), vec![(root(), 42u32)]);

			run_to_block(10);
			assert_eq!(logger::log(), vec![(root(), 42u32), (root(), 42u32)]);

			run_to_block(13);
			assert_eq!(logger::log(), vec![(root(), 42u32), (root(), 42u32), (root(), 42u32)]);

			run_to_block(100);
			assert_eq!(logger::log(), vec![(root(), 42u32), (root(), 42u32), (root(), 42u32)]);
		});
	}

	#[test]
	fn cancel_named_scheduling_works_with_normal_cancel() {
		new_test_ext().execute_with(|| {
			// at #4.
			Scheduler::do_schedule_named(
				1u32.encode(), DispatchTime::At(4), None, 127, root(), Call::Logger(logger::Call::log(69, 1000))
			).unwrap();
			let i = Scheduler::do_schedule(
				DispatchTime::At(4), None, 127, root(), Call::Logger(logger::Call::log(42, 1000))
			).unwrap();
			run_to_block(3);
			assert!(logger::log().is_empty());
			assert_ok!(Scheduler::do_cancel_named(None, 1u32.encode()));
			assert_ok!(Scheduler::do_cancel(None, i));
			run_to_block(100);
			assert!(logger::log().is_empty());
		});
	}

	#[test]
	fn cancel_named_periodic_scheduling_works() {
		new_test_ext().execute_with(|| {
			// at #4, every 3 blocks, 3 times.
			Scheduler::do_schedule_named(
				1u32.encode(),
				DispatchTime::At(4),
				Some((3, 3)),
				127,
				root(),
				Call::Logger(logger::Call::log(42, 1000))
			).unwrap();
			// same id results in error.
			assert!(Scheduler::do_schedule_named(
				1u32.encode(),
				DispatchTime::At(4),
				None,
				127,
				root(),
				Call::Logger(logger::Call::log(69, 1000))
			).is_err());
			// different id is ok.
			Scheduler::do_schedule_named(
				2u32.encode(), DispatchTime::At(8), None, 127, root(), Call::Logger(logger::Call::log(69, 1000))
			).unwrap();
			run_to_block(3);
			assert!(logger::log().is_empty());
			run_to_block(4);
			assert_eq!(logger::log(), vec![(root(), 42u32)]);
			run_to_block(6);
			assert_ok!(Scheduler::do_cancel_named(None, 1u32.encode()));
			run_to_block(100);
			assert_eq!(logger::log(), vec![(root(), 42u32), (root(), 69u32)]);
		});
	}

	#[test]
	fn scheduler_respects_weight_limits() {
		new_test_ext().execute_with(|| {
			let _ = Scheduler::do_schedule(
				DispatchTime::At(4),
				None,
				127,
				root(),
				Call::Logger(logger::Call::log(42, MaximumSchedulerWeight::get() / 2))
			);
			let _ = Scheduler::do_schedule(
				DispatchTime::At(4),
				None,
				127,
				root(), Call::Logger(logger::Call::log(69, MaximumSchedulerWeight::get() / 2))
			);
			// 69 and 42 do not fit together
			run_to_block(4);
			assert_eq!(logger::log(), vec![(root(), 42u32)]);
			run_to_block(5);
			assert_eq!(logger::log(), vec![(root(), 42u32), (root(), 69u32)]);
		});
	}

	#[test]
	fn scheduler_respects_hard_deadlines_more() {
		new_test_ext().execute_with(|| {
			let _ = Scheduler::do_schedule(
				DispatchTime::At(4),
				None,
				0,
				root(),
				Call::Logger(logger::Call::log(42, MaximumSchedulerWeight::get() / 2))
			);
			let _ = Scheduler::do_schedule(
				DispatchTime::At(4),
				None,
				0,
				root(),
				Call::Logger(logger::Call::log(69, MaximumSchedulerWeight::get() / 2))
			);
			// With base weights, 69 and 42 should not fit together, but do because of hard deadlines
			run_to_block(4);
			assert_eq!(logger::log(), vec![(root(), 42u32), (root(), 69u32)]);
		});
	}

	#[test]
	fn scheduler_respects_priority_ordering() {
		new_test_ext().execute_with(|| {
			let _ = Scheduler::do_schedule(
				DispatchTime::At(4),
				None,
				1,
				root(),
				Call::Logger(logger::Call::log(42, MaximumSchedulerWeight::get() / 2))
			);
			let _ = Scheduler::do_schedule(
				DispatchTime::At(4),
				None,
				0,
				root(),
				Call::Logger(logger::Call::log(69, MaximumSchedulerWeight::get() / 2))
			);
			run_to_block(4);
			assert_eq!(logger::log(), vec![(root(), 69u32), (root(), 42u32)]);
		});
	}

	#[test]
	fn scheduler_respects_priority_ordering_with_soft_deadlines() {
		new_test_ext().execute_with(|| {
			let _ = Scheduler::do_schedule(
				DispatchTime::At(4),
				None,
				255,
				root(), Call::Logger(logger::Call::log(42, MaximumSchedulerWeight::get() / 3))
			);
			let _ = Scheduler::do_schedule(
				DispatchTime::At(4),
				None,
				127,
				root(), Call::Logger(logger::Call::log(69, MaximumSchedulerWeight::get() / 2))
			);
			let _ = Scheduler::do_schedule(
				DispatchTime::At(4),
				None,
				126,
				root(), Call::Logger(logger::Call::log(2600, MaximumSchedulerWeight::get() / 2))
			);

			// 2600 does not fit with 69 or 42, but has higher priority, so will go through
			run_to_block(4);
			assert_eq!(logger::log(), vec![(root(), 2600u32)]);
			// 69 and 42 fit together
			run_to_block(5);
			assert_eq!(logger::log(), vec![(root(), 2600u32), (root(), 69u32), (root(), 42u32)]);
		});
	}

	#[test]
	fn on_initialize_weight_is_correct() {
		new_test_ext().execute_with(|| {
			let base_weight: Weight = <Test as frame_system::Trait>::DbWeight::get().reads_writes(1, 2) + 10_000_000;
			let base_multiplier = 25_000_000;
			let named_multiplier = <Test as frame_system::Trait>::DbWeight::get().writes(1);
			let periodic_multiplier = <Test as frame_system::Trait>::DbWeight::get().reads_writes(1, 1);

			// Named
			assert_ok!(
				Scheduler::do_schedule_named(
					1u32.encode(), DispatchTime::At(1), None, 255, root(),
					Call::Logger(logger::Call::log(3, MaximumSchedulerWeight::get() / 3))
				)
			);
			// Anon Periodic
			let _ = Scheduler::do_schedule(
				DispatchTime::At(1),
				Some((1000, 3)),
				128,
				root(),
				Call::Logger(logger::Call::log(42, MaximumSchedulerWeight::get() / 3))
			);
			// Anon
			let _ = Scheduler::do_schedule(
				DispatchTime::At(1),
				None,
				127,
				root(),
				Call::Logger(logger::Call::log(69, MaximumSchedulerWeight::get() / 2))
			);
			// Named Periodic
			assert_ok!(Scheduler::do_schedule_named(
				2u32.encode(), DispatchTime::At(1), Some((1000, 3)), 126, root(),
				Call::Logger(logger::Call::log(2600, MaximumSchedulerWeight::get() / 2)))
			);

			// Will include the named periodic only
			let actual_weight = Scheduler::on_initialize(1);
			let call_weight = MaximumSchedulerWeight::get() / 2;
			assert_eq!(
				actual_weight, call_weight + base_weight + base_multiplier + named_multiplier + periodic_multiplier
			);
			assert_eq!(logger::log(), vec![(root(), 2600u32)]);

			// Will include anon and anon periodic
			let actual_weight = Scheduler::on_initialize(2);
			let call_weight = MaximumSchedulerWeight::get() / 2 + MaximumSchedulerWeight::get() / 3;
			assert_eq!(actual_weight, call_weight + base_weight + base_multiplier * 2 + periodic_multiplier);
			assert_eq!(logger::log(), vec![(root(), 2600u32), (root(), 69u32), (root(), 42u32)]);

			// Will include named only
			let actual_weight = Scheduler::on_initialize(3);
			let call_weight = MaximumSchedulerWeight::get() / 3;
			assert_eq!(actual_weight, call_weight + base_weight + base_multiplier + named_multiplier);
			assert_eq!(logger::log(), vec![(root(), 2600u32), (root(), 69u32), (root(), 42u32), (root(), 3u32)]);

			// Will contain none
			let actual_weight = Scheduler::on_initialize(4);
			assert_eq!(actual_weight, 0);
		});
	}

	#[test]
	fn root_calls_works() {
		new_test_ext().execute_with(|| {
			let call = Box::new(Call::Logger(logger::Call::log(69, 1000)));
			let call2 = Box::new(Call::Logger(logger::Call::log(42, 1000)));
			assert_ok!(Scheduler::schedule_named(Origin::root(), 1u32.encode(), 4, None, 127, call));
			assert_ok!(Scheduler::schedule(Origin::root(), 4, None, 127, call2));
			run_to_block(3);
			// Scheduled calls are in the agenda.
			assert_eq!(Agenda::<Test>::get(4).len(), 2);
			assert!(logger::log().is_empty());
			assert_ok!(Scheduler::cancel_named(Origin::root(), 1u32.encode()));
			assert_ok!(Scheduler::cancel(Origin::root(), 4, 1));
			// Scheduled calls are made NONE, so should not effect state
			run_to_block(100);
			assert!(logger::log().is_empty());
		});
	}

	#[test]
	fn fails_to_schedule_task_in_the_past() {
		new_test_ext().execute_with(|| {
			run_to_block(3);

			let call = Box::new(Call::Logger(logger::Call::log(69, 1000)));
			let call2 = Box::new(Call::Logger(logger::Call::log(42, 1000)));

			assert_err!(
				Scheduler::schedule_named(Origin::root(), 1u32.encode(), 2, None, 127, call),
				Error::<Test>::TargetBlockNumberInPast,
			);

			assert_err!(
				Scheduler::schedule(Origin::root(), 2, None, 127, call2.clone()),
				Error::<Test>::TargetBlockNumberInPast,
			);

			assert_err!(
				Scheduler::schedule(Origin::root(), 3, None, 127, call2),
				Error::<Test>::TargetBlockNumberInPast,
			);
		});
	}

	#[test]
	fn should_use_orign() {
		new_test_ext().execute_with(|| {
			let call = Box::new(Call::Logger(logger::Call::log(69, 1000)));
			let call2 = Box::new(Call::Logger(logger::Call::log(42, 1000)));
			assert_ok!(
				Scheduler::schedule_named(system::RawOrigin::Signed(1).into(), 1u32.encode(), 4, None, 127, call)
			);
			assert_ok!(Scheduler::schedule(system::RawOrigin::Signed(1).into(), 4, None, 127, call2));
			run_to_block(3);
			// Scheduled calls are in the agenda.
			assert_eq!(Agenda::<Test>::get(4).len(), 2);
			assert!(logger::log().is_empty());
			assert_ok!(Scheduler::cancel_named(system::RawOrigin::Signed(1).into(), 1u32.encode()));
			assert_ok!(Scheduler::cancel(system::RawOrigin::Signed(1).into(), 4, 1));
			// Scheduled calls are made NONE, so should not effect state
			run_to_block(100);
			assert!(logger::log().is_empty());
		});
	}

	#[test]
	fn should_check_orign() {
		new_test_ext().execute_with(|| {
			let call = Box::new(Call::Logger(logger::Call::log(69, 1000)));
			let call2 = Box::new(Call::Logger(logger::Call::log(42, 1000)));
			assert_noop!(
				Scheduler::schedule_named(system::RawOrigin::Signed(2).into(), 1u32.encode(), 4, None, 127, call),
				BadOrigin
			);
			assert_noop!(Scheduler::schedule(system::RawOrigin::Signed(2).into(), 4, None, 127, call2), BadOrigin);
		});
	}

	#[test]
	fn should_check_orign_for_cancel() {
		new_test_ext().execute_with(|| {
			let call = Box::new(Call::Logger(logger::Call::log_without_filter(69, 1000)));
			let call2 = Box::new(Call::Logger(logger::Call::log_without_filter(42, 1000)));
			assert_ok!(
				Scheduler::schedule_named(system::RawOrigin::Signed(1).into(), 1u32.encode(), 4, None, 127, call)
			);
			assert_ok!(Scheduler::schedule(system::RawOrigin::Signed(1).into(), 4, None, 127, call2));
			run_to_block(3);
			// Scheduled calls are in the agenda.
			assert_eq!(Agenda::<Test>::get(4).len(), 2);
			assert!(logger::log().is_empty());
			assert_noop!(Scheduler::cancel_named(system::RawOrigin::Signed(2).into(), 1u32.encode()), BadOrigin);
			assert_noop!(Scheduler::cancel(system::RawOrigin::Signed(2).into(), 4, 1), BadOrigin);
			assert_noop!(Scheduler::cancel_named(system::RawOrigin::Root.into(), 1u32.encode()), BadOrigin);
			assert_noop!(Scheduler::cancel(system::RawOrigin::Root.into(), 4, 1), BadOrigin);
			run_to_block(5);
			assert_eq!(
				logger::log(),
				vec![(system::RawOrigin::Signed(1).into(), 69u32), (system::RawOrigin::Signed(1).into(), 42u32)]
			);
		});
	}

	#[test]
	fn migration_to_v2_works() {
		use substrate_test_utils::assert_eq_uvec;

		new_test_ext().execute_with(|| {
			for i in 0..3u64 {
				let k = i.twox_64_concat();
				let old = vec![
					Some(ScheduledV1 {
						maybe_id: None,
						priority: i as u8 + 10,
						call: Call::Logger(logger::Call::log(96, 100)),
						maybe_periodic: None,
					}),
					None,
					Some(ScheduledV1 {
						maybe_id: Some(b"test".to_vec()),
						priority: 123,
						call: Call::Logger(logger::Call::log(69, 1000)),
						maybe_periodic: Some((456u64, 10)),
					}),
				];
				frame_support::migration::put_storage_value(
					b"Scheduler",
					b"Agenda",
					&k,
					old,
				);
			}

			assert_eq!(StorageVersion::get(), Releases::V1);

			assert!(Scheduler::migrate_v1_to_t2());

			assert_eq_uvec!(Agenda::<Test>::iter().collect::<Vec<_>>(), vec![
				(
					0,
					vec![
					Some(ScheduledV2 {
						maybe_id: None,
						priority: 10,
						call: Call::Logger(logger::Call::log(96, 100)),
						maybe_periodic: None,
						origin: root(),
						_phantom: PhantomData::<u64>::default(),
					}),
					None,
					Some(ScheduledV2 {
						maybe_id: Some(b"test".to_vec()),
						priority: 123,
						call: Call::Logger(logger::Call::log(69, 1000)),
						maybe_periodic: Some((456u64, 10)),
						origin: root(),
						_phantom: PhantomData::<u64>::default(),
					}),
				]),
				(
					1,
					vec![
						Some(ScheduledV2 {
							maybe_id: None,
							priority: 11,
							call: Call::Logger(logger::Call::log(96, 100)),
							maybe_periodic: None,
							origin: root(),
							_phantom: PhantomData::<u64>::default(),
						}),
						None,
						Some(ScheduledV2 {
							maybe_id: Some(b"test".to_vec()),
							priority: 123,
							call: Call::Logger(logger::Call::log(69, 1000)),
							maybe_periodic: Some((456u64, 10)),
							origin: root(),
							_phantom: PhantomData::<u64>::default(),
						}),
					]
				),
				(
					2,
					vec![
						Some(ScheduledV2 {
							maybe_id: None,
							priority: 12,
							call: Call::Logger(logger::Call::log(96, 100)),
							maybe_periodic: None,
							origin: root(),
							_phantom: PhantomData::<u64>::default(),
						}),
						None,
						Some(ScheduledV2 {
							maybe_id: Some(b"test".to_vec()),
							priority: 123,
							call: Call::Logger(logger::Call::log(69, 1000)),
							maybe_periodic: Some((456u64, 10)),
							origin: root(),
							_phantom: PhantomData::<u64>::default(),
						}),
					]
				)
			]);

			assert_eq!(StorageVersion::get(), Releases::V2);
		});
	}
}
