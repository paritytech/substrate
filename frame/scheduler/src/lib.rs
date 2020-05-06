// Copyright 2017-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! # Scheduler
//!
//! \# Scheduler
//!
//! - \[`scheduler::Trait`](./trait.Trait.html)
//! - \[`Call`](./enum.Call.html)
//! - \[`Module`](./struct.Module.html)
//!
//! \## Overview
//!
//! // Short description of pallet's purpose.
//! // Links to Traits that should be implemented.
//! // What this pallet is for.
//! // What functionality the pallet provides.
//! // When to use the pallet (use case examples).
//! // How it is used.
//! // Inputs it uses and the source of each input.
//! // Outputs it produces.
//!
//! \## Terminology
//!
//! \## Goals
//!
//! \## Interface
//!
//! \### Dispatchable Functions

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use codec::{Encode, Decode};
use sp_runtime::{RuntimeDebug, traits::{Zero, One}};
use frame_support::{
	dispatch::{Dispatchable, DispatchResult, Parameter}, decl_module, decl_storage, decl_event,
	traits::{Get, schedule},
	weights::{GetDispatchInfo, Weight},
};
use frame_system::{self as system};

/// Our pallet's configuration trait. All our types and constants go in here. If the
/// pallet is dependent on specific other pallets, then their configuration traits
/// should be added to our implied traits list.
///
/// `system::Trait` should always be included in our implied traits.
pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// The aggregated origin which the dispatch will take.
	type Origin: From<system::RawOrigin<Self::AccountId>>;

	/// The aggregated call type.
	type Call: Parameter + Dispatchable<Origin=<Self as Trait>::Origin> + GetDispatchInfo;

	/// The maximum weight that may be scheduled per block for any dispatchables of less priority
	/// than `schedule::HARD_DEADLINE`.
	type MaximumWeight: Get<Weight>;
}

/// Just a simple index for naming period tasks.
pub type PeriodicIndex = u32;
/// The location of a scheduled task that can be used to remove it.
pub type TaskAddress<BlockNumber> = (BlockNumber, u32);

/// Information regarding an item to be executed in the future.
#[derive(Clone, RuntimeDebug, Encode, Decode)]
pub struct Scheduled<Call, BlockNumber> {
	/// The unique identity for this task, if there is one.
	maybe_id: Option<Vec<u8>>,
	/// This task's priority.
	priority: schedule::Priority,
	/// The call to be dispatched.
	call: Call,
	/// If the call is periodic, then this points to the information concerning that.
	maybe_periodic: Option<schedule::Period<BlockNumber>>,
}

decl_storage! {
	trait Store for Module<T: Trait> as Scheduler {
		/// Items to be executed, indexed by the block number that they should be executed on.
		pub Agenda: map hasher(twox_64_concat) T::BlockNumber
			=> Vec<Option<Scheduled<<T as Trait>::Call, T::BlockNumber>>>;

		/// Lookup from identity to the block number and index of the task.
		Lookup: map hasher(twox_64_concat) Vec<u8> => Option<TaskAddress<T::BlockNumber>>;
	}
}

decl_event!(
	pub enum Event<T> where <T as system::Trait>::BlockNumber {
		Scheduled(BlockNumber),
		Dispatched(TaskAddress<BlockNumber>, Option<Vec<u8>>, DispatchResult),
	}
);

decl_module! {
	// Simple declaration of the `Module` type. Lets the macro know what its working on.
	pub struct Module<T: Trait> for enum Call where origin: <T as system::Trait>::Origin {
		fn deposit_event() = default;

		fn on_initialize(now: T::BlockNumber) -> Weight {
			let limit = T::MaximumWeight::get();
			let mut queued = Agenda::<T>::take(now).into_iter()
				.enumerate()
				.filter_map(|(index, s)| s.map(|inner| (index as u32, inner)))
				.collect::<Vec<_>>();
			queued.sort_by_key(|(_, s)| s.priority);
			let mut result = 0;
			let unused_items = queued.into_iter()
				.enumerate()
				.scan(0, |cumulative_weight, (order, (index, s))| {
					*cumulative_weight += s.call.get_dispatch_info().weight;
					Some((order, index, *cumulative_weight, s))
				})
				.filter_map(|(order, index, cumulative_weight, mut s)| {
					if s.priority <= schedule::HARD_DEADLINE || cumulative_weight <= limit || order == 0 {
						let r = s.call.clone().dispatch(system::RawOrigin::Root.into());
						let maybe_id = s.maybe_id.clone();
						if let &Some((period, count)) = &s.maybe_periodic {
							if count > 1 {
								s.maybe_periodic = Some((period, count - 1));
							} else {
								s.maybe_periodic = None;
							}
							let next = now + period;
							if let Some(ref id) = s.maybe_id {
								let next_index = Agenda::<T>::decode_len(now + period).unwrap_or(0) as u32;
								Lookup::<T>::insert(id, (next, next_index));
							}
							Agenda::<T>::append_or_insert(next, &[Some(s)][..]);
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
						result = cumulative_weight;
						None
					} else {
						Some(Some(s))
					}
				})
				.collect::<Vec<_>>();
			if !unused_items.is_empty() {
				let next = now + One::one();
				Agenda::<T>::append_or_insert(next, &unused_items[..]);
			}
			result
		}
	}
}

impl<T: Trait> schedule::Anon<T::BlockNumber, <T as Trait>::Call> for Module<T> {
	type Address = TaskAddress<T::BlockNumber>;

	fn schedule(
		when: T::BlockNumber,
		maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
		priority: schedule::Priority,
		call: <T as Trait>::Call
	) -> Self::Address {
		// sanitize maybe_periodic
		let maybe_periodic = maybe_periodic
			.filter(|p| p.1 > 1 && !p.0.is_zero())
			// Remove one from the number of repetitions since we will schedule one now.
			.map(|(p, c)| (p, c - 1));
		let s = Some(Scheduled { maybe_id: None, priority, call, maybe_periodic });
		Agenda::<T>::append_or_insert(when, &[s][..]);
		(when, Agenda::<T>::decode_len(when).unwrap_or(1) as u32 - 1)
	}

	fn cancel((when, index): Self::Address) -> Result<(), ()> {
		if let Some(s) = Agenda::<T>::mutate(when, |agenda| agenda.get_mut(index as usize).and_then(Option::take)) {
			if let Some(id) = s.maybe_id {
				Lookup::<T>::remove(id)
			}
			Ok(())
		} else {
			Err(())
		}
	}
}

impl<T: Trait> schedule::Named<T::BlockNumber, <T as Trait>::Call> for Module<T> {
	type Address = TaskAddress<T::BlockNumber>;

	fn schedule_named(
		id: impl Encode,
		when: T::BlockNumber,
		maybe_periodic: Option<schedule::Period<T::BlockNumber>>,
		priority: schedule::Priority,
		call: <T as Trait>::Call,
	) -> Result<Self::Address, ()> {
		// determine id and ensure it is unique
		let id = id.encode();
		if Lookup::<T>::contains_key(&id) {
			return Err(())
		}

		// sanitize maybe_periodic
		let maybe_periodic = maybe_periodic
			.filter(|p| p.1 > 1 && !p.0.is_zero())
			// Remove one from the number of repetitions since we will schedule one now.
			.map(|(p, c)| (p, c - 1));

		let s = Scheduled { maybe_id: Some(id.clone()), priority, call, maybe_periodic };
		Agenda::<T>::append_or_insert(when, &[Some(s)][..]);
		let index = Agenda::<T>::decode_len(when).unwrap_or(1) as u32 - 1;
		let address = (when, index);
		Lookup::<T>::insert(&id, &address);
		Ok(address)
	}

	fn cancel_named(id: impl Encode) -> Result<(), ()> {
		if let Some((when, index)) = id.using_encoded(|d| Lookup::<T>::take(d)) {
			let i = index as usize;
			Agenda::<T>::mutate(when, |agenda| if let Some(s) = agenda.get_mut(i) { *s = None });
			Ok(())
		} else {
			Err(())
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use frame_support::{
		impl_outer_event, impl_outer_origin, impl_outer_dispatch, parameter_types, assert_ok,
		traits::{OnInitialize, OnFinalize, schedule::{Anon, Named}},
		weights::{DispatchClass, FunctionOf, Pays}
	};
	use sp_core::H256;
	// The testing primitives are very useful for avoiding having to work with signatures
	// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
	use sp_runtime::{
		Perbill,
		testing::Header,
		traits::{BlakeTwo256, IdentityLookup},
	};
	use crate as scheduler;

	mod logger {
		use super::*;
		use std::cell::RefCell;
		use frame_system::ensure_root;

		thread_local! {
			static LOG: RefCell<Vec<u32>> = RefCell::new(Vec::new());
		}
		pub fn log() -> Vec<u32> {
			LOG.with(|log| log.borrow().clone())
		}
		pub trait Trait: system::Trait {
			type Event: From<Event> + Into<<Self as system::Trait>::Event>;
		}
		decl_storage! {
			trait Store for Module<T: Trait> as Logger {
			}
		}
		decl_event! {
			pub enum Event {
				Logged(u32, Weight),
			}
		}
		decl_module! {
			// Simple declaration of the `Module` type. Lets the macro know what its working on.
			pub struct Module<T: Trait> for enum Call where origin: <T as system::Trait>::Origin {
				fn deposit_event() = default;

				#[weight = FunctionOf(
					|args: (&u32, &Weight)| *args.1,
					|_: (&u32, &Weight)| DispatchClass::Normal,
					Pays::Yes,
				)]
				fn log(origin, i: u32, weight: Weight) {
					ensure_root(origin)?;
					Self::deposit_event(Event::Logged(i, weight));
					LOG.with(|log| {
						log.borrow_mut().push(i);
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
	// For testing the pallet, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of pallets we want to use.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl system::Trait for Test {
		type Origin = Origin;
		type Call = ();
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
		type DbWeight = ();
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
		type ModuleToIndex = ();
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
	}
	impl logger::Trait for Test {
		type Event = ();
	}
	parameter_types! {
		pub const MaximumWeight: Weight = 10_000;
	}
	impl Trait for Test {
		type Event = ();
		type Origin = Origin;
		type Call = Call;
		type MaximumWeight = MaximumWeight;
	}
	type System = system::Module<Test>;
	type Logger = logger::Module<Test>;
	type Scheduler = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> sp_io::TestExternalities {
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

	#[test]
	fn basic_scheduling_works() {
		new_test_ext().execute_with(|| {
			Scheduler::schedule(4, None, 127, Call::Logger(logger::Call::log(42, 1000)));
			run_to_block(3);
			assert!(logger::log().is_empty());
			run_to_block(4);
			assert_eq!(logger::log(), vec![42u32]);
			run_to_block(100);
			assert_eq!(logger::log(), vec![42u32]);
		});
	}

	#[test]
	fn periodic_scheduling_works() {
		new_test_ext().execute_with(|| {
			// at #4, every 3 blocks, 3 times.
			Scheduler::schedule(4, Some((3, 3)), 127, Call::Logger(logger::Call::log(42, 1000)));
			run_to_block(3);
			assert!(logger::log().is_empty());
			run_to_block(4);
			assert_eq!(logger::log(), vec![42u32]);
			run_to_block(6);
			assert_eq!(logger::log(), vec![42u32]);
			run_to_block(7);
			assert_eq!(logger::log(), vec![42u32, 42u32]);
			run_to_block(9);
			assert_eq!(logger::log(), vec![42u32, 42u32]);
			run_to_block(10);
			assert_eq!(logger::log(), vec![42u32, 42u32, 42u32]);
			run_to_block(100);
			assert_eq!(logger::log(), vec![42u32, 42u32, 42u32]);
		});
	}

	#[test]
	fn cancel_named_scheduling_works_with_normal_cancel() {
		new_test_ext().execute_with(|| {
			// at #4.
			Scheduler::schedule_named(1u32, 4, None, 127, Call::Logger(logger::Call::log(69, 1000))).unwrap();
			let i = Scheduler::schedule(4, None, 127, Call::Logger(logger::Call::log(42, 1000)));
			run_to_block(3);
			assert!(logger::log().is_empty());
			assert_ok!(Scheduler::cancel_named(1u32));
			assert_ok!(Scheduler::cancel(i));
			run_to_block(100);
			assert!(logger::log().is_empty());
		});
	}

	#[test]
	fn cancel_named_periodic_scheduling_works() {
		new_test_ext().execute_with(|| {
			// at #4, every 3 blocks, 3 times.
			Scheduler::schedule_named(1u32, 4, Some((3, 3)), 127, Call::Logger(logger::Call::log(42, 1000))).unwrap();
			// same id results in error.
			assert!(Scheduler::schedule_named(1u32, 4, None, 127, Call::Logger(logger::Call::log(69, 1000))).is_err());
			// different id is ok.
			Scheduler::schedule_named(2u32, 8, None, 127, Call::Logger(logger::Call::log(69, 1000))).unwrap();
			run_to_block(3);
			assert!(logger::log().is_empty());
			run_to_block(4);
			assert_eq!(logger::log(), vec![42u32]);
			run_to_block(6);
			assert_ok!(Scheduler::cancel_named(1u32));
			run_to_block(100);
			assert_eq!(logger::log(), vec![42u32, 69u32]);
		});
	}

	#[test]
	fn scheduler_respects_weight_limits() {
		new_test_ext().execute_with(|| {
			Scheduler::schedule(4, None, 127, Call::Logger(logger::Call::log(42, 6000)));
			Scheduler::schedule(4, None, 127, Call::Logger(logger::Call::log(69, 6000)));
			run_to_block(4);
			assert_eq!(logger::log(), vec![42u32]);
			run_to_block(5);
			assert_eq!(logger::log(), vec![42u32, 69u32]);
		});
	}

	#[test]
	fn scheduler_respects_hard_deadlines_more() {
		new_test_ext().execute_with(|| {
			Scheduler::schedule(4, None, 0, Call::Logger(logger::Call::log(42, 6000)));
			Scheduler::schedule(4, None, 0, Call::Logger(logger::Call::log(69, 6000)));
			run_to_block(4);
			assert_eq!(logger::log(), vec![42u32, 69u32]);
		});
	}

	#[test]
	fn scheduler_respects_priority_ordering() {
		new_test_ext().execute_with(|| {
			Scheduler::schedule(4, None, 1, Call::Logger(logger::Call::log(42, 6000)));
			Scheduler::schedule(4, None, 0, Call::Logger(logger::Call::log(69, 6000)));
			run_to_block(4);
			assert_eq!(logger::log(), vec![69u32, 42u32]);
		});
	}

	#[test]
	fn scheduler_respects_priority_ordering_with_soft_deadlines() {
		new_test_ext().execute_with(|| {
			Scheduler::schedule(4, None, 255, Call::Logger(logger::Call::log(42, 5000)));
			Scheduler::schedule(4, None, 127, Call::Logger(logger::Call::log(69, 5000)));
			Scheduler::schedule(4, None, 126, Call::Logger(logger::Call::log(2600, 6000)));
			run_to_block(4);
			assert_eq!(logger::log(), vec![2600u32]);
			run_to_block(5);
			assert_eq!(logger::log(), vec![2600u32, 69u32, 42u32]);
		});
	}

	#[test]
	fn initialize_weight_is_correct() {
		new_test_ext().execute_with(|| {
			Scheduler::schedule(1, None, 255, Call::Logger(logger::Call::log(3, 1000)));
			Scheduler::schedule(1, None, 128, Call::Logger(logger::Call::log(42, 5000)));
			Scheduler::schedule(1, None, 127, Call::Logger(logger::Call::log(69, 5000)));
			Scheduler::schedule(1, None, 126, Call::Logger(logger::Call::log(2600, 6000)));
			let weight = Scheduler::on_initialize(1);
			assert_eq!(weight, 6000);
			let weight = Scheduler::on_initialize(2);
			assert_eq!(weight, 10000);
			let weight = Scheduler::on_initialize(3);
			assert_eq!(weight, 1000);
			let weight = Scheduler::on_initialize(4);
			assert_eq!(weight, 0);
		});
	}
}
