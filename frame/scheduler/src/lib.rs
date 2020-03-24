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
//! - \[`<INSERT_CUSTOM_PALLET_NAME>::Trait`](./trait.Trait.html)
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
use sp_runtime::{RuntimeDebug, traits::One};
use frame_support::{
	dispatch::{Dispatchable, Parameter}, decl_module, decl_storage, decl_event, traits::Get,
	weights::{DispatchClass, Weight, FunctionOf, GetDispatchInfo},
};
//use frame_benchmarking::{benchmarks, account};
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
	/// than 255.
	type MaximumWeight: Get<Weight>;
}

/// Just a simple index for naming period tasks.
pub type PeriodicIndex = u32;
/// Priority with which a call is scheduled. It's just a linear amount with higher values meaning
/// higher priority.
pub type Priority = u8;

/// The highest priority. We invest the value so that normal sorting will place the highest
/// priority at the beginning of the list.
pub const HIGHEST_PRORITY: Priority = 0;
/// Anything of this value or lower will definitely be scheduled on the block that the ask for, even
/// if it breaches the `MaximumWeight` limitation.
pub const HARD_DEADLINE: Priority = 63;
/// The lowest priority. Most stuff should be around here.
pub const LOWEST_PRORITY: Priority = 255;

/// Information regarding an item to be executed in the future.
#[derive(Clone, RuntimeDebug, Encode, Decode)]
pub struct Scheduled<Call> {
	/// This task's priority.
	priority: Priority,
	/// The call to be dispatched.
	call: Call,
	/// If the call is periodic, then this points to the information concerning that.
	maybe_periodic: Option<PeriodicIndex>,
}

decl_storage! {
	trait Store for Module<T: Trait> as Scheduler {
		/// Any period items.
		Periodic: map hasher(twox_64_concat) PeriodicIndex => Option<(T::BlockNumber, u32)>;

		/// Items to be executed, indexed by the block number that they should be executed on.
		/// This is ordered by `priority`.
		Agenda: map hasher(twox_64_concat) T::BlockNumber => Vec<Scheduled<<T as Trait>::Call>>;

		/// The next free periodic index.
		LastPeriodicIndex: PeriodicIndex;
	}
}

decl_event!(
	pub enum Event<T> where <T as system::Trait>::BlockNumber {
		Scheduled(BlockNumber),
	}
);

decl_module! {
	// Simple declaration of the `Module` type. Lets the macro know what its working on.
	pub struct Module<T: Trait> for enum Call where origin: <T as system::Trait>::Origin {
		fn deposit_event() = default;

		#[weight = FunctionOf(|_| -> u32 {
			let now = system::Module::<T>::block_number();
			let limit = T::MaximumWeight::get();
			let mut queued = Agenda::<T>::get(now).into_iter()
				.map(|i| (i.priority, i.call.get_dispatch_info().weight))
				.collect::<Vec<_>>();
			queued.sort_by_key(|i| i.0);
			queued.into_iter()
				.scan(0, |a, i| {
					*a += i.1;
					if i.0 <= HARD_DEADLINE || *a <= limit { Some(*a) } else { None }
				})
				.last()
				.unwrap_or(0)
				+ 10_000
		}, || DispatchClass::Normal, true)]
		fn on_initialize(now: T::BlockNumber) {
			let limit = T::MaximumWeight::get();
			let mut queued = Agenda::<T>::take(now);
			queued.sort_by_key(|i| i.priority);
			let unused_items = queued.into_iter()
				.scan(0, |cumulative_weight, i| {
					*cumulative_weight += i.call.get_dispatch_info().weight;
					Some((*cumulative_weight, i))
				})
				.filter_map(|(cumulative_weight, i)| {
					if i.priority <= HARD_DEADLINE || cumulative_weight <= limit {
						let maybe_reschedule = i.maybe_periodic.map(|p| (p, i.clone()));
						let _ = i.call.dispatch(system::RawOrigin::Root.into());
						if let Some((periodic_index, i)) = maybe_reschedule {
							// Register the next instance of this task
							if let Some((period, count)) = Periodic::<T>::get(periodic_index) {
								if count > 1 {
									Periodic::<T>::insert(periodic_index, (period, count - 1));
								} else {
									Periodic::<T>::remove(periodic_index);
								}
								Agenda::<T>::append_or_insert(now + period, &[i][..]);
							}
						}
						None
					} else {
						Some(i)
					}
				})
				.collect::<Vec<_>>();
			let next = now + One::one();
			if !unused_items.is_empty() {
				Agenda::<T>::append_or_insert(next, &unused_items[..]);
			}
		}
	}
}

/// A type that can be used as a scheduler.
pub trait Schedule<BlockNumber, Call> {
	/// Schedule a one-off dispatch to happen at the beginning of some block in the future.
	fn schedule(when: BlockNumber, priority: Priority, call: Call);

	/// Schedule a dispatch to happen periodically into the future for come number of times.
	///
	/// An index is returned so that it can be cancelled at some point in the future.
	fn schedule_periodic(
		when: BlockNumber,
		period: BlockNumber,
		count: u32,
		priority: Priority,
		call: Call,
	) -> PeriodicIndex;

	/// Cancel a periodic dispatch. If called during its dispatch, it will not be dispatched
	/// any further. If called between dispatches, the next dispatch will happen as scheduled but
	/// then it will cease.
	fn cancel_periodic(index: PeriodicIndex) -> Result<(), ()>;
}

impl<T: Trait> Schedule<T::BlockNumber, <T as Trait>::Call> for Module<T> {
	fn schedule(when: T::BlockNumber, priority: Priority, call: <T as Trait>::Call) {
		let s = Scheduled { priority, call, maybe_periodic: None };
		Agenda::<T>::append_or_insert(when, &[s][..]);
	}

	fn schedule_periodic(
		when: T::BlockNumber,
		period: T::BlockNumber,
		count: u32,
		priority: Priority,
		call: <T as Trait>::Call,
	) -> PeriodicIndex {
		match count {
			0 => 0,
			1 => {
				Self::schedule(when, priority, call);
				0
			}
			count => {
				let index = LastPeriodicIndex::mutate(|i| { *i += 1; *i });
				Periodic::<T>::insert(index, (period, count - 1));
				let s = Scheduled { priority, call, maybe_periodic: Some(index) };
				Agenda::<T>::append_or_insert(when, &[s][..]);
				index
			}
		}
	}

	fn cancel_periodic(index: PeriodicIndex) -> Result<(), ()> {
		if index == 0 {
			Err(())
		} else {
			Periodic::<T>::take(index).map(|_| ()).ok_or(())
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use frame_support::{
		impl_outer_event, impl_outer_origin, impl_outer_dispatch, parameter_types
	};
	use sp_core::H256;
	// The testing primitives are very useful for avoiding having to work with signatures
	// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
	use sp_runtime::{
		Perbill,
		testing::Header,
		traits::{BlakeTwo256, OnInitialize, OnFinalize, IdentityLookup},
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
					true
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
			Scheduler::schedule(4, 127, Call::Logger(logger::Call::log(42, 1000)));
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
			Scheduler::schedule_periodic(4, 3, 3, 127, Call::Logger(logger::Call::log(42, 1000)));
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
	fn cancel_period_scheduling_works() {
		new_test_ext().execute_with(|| {
			// at #4, every 3 blocks, 3 times.
			let i = Scheduler::schedule_periodic(4, 3, 3, 127, Call::Logger(logger::Call::log(42, 1000)));
			run_to_block(3);
			assert!(logger::log().is_empty());
			run_to_block(4);
			assert_eq!(logger::log(), vec![42u32]);
			run_to_block(6);
			assert_eq!(logger::log(), vec![42u32]);
			Scheduler::cancel_periodic(i).unwrap();
			run_to_block(7);
			assert_eq!(logger::log(), vec![42u32, 42u32]);
			run_to_block(100);
			assert_eq!(logger::log(), vec![42u32, 42u32]);
		});
	}

	#[test]
	fn scheduler_respects_weight_limits() {
		new_test_ext().execute_with(|| {
			Scheduler::schedule(4, 127, Call::Logger(logger::Call::log(42, 6000)));
			Scheduler::schedule(4, 127, Call::Logger(logger::Call::log(69, 6000)));
			run_to_block(4);
			assert_eq!(logger::log(), vec![42u32]);
			run_to_block(5);
			assert_eq!(logger::log(), vec![42u32, 69u32]);
		});
	}

	#[test]
	fn scheduler_respects_hard_deadlines_more() {
		new_test_ext().execute_with(|| {
			Scheduler::schedule(4, 0, Call::Logger(logger::Call::log(42, 6000)));
			Scheduler::schedule(4, 0, Call::Logger(logger::Call::log(69, 6000)));
			run_to_block(4);
			assert_eq!(logger::log(), vec![42u32, 69u32]);
		});
	}

	#[test]
	fn scheduler_respects_priority_ordering() {
		new_test_ext().execute_with(|| {
			Scheduler::schedule(4, 1, Call::Logger(logger::Call::log(42, 6000)));
			Scheduler::schedule(4, 0, Call::Logger(logger::Call::log(69, 6000)));
			run_to_block(4);
			assert_eq!(logger::log(), vec![69u32, 42u32]);
		});
	}

	#[test]
	fn scheduler_respects_priority_ordering_with_soft_deadlines() {
		new_test_ext().execute_with(|| {
			Scheduler::schedule(4, 255, Call::Logger(logger::Call::log(42, 5000)));
			Scheduler::schedule(4, 127, Call::Logger(logger::Call::log(69, 5000)));
			Scheduler::schedule(4, 126, Call::Logger(logger::Call::log(2600, 6000)));
			run_to_block(4);
			assert_eq!(logger::log(), vec![2600u32]);
			run_to_block(5);
			assert_eq!(logger::log(), vec![2600u32, 69u32, 42u32]);
		});
	}
}
