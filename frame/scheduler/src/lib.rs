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

use sp_std::marker::PhantomData;
use frame_support::{
	dispatch::DispatchResult, decl_module, decl_storage, decl_event,
	weights::{
		SimpleDispatchInfo, DispatchInfo, DispatchClass, ClassifyDispatch, WeighData, Weight,
		PaysFee
	},
};
use sp_std::prelude::*;
use frame_benchmarking::{benchmarks, account};
use frame_system::{self as system, ensure_signed, ensure_root, RawOrigin};
use codec::{Encode, Decode};
use sp_runtime::{
	traits::{SignedExtension, Bounded, SaturatedConversion},
	transaction_validity::{
		ValidTransaction, TransactionValidityError, InvalidTransaction, TransactionValidity,
	},
};

/// A type alias for the balance type from this pallet's point of view.
type BalanceOf<T> = <T as pallet_balances::Trait>::Balance;

/// Our pallet's configuration trait. All our types and constants go in here. If the
/// pallet is dependent on specific other pallets, then their configuration traits
/// should be added to our implied traits list.
///
/// `frame_system::Trait` should always be included in our implied traits.
pub trait Trait: pallet_balances::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// The aggregated origin which the dispatch will take.
	type Origin: From<frame_system::RawOrigin<T::AccountId>>;

	/// The aggregated call type.
	type Call: Parameter + Dispatchable<Origin=Self::Origin>;

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
pub struct Scheduled<Call, Origin> {
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
		Agenda: map hasher(twox_64_concat) T::BlockNumber
			=> Vec<Scheduled<<T as Trait>::Call, <T as Trait>::Origin>>;

		/// The next free periodic index.
		NextPeriodicIndex: PeriodicIndex;
	}
}

decl_event!(
	pub enum Event<T> where B = <T as pallet_balances::Trait>::Balance {
		Scheduled(T::BlockNumber),
	}
);

decl_module! {
	// Simple declaration of the `Module` type. Lets the macro know what its working on.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		#[weight = FunctionOf(|| {
			let now = frame_system::Module::<T>::block_number();
			let limit = T::MaximumWeight::get();
			let mut queued = Agenda::<T>::get(now).into_iter()
				.map(|i| (i.priority, i.call.get_dispatch_info().weight))
				.collect::<Vec<_>>();
			queued.sort();
			queued
				.scan(0, |a, i| {
					*a += i.1;
					if i.0 <= HARD_DEADLINE || *a <= limit { Some(a) } else { None }
				})
				.last()
		}, || DispatchClass::Normal, true)]
		fn on_initialize(_n: T::BlockNumber) {
			let limit = T::MaximumWeight::get();
			let mut queued = Agenda::<T>::take(now);
			queued.sort();
			let unused_items = queued.into_iter()
				.scan(0, |cumulative_weight, i| {
					*cumulative_weight += i.call.get_dispatch_info().weight;
					Some((*cumulative_weight, i))
				})
				.filter_map(|(cumulative_weight, i)| {
					if i.priority <= HARD_DEADLINE || cumulative_weight <= limit {
						let maybe_reschedule = i.maybe_periodic.map(|p| (p, i.clone()));
						let _ = i.call.dispatch(frame_system::RawOrigin::ROOT.into());
						if let Some((periodic_index, i)) = maybe_reschedule {
							// Register the next instance of this task
							if let Some((period, count)) = Periodic::get(periodic_index) {
								if count > 1 {
									count -= 1;
									Periodic::insert(periodic_index, (period, count));
								} else {
									Periodic::remove(periodic_index);
								}
								Agenda::<T>::append(now + period, i);
							}
						}
						None
					} else {
						Some(i)
					}
				});
				.collect::<Vec<_>>();
			if !queued_items.is_empty() {
				Agenda::<T>::append_or_put(next, queued_items.into_iter());
			}
		}
	}
}

/// A type that can be used as a scheduler.
pub trait Schedule<BlockNumber, Call> {
	fn schedule(when: BlockNumber, call: Call);
	fn schedule_periodic(when: BlockNumber, period: BlockNumber, count: u32, call: Call);
}

impl<T: Trait> Scheduler<T::Call> for Module<T> {
	fn schedule(when: BlockNumber, priority: Priority, call: Call) {
		Agenda::<T>::append(when, Scheduled { priority, call, maybe_periodic: None });
	}

	fn schedule_periodic(
		when: BlockNumber,
		priority: Priority,
		period: BlockNumber,
		count: u32,
		call: Call
	) -> PeriodicIndex {
		let index = NextPeriodicIndex::mutate(|i| { let r = *1; *i += 1; *r });
		Periodic::<T>::insert(index, (period, count));
		Agenda::<T>::append(when, Scheduled { priority, call, maybe_periodic: Some(index) });
		index
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use frame_support::{assert_ok, impl_outer_origin, parameter_types, weights::GetDispatchInfo};
	use sp_core::H256;
	// The testing primitives are very useful for avoiding having to work with signatures
	// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
	use sp_runtime::{
		Perbill,
		testing::Header,
		traits::{BlakeTwo256, OnInitialize, OnFinalize, IdentityLookup},
	};

	impl_outer_origin! {
		pub enum Origin for Test  where system = frame_system {}
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
	impl frame_system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = ();
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
		type AccountData = pallet_balances::AccountData<u64>;
		type OnNewAccount = ();
		type OnKilledAccount = ();
	}
	parameter_types! {
		pub const ExistentialDeposit: u64 = 1;
	}
	impl pallet_balances::Trait for Test {
		type Balance = u64;
		type DustRemoval = ();
		type Event = ();
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
	}
	impl Trait for Test {
		type Event = ();
	}
	type System = frame_system::Module<Test>;
	type Scheduler = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		// We use default for brevity, but you can configure as desired if needed.
		pallet_balances::GenesisConfig::<Test>::default().assimilate_storage(&mut t).unwrap();
		GenesisConfig::<Test>{
			dummy: 42,
			// we configure the map with (key, value) pairs.
			bar: vec![(1, 2), (2, 3)],
			foo: 24,
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}

	#[test]
	fn it_works_for_optional_value() {
		new_test_ext().execute_with(|| {
			// Check that GenesisBuilder works properly.
			assert_eq!(Scheduler::dummy(), Some(42));

			// Check that accumulate works when we have Some value in Dummy already.
			assert_ok!(Scheduler::accumulate_dummy(Origin::signed(1), 27));
			assert_eq!(Scheduler::dummy(), Some(69));

			// Check that finalizing the block removes Dummy from storage.
			<Scheduler as OnFinalize<u64>>::on_finalize(1);
			assert_eq!(Scheduler::dummy(), None);

			// Check that accumulate works when we Dummy has None in it.
			<Scheduler as OnInitialize<u64>>::on_initialize(2);
			assert_ok!(Scheduler::accumulate_dummy(Origin::signed(1), 42));
			assert_eq!(Scheduler::dummy(), Some(42));
		});
	}

	#[test]
	fn it_works_for_default_value() {
		new_test_ext().execute_with(|| {
			assert_eq!(Scheduler::foo(), 24);
			assert_ok!(Scheduler::accumulate_foo(Origin::signed(1), 1));
			assert_eq!(Scheduler::foo(), 25);
		});
	}

	#[test]
	fn signed_ext_watch_dummy_works() {
		new_test_ext().execute_with(|| {
			let call = <Call<Test>>::set_dummy(10);
			let info = DispatchInfo::default();

			assert_eq!(
				WatchDummy::<Test>(PhantomData).validate(&1, &call, info, 150)
					.unwrap()
					.priority,
				Bounded::max_value(),
			);
			assert_eq!(
				WatchDummy::<Test>(PhantomData).validate(&1, &call, info, 250),
				InvalidTransaction::ExhaustsResources.into(),
			);
		})
	}

	#[test]
	fn weights_work() {
		// must have a default weight.
		let default_call = <Call<Test>>::accumulate_dummy(10);
		let info = default_call.get_dispatch_info();
		// aka. `let info = <Call<Test> as GetDispatchInfo>::get_dispatch_info(&default_call);`
		assert_eq!(info.weight, 10_000);

		// must have a custom weight of `100 * arg = 2000`
		let custom_call = <Call<Test>>::set_dummy(20);
		let info = custom_call.get_dispatch_info();
		assert_eq!(info.weight, 2000);
	}
}
