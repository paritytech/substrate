// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//	 http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#![cfg(feature = "runtime-benchmarks")]

use super::{Pallet as SafeMode, *};

use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_support::traits::{Currency, UnfilteredDispatchable};
use frame_system::{Pallet as System, RawOrigin};
use sp_runtime::traits::{Bounded, One};

benchmarks! {
	activate {
		let caller: T::AccountId = whitelisted_caller();
		let origin = RawOrigin::Signed(caller.clone());
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	}: _(origin)
	verify {
		assert_eq!(
			SafeMode::<T>::active_until().unwrap(),
			System::<T>::block_number() + T::ActivationDuration::get()
		);
	}

	force_activate {
		let force_origin = T::ForceActivateOrigin::successful_origin();
		let duration = T::ForceActivateOrigin::ensure_origin(force_origin.clone()).unwrap();
		let call = Call::<T>::force_activate {};
	}: { call.dispatch_bypass_filter(force_origin)? }
	verify {
		assert_eq!(
			SafeMode::<T>::active_until().unwrap(),
			System::<T>::block_number() +
			duration
		);
	}

	extend {
		let caller: T::AccountId = whitelisted_caller();
		let origin = RawOrigin::Signed(caller.clone());
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		System::<T>::set_block_number(1u32.into());
		assert!(SafeMode::<T>::activate(origin.clone().into()).is_ok());
	}: _(origin)
	verify {
		assert_eq!(
			SafeMode::<T>::active_until().unwrap(),
			System::<T>::block_number() + T::ActivationDuration::get() + T::ExtendDuration::get()
		);
	}

	force_extend {
		let caller: T::AccountId = whitelisted_caller();
		let origin = RawOrigin::Signed(caller.clone());
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		System::<T>::set_block_number(1u32.into());
		assert!(SafeMode::<T>::activate(origin.clone().into()).is_ok());

		let force_origin = T::ForceExtendOrigin::successful_origin();
		let extension = T::ForceExtendOrigin::ensure_origin(force_origin.clone()).unwrap();
		let call = Call::<T>::force_extend {};
	}: { call.dispatch_bypass_filter(force_origin)? }
	verify {
		assert_eq!(
			SafeMode::<T>::active_until().unwrap(),
			System::<T>::block_number() +  T::ActivationDuration::get() + extension
		);
	}

	force_deactivate {
		let caller: T::AccountId = whitelisted_caller();
		let origin = RawOrigin::Signed(caller.clone());
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		assert!(SafeMode::<T>::activate(origin.clone().into()).is_ok());

		let force_origin = T::ForceDeactivateOrigin::successful_origin();
		let call = Call::<T>::force_deactivate {};
	}: { call.dispatch_bypass_filter(force_origin)? }
	verify {
		assert_eq!(
			SafeMode::<T>::active_until(),
			None
		);
	}

	release_reservation {
		let caller: T::AccountId = whitelisted_caller();
		let origin = RawOrigin::Signed(caller.clone());
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let activated_at_block: T::BlockNumber = System::<T>::block_number();
		assert!(SafeMode::<T>::activate(origin.clone().into()).is_ok());
		let current_reservation = Reservations::<T>::get(&caller, activated_at_block).unwrap_or_default();
		assert_eq!(
			T::Currency::free_balance(&caller),
			BalanceOf::<T>::max_value() - T::ActivateReservationAmount::get().unwrap()
		);

		let force_origin = T::ForceDeactivateOrigin::successful_origin();
		assert!(SafeMode::<T>::force_deactivate(force_origin.clone()).is_ok());

		System::<T>::set_block_number(System::<T>::block_number() + T::ReleaseDelay::get().unwrap() + One::one());
		System::<T>::on_initialize(System::<T>::block_number());
		SafeMode::<T>::on_initialize(System::<T>::block_number());

		let call = Call::<T>::release_reservation { account: caller.clone(), block: activated_at_block.clone()};
	}: { call.dispatch_bypass_filter(origin.into())? }
	verify {
		assert_eq!(
			T::Currency::free_balance(&caller),
			BalanceOf::<T>::max_value()
		);
	}

	force_release_reservation {
		let caller: T::AccountId = whitelisted_caller();
		let origin = RawOrigin::Signed(caller.clone());
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let activated_at_block: T::BlockNumber = System::<T>::block_number();
		assert!(SafeMode::<T>::activate(origin.clone().into()).is_ok());
		let current_reservation = Reservations::<T>::get(&caller, activated_at_block).unwrap_or_default();
		assert_eq!(
			T::Currency::free_balance(&caller),
			BalanceOf::<T>::max_value() - T::ActivateReservationAmount::get().unwrap()
		);

		let force_origin = T::ForceDeactivateOrigin::successful_origin();
		assert!(SafeMode::<T>::force_deactivate(force_origin.clone()).is_ok());

		System::<T>::set_block_number(System::<T>::block_number() + One::one());
		System::<T>::on_initialize(System::<T>::block_number());
		SafeMode::<T>::on_initialize(System::<T>::block_number());

		let release_origin = T::ForceReservationOrigin::successful_origin();
		let call = Call::<T>::force_release_reservation { account: caller.clone(), block: activated_at_block.clone()};
	}: { call.dispatch_bypass_filter(release_origin)? }
	verify {
		assert_eq!(
			T::Currency::free_balance(&caller),
			BalanceOf::<T>::max_value()
		);
	}

	slash_reservation {
		let caller: T::AccountId = whitelisted_caller();
		let origin = RawOrigin::Signed(caller.clone());
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let activated_at_block: T::BlockNumber = System::<T>::block_number();
		assert!(SafeMode::<T>::activate(origin.clone().into()).is_ok());
		let current_reservation = Reservations::<T>::get(&caller, activated_at_block).unwrap_or_default();
		assert_eq!(
			T::Currency::free_balance(&caller),
			BalanceOf::<T>::max_value() - T::ActivateReservationAmount::get().unwrap()
		);

		let force_origin = T::ForceDeactivateOrigin::successful_origin();
		assert!(SafeMode::<T>::force_deactivate(force_origin.clone()).is_ok());

		let release_origin = T::ForceReservationOrigin::successful_origin();
		let call = Call::<T>::slash_reservation { account: caller.clone(), block: activated_at_block.clone()};
	}: { call.dispatch_bypass_filter(release_origin)? }
	verify {
		assert_eq!(
			T::Currency::free_balance(&caller),
			BalanceOf::<T>::max_value() - T::ActivateReservationAmount::get().unwrap()
		);
	}

	impl_benchmark_test_suite!(SafeMode, crate::mock::new_test_ext(), crate::mock::Test);
}
