// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use frame_benchmarking::v2::*;
use frame_support::traits::{fungible::Mutate as FunMutate, UnfilteredDispatchable};
use frame_system::{Pallet as System, RawOrigin};
use sp_runtime::traits::{Bounded, One, Zero};

#[benchmarks(where T::Currency: FunMutate<T::AccountId>)]
mod benchmarks {
	use super::*;

	/// `on_initialize` doing nothing.
	#[benchmark]
	fn on_initialize_noop() {
		#[block]
		{
			SafeMode::<T>::on_initialize(1u32.into());
		}
	}

	/// `on_initialize` exiting since the until block is in the past.
	#[benchmark]
	fn on_initialize_exit() {
		EnteredUntil::<T>::put(&BlockNumberFor::<T>::zero());
		assert!(SafeMode::<T>::is_entered());

		#[block]
		{
			SafeMode::<T>::on_initialize(1u32.into());
		}

		assert!(!SafeMode::<T>::is_entered());
	}

	/// Permissionless enter - if configured.
	#[benchmark]
	fn enter() -> Result<(), BenchmarkError> {
		T::EnterDepositAmount::get().ok_or_else(|| BenchmarkError::Weightless)?;

		let caller: T::AccountId = whitelisted_caller();
		let origin = RawOrigin::Signed(caller.clone());
		T::Currency::set_balance(&caller, init_bal::<T>());

		#[extrinsic_call]
		_(origin);

		assert_eq!(
			EnteredUntil::<T>::get().unwrap(),
			System::<T>::block_number() + T::EnterDuration::get()
		);
		Ok(())
	}

	/// Forceful enter - if configured.
	#[benchmark]
	fn force_enter() -> Result<(), BenchmarkError> {
		let force_origin =
			T::ForceEnterOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;

		let duration = T::ForceEnterOrigin::ensure_origin(force_origin.clone()).unwrap();

		#[extrinsic_call]
		_(force_origin as T::RuntimeOrigin);

		assert_eq!(EnteredUntil::<T>::get().unwrap(), System::<T>::block_number() + duration);
		Ok(())
	}

	/// Permissionless extend - if configured.
	#[benchmark]
	fn extend() -> Result<(), BenchmarkError> {
		T::ExtendDepositAmount::get().ok_or_else(|| BenchmarkError::Weightless)?;

		let alice: T::AccountId = whitelisted_caller();
		T::Currency::set_balance(&alice, init_bal::<T>());

		System::<T>::set_block_number(1u32.into());
		assert!(SafeMode::<T>::do_enter(None, 1u32.into()).is_ok());

		#[extrinsic_call]
		_(RawOrigin::Signed(alice));

		assert_eq!(
			EnteredUntil::<T>::get().unwrap(),
			System::<T>::block_number() + 1u32.into() + T::ExtendDuration::get()
		);
		Ok(())
	}

	/// Forceful extend - if configured.
	#[benchmark]
	fn force_extend() -> Result<(), BenchmarkError> {
		let force_origin = T::ForceExtendOrigin::try_successful_origin()
			.map_err(|_| BenchmarkError::Weightless)?;

		System::<T>::set_block_number(1u32.into());
		assert!(SafeMode::<T>::do_enter(None, 1u32.into()).is_ok());

		let duration = T::ForceExtendOrigin::ensure_origin(force_origin.clone()).unwrap();
		let call = Call::<T>::force_extend {};

		#[block]
		{
			call.dispatch_bypass_filter(force_origin)?;
		}

		assert_eq!(
			EnteredUntil::<T>::get().unwrap(),
			System::<T>::block_number() + 1u32.into() + duration
		);
		Ok(())
	}

	/// Forceful exit - if configured.
	#[benchmark]
	fn force_exit() -> Result<(), BenchmarkError> {
		let force_origin =
			T::ForceExitOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
		assert!(SafeMode::<T>::do_enter(None, 1u32.into()).is_ok());

		#[extrinsic_call]
		_(force_origin as T::RuntimeOrigin);

		assert_eq!(EnteredUntil::<T>::get(), None);
		Ok(())
	}

	/// Permissionless release of a deposit - if configured.
	#[benchmark]
	fn release_deposit() -> Result<(), BenchmarkError> {
		let delay = T::ReleaseDelay::get().ok_or_else(|| BenchmarkError::Weightless)?;

		let alice: T::AccountId = whitelisted_caller();
		let origin = RawOrigin::Signed(alice.clone());

		T::Currency::set_balance(&alice, init_bal::<T>());
		// Mock the storage. This is needed in case the `EnterDepositAmount` is zero.
		let block: BlockNumberFor<T> = 1u32.into();
		let bal: BalanceOf<T> = 1u32.into();
		Deposits::<T>::insert(&alice, &block, &bal);
		T::Currency::hold(&HoldReason::EnterOrExtend.into(), &alice, bal)?;
		EnteredUntil::<T>::put(&block);
		assert!(SafeMode::<T>::do_exit(ExitReason::Force).is_ok());

		System::<T>::set_block_number(delay + One::one() + 2u32.into());
		System::<T>::on_initialize(System::<T>::block_number());
		SafeMode::<T>::on_initialize(System::<T>::block_number());

		#[extrinsic_call]
		_(origin, alice.clone(), 1u32.into());

		assert!(!Deposits::<T>::contains_key(&alice, &block));
		assert_eq!(T::Currency::balance(&alice), init_bal::<T>());
		Ok(())
	}

	/// Forceful release of a deposit - if configured.
	#[benchmark]
	fn force_release_deposit() -> Result<(), BenchmarkError> {
		let force_origin = T::ForceDepositOrigin::try_successful_origin()
			.map_err(|_| BenchmarkError::Weightless)?;

		let alice: T::AccountId = whitelisted_caller();
		T::Currency::set_balance(&alice, init_bal::<T>());

		// Mock the storage. This is needed in case the `EnterDepositAmount` is zero.
		let block: BlockNumberFor<T> = 1u32.into();
		let bal: BalanceOf<T> = 1u32.into();
		Deposits::<T>::insert(&alice, &block, &bal);
		T::Currency::hold(&&HoldReason::EnterOrExtend.into(), &alice, bal)?;
		EnteredUntil::<T>::put(&block);

		assert_eq!(T::Currency::balance(&alice), init_bal::<T>() - 1u32.into());
		assert!(SafeMode::<T>::do_exit(ExitReason::Force).is_ok());

		System::<T>::set_block_number(System::<T>::block_number() + One::one());
		System::<T>::on_initialize(System::<T>::block_number());
		SafeMode::<T>::on_initialize(System::<T>::block_number());

		#[extrinsic_call]
		_(force_origin as T::RuntimeOrigin, alice.clone(), block);

		assert!(!Deposits::<T>::contains_key(&alice, block));
		assert_eq!(T::Currency::balance(&alice), init_bal::<T>());
		Ok(())
	}

	#[benchmark]
	fn force_slash_deposit() -> Result<(), BenchmarkError> {
		let force_origin = T::ForceDepositOrigin::try_successful_origin()
			.map_err(|_| BenchmarkError::Weightless)?;

		let alice: T::AccountId = whitelisted_caller();
		T::Currency::set_balance(&alice, init_bal::<T>());

		// Mock the storage. This is needed in case the `EnterDepositAmount` is zero.
		let block: BlockNumberFor<T> = 1u32.into();
		let bal: BalanceOf<T> = 1u32.into();
		Deposits::<T>::insert(&alice, &block, &bal);
		T::Currency::hold(&&HoldReason::EnterOrExtend.into(), &alice, bal)?;
		EnteredUntil::<T>::put(&block);
		assert!(SafeMode::<T>::do_exit(ExitReason::Force).is_ok());

		#[extrinsic_call]
		_(force_origin as T::RuntimeOrigin, alice.clone(), block);

		assert!(!Deposits::<T>::contains_key(&alice, block));
		assert_eq!(T::Currency::balance(&alice), init_bal::<T>() - 1u32.into());
		Ok(())
	}

	fn init_bal<T: Config>() -> BalanceOf<T> {
		BalanceOf::<T>::max_value() / 10u32.into()
	}

	impl_benchmark_test_suite!(SafeMode, crate::mock::new_test_ext(), crate::mock::Test);
}
