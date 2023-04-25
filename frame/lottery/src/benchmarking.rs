// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Lottery pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use crate::Pallet as Lottery;
use frame_benchmarking::{
	impl_benchmark_test_suite,
	v1::{account, whitelisted_caller, BenchmarkError},
	v2::*,
};
use frame_support::{
	storage::bounded_vec::BoundedVec,
	traits::{EnsureOrigin, OnInitialize},
};
use frame_system::RawOrigin;
use sp_runtime::traits::{Bounded, Zero};

// Set up and start a lottery
fn setup_lottery<T: Config>(repeat: bool) -> Result<(), &'static str> {
	let price = T::Currency::minimum_balance();
	let length = 10u32.into();
	let delay = 5u32.into();
	// Calls will be maximum length...
	let mut calls = vec![
		frame_system::Call::<T>::set_code { code: vec![] }.into();
		T::MaxCalls::get().saturating_sub(1) as usize
	];
	// Last call will be the match for worst case scenario.
	calls.push(frame_system::Call::<T>::remark { remark: vec![] }.into());
	let origin = T::ManagerOrigin::try_successful_origin()
		.expect("ManagerOrigin has no successful origin required for the benchmark");
	Lottery::<T>::set_calls(origin.clone(), calls)?;
	Lottery::<T>::start_lottery(origin, price, length, delay, repeat)?;
	Ok(())
}

#[benchmarks]
mod benchmarks {
	use super::*;

	#[benchmark]
	fn buy_ticket() -> Result<(), BenchmarkError> {
		let caller = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		setup_lottery::<T>(false)?;
		// force user to have a long vec of calls participating
		let set_code_index: CallIndex = Lottery::<T>::call_to_index(
			&frame_system::Call::<T>::set_code { code: vec![] }.into(),
		)?;
		let already_called: (u32, BoundedVec<CallIndex, T::MaxCalls>) = (
			LotteryIndex::<T>::get(),
			BoundedVec::<CallIndex, T::MaxCalls>::try_from(vec![
				set_code_index;
				T::MaxCalls::get().saturating_sub(1)
					as usize
			])
			.unwrap(),
		);
		Participants::<T>::insert(&caller, already_called);

		let call = frame_system::Call::<T>::remark { remark: vec![] };

		#[extrinsic_call]
		_(RawOrigin::Signed(caller), Box::new(call.into()));

		assert_eq!(TicketsCount::<T>::get(), 1);

		Ok(())
	}

	#[benchmark]
	fn set_calls(n: Linear<0, { T::MaxCalls::get() }>) -> Result<(), BenchmarkError> {
		let calls = vec![frame_system::Call::<T>::remark { remark: vec![] }.into(); n as usize];
		let origin =
			T::ManagerOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
		assert!(CallIndices::<T>::get().is_empty());

		#[extrinsic_call]
		_(origin as T::RuntimeOrigin, calls);

		if !n.is_zero() {
			assert!(!CallIndices::<T>::get().is_empty());
		}

		Ok(())
	}

	#[benchmark]
	fn start_lottery() -> Result<(), BenchmarkError> {
		let price = BalanceOf::<T>::max_value();
		let end = 10u32.into();
		let payout = 5u32.into();
		let origin =
			T::ManagerOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;

		#[extrinsic_call]
		_(origin as T::RuntimeOrigin, price, end, payout, true);

		assert!(crate::Lottery::<T>::get().is_some());

		Ok(())
	}

	#[benchmark]
	fn stop_repeat() -> Result<(), BenchmarkError> {
		setup_lottery::<T>(true)?;
		assert_eq!(crate::Lottery::<T>::get().unwrap().repeat, true);
		let origin =
			T::ManagerOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;

		#[extrinsic_call]
		_(origin as T::RuntimeOrigin);

		assert_eq!(crate::Lottery::<T>::get().unwrap().repeat, false);

		Ok(())
	}

	#[benchmark]
	fn on_initialize_end() -> Result<(), BenchmarkError> {
		setup_lottery::<T>(false)?;
		let winner = account("winner", 0, 0);
		// User needs more than min balance to get ticket
		T::Currency::make_free_balance_be(&winner, T::Currency::minimum_balance() * 10u32.into());
		// Make sure lottery account has at least min balance too
		let lottery_account = Lottery::<T>::account_id();
		T::Currency::make_free_balance_be(
			&lottery_account,
			T::Currency::minimum_balance() * 10u32.into(),
		);
		// Buy a ticket
		let call = frame_system::Call::<T>::remark { remark: vec![] };
		Lottery::<T>::buy_ticket(RawOrigin::Signed(winner.clone()).into(), Box::new(call.into()))?;
		// Kill user account for worst case
		T::Currency::make_free_balance_be(&winner, 0u32.into());
		// Assert that lotto is set up for winner
		assert_eq!(TicketsCount::<T>::get(), 1);
		assert!(!Lottery::<T>::pot().1.is_zero());

		#[block]
		{
			// Generate `MaxGenerateRandom` numbers for worst case scenario
			for i in 0..T::MaxGenerateRandom::get() {
				Lottery::<T>::generate_random_number(i);
			}
			// Start lottery has block 15 configured for payout
			Lottery::<T>::on_initialize(15u32.into());
		}

		assert!(crate::Lottery::<T>::get().is_none());
		assert_eq!(TicketsCount::<T>::get(), 0);
		assert_eq!(Lottery::<T>::pot().1, 0u32.into());
		assert!(!T::Currency::free_balance(&winner).is_zero());

		Ok(())
	}

	#[benchmark]
	fn on_initialize_repeat() -> Result<(), BenchmarkError> {
		setup_lottery::<T>(true)?;
		let winner = account("winner", 0, 0);
		// User needs more than min balance to get ticket
		T::Currency::make_free_balance_be(&winner, T::Currency::minimum_balance() * 10u32.into());
		// Make sure lottery account has at least min balance too
		let lottery_account = Lottery::<T>::account_id();
		T::Currency::make_free_balance_be(
			&lottery_account,
			T::Currency::minimum_balance() * 10u32.into(),
		);
		// Buy a ticket
		let call = frame_system::Call::<T>::remark { remark: vec![] };
		Lottery::<T>::buy_ticket(RawOrigin::Signed(winner.clone()).into(), Box::new(call.into()))?;
		// Kill user account for worst case
		T::Currency::make_free_balance_be(&winner, 0u32.into());
		// Assert that lotto is set up for winner
		assert_eq!(TicketsCount::<T>::get(), 1);
		assert!(!Lottery::<T>::pot().1.is_zero());

		#[block]
		{
			// Generate `MaxGenerateRandom` numbers for worst case scenario
			for i in 0..T::MaxGenerateRandom::get() {
				Lottery::<T>::generate_random_number(i);
			}
			// Start lottery has block 15 configured for payout
			Lottery::<T>::on_initialize(15u32.into());
		}

		assert!(crate::Lottery::<T>::get().is_some());
		assert_eq!(LotteryIndex::<T>::get(), 2);
		assert_eq!(TicketsCount::<T>::get(), 0);
		assert_eq!(Lottery::<T>::pot().1, 0u32.into());
		assert!(!T::Currency::free_balance(&winner).is_zero());

		Ok(())
	}

	impl_benchmark_test_suite!(Lottery, crate::mock::new_test_ext(), crate::mock::Test);
}
