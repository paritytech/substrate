// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, whitelisted_caller};
use sp_runtime::traits::Bounded;

use crate::Module as Lottery;

// Set up and start a lottery
fn start_lottery<T: Trait>() -> Result<(), &'static str> {
	let price = T::Currency::minimum_balance();
	let start = 0.into();
	let end = 10.into();
	let payout = 15.into();
	// Calls will be maximum length...
	let mut calls = vec![
		frame_system::Call::<T>::set_code(vec![]).into();
		T::MaxCalls::get().saturating_sub(1)
	];
	// Last call will be the match for worst case scenario.
	calls.push(frame_system::Call::<T>::remark(vec![]).into());
	Lottery::<T>::setup_lottery(RawOrigin::Root.into(), price, start, end, payout, calls)?;
	Ok(())
}

benchmarks! {
	_ { }

	setup_lottery {
		let price = BalanceOf::<T>::max_value();
		let start = 0.into();
		let end = 10.into();
		let payout = 15.into();
		let calls = vec![
			frame_system::Call::<T>::remark(vec![]).into(),
		];

	// 	let call = Call::<T>::setup_lottery(price, start, end, payout, calls);
	// 	let origin = T::ManagerOrigin::successful_origin();

	// 	// use success origin
	// }: { call.dispatch_bypass_filter(origin)? }
	}: _(RawOrigin::Root, price, start, end, payout, calls)
	verify {
		assert!(crate::Lottery::<T>::get().is_some());
	}

	buy_ticket {
		let caller = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
		start_lottery::<T>()?;
		// force user to have a long vec of calls participating
		let set_code_index: CallIndex = Lottery::<T>::call_to_index(
			&frame_system::Call::<T>::set_code(vec![]).into()
		)?;
		let already_called: Vec<CallIndex> = vec![
			set_code_index;
			T::MaxCalls::get().saturating_sub(1)
		];
		Participants::<T>::insert(&caller, already_called);

		let call = frame_system::Call::<T>::remark(vec![]);
	}: _(RawOrigin::Signed(caller), call.into())
	verify {
		assert_eq!(TicketsCount::get(), 1);
	}

	on_initialize {

	}: {

	}

}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mock::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_setup_lottery::<Test>());
			assert_ok!(test_benchmark_buy_ticket::<Test>());
		});
	}
}
