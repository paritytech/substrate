// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

#![cfg(feature = "runtime-benchmarks")]

use super::{Call as SafeModeCall, Pallet as SafeMode, *};

use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_support::traits::Currency;
use frame_system::{Pallet as System, RawOrigin};
use sp_runtime::traits::Bounded;

benchmarks! {
  activate {
		let caller: T::AccountId = whitelisted_caller();
	let origin = RawOrigin::Signed(caller.clone());
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
  }: activate(origin)
  verify {
		assert_eq!(
			SafeMode::<T>::activated().unwrap(),
			System::<T>::block_number() + T::ActivateDuration::get()
		);
  }

//  force_activate {
//   /* code to set the initial state */
//   }: {
//     /* code to test the function benchmarked */
//   }
//   verify {
//     /* optional verification */
//   }

// extend {
//   /* code to set the initial state */
//   }: {
//     /* code to test the function benchmarked */
//   }
//   verify {
//     /* optional verification */
//   }

// force_extend {
//     /* code to set the initial state */
//   }: {
//     /* code to test the function benchmarked */
//   }
//   verify {
//     /* optional verification */
//   }

// force_inactivate {
//     /* code to set the initial state */
//   }: {
//     /* code to test the function benchmarked */
//   }
//   verify {
//     /* optional verification */
//   }

// repay_stake {
//     /* code to set the initial state */
//   }: {
//     /* code to test the function benchmarked */
//   }
//   verify {
//     /* optional verification */
//   }

// slash_stake {
//     /* code to set the initial state */
//   }: {
//     /* code to test the function benchmarked */
//   }
//   verify {
//     /* optional verification */
//   }

  impl_benchmark_test_suite!(SafeMode, crate::mock::new_test_ext(), crate::mock::Test);
}
