// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

// Benchmarks for AssetTxPayment Pallet

#![cfg(feature = "runtime-benchmarks")]

use super::*;
#[allow(unused_imports)] // benchmarks
use crate::Pallet as AssetTxPayment;
use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_system::RawOrigin;

benchmarks! {
	set_payment_asset {
		let caller: T::AccountId = whitelisted_caller();
		// NOTE: best effort without refactoring to support runtime for tests (need asset_id)
	}: _(RawOrigin::Signed(caller.clone()), caller.clone(), <_>::default())
	verify {
		let actual = <PaymentAssets::<T>>::get(&caller);
		assert_eq!(actual, None);
	}
	impl_benchmark_test_suite!(AssetTxPayment, crate::tests::new_test_ext(), crate::tests::Runtime);
}
