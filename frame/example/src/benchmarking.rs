// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Benchmarking for pallet-example.

#![cfg(feature = "runtime-benchmarks")]

use crate::*;
use frame_benchmarking::{benchmarks, whitelisted_caller, impl_benchmark_test_suite};
use frame_system::RawOrigin;

benchmarks!{
	// This will measure the execution time of `accumulate_dummy` for b in [1..1000] range.
	accumulate_dummy {
		let b in 1 .. 1000;
		// The caller account is whitelisted for DB reads/write by the benchmarking macro.
		let caller: T::AccountId = whitelisted_caller();
	}: _(RawOrigin::Signed(caller), b.into())

	// This will measure the execution time of `set_dummy` for b in [1..1000] range.
	set_dummy {
		let b in 1 .. 1000;
	}: _(RawOrigin::Root, b.into())

	// This will measure the execution time of sorting a vector.
	sort_vector {
		let x in 0 .. 10000;
		let mut m = Vec::<u32>::new();
		for i in (0..x).rev() {
			m.push(i);
		}
	}: {
		m.sort();
	}
}

impl_benchmark_test_suite!(Pallet, crate::tests::new_test_ext(), crate::tests::Test);
