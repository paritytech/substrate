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

//! Benchmarking for `pallet-example-basic`.

// Only enable this module for benchmarking.
#![cfg(feature = "runtime-benchmarks")]

use crate::*;
use frame_benchmarking::v1::{
	impl_benchmark_test_suite,
	v2::{benchmarks, Linear},
	whitelisted_caller,
};
use frame_system::RawOrigin;

// To actually run this benchmark on pallet-example-basic, we need to put this pallet into the
//   runtime and compile it with `runtime-benchmarks` feature. The detail procedures are
//   documented at:
//   https://docs.substrate.io/reference/how-to-guides/weights/add-benchmarks/
//
// The auto-generated weight estimate of this pallet is copied over to the `weights.rs` file.
// The exact command of how the estimate generated is printed at the top of the file.

// Details on using the benchmarks macro can be seen at:
//   https://paritytech.github.io/substrate/master/frame_benchmarking/trait.Benchmarking.html#tymethod.benchmarks
#[benchmarks]
mod benchmarks {
	use super::*;

	// This will measure the execution time of `set_dummy`.
	#[benchmark]
	fn set_dummy_benchmark() {
		// This is the benchmark setup phase.
		// `set_dummy` is a constant time function, hence we hard-code some random value here.
		let value = 1000u32.into();
		#[extrinsic_call]
		set_dummy(RawOrigin::Root, value); // The execution phase is just running `set_dummy` extrinsic call

		// This is the optional benchmark verification phase, asserting certain states.
		assert_eq!(Pallet::<T>::dummy(), Some(value))
	}

	// This will measure the execution time of `accumulate_dummy`.
	// The benchmark execution phase is shorthanded. When the name of the benchmark case is the same
	// as the extrinsic call. `_(...)` is used to represent the extrinsic name.
	// The benchmark verification phase is omitted.
	#[benchmark]
	fn accumulate_dummy() {
		let value = 1000u32.into();
		// The caller account is whitelisted for DB reads/write by the benchmarking macro.
		let caller: T::AccountId = whitelisted_caller();

		// You can use `_` if the name of the Call matches the benchmark name.
		#[extrinsic_call]
		_(RawOrigin::Signed(caller), value);
	}

	/// You can write helper functions in here since its a normal Rust module.
	fn setup_vector(len: u32) -> Vec<u32> {
		let mut vector = Vec::<u32>::new();
		for i in (0..len).rev() {
			vector.push(i);
		}
		vector
	}

	// This will measure the execution time of sorting a vector.
	//
	// Define `x` as a linear component with range `[0, =10_000]`. This means that the benchmarking
	// will assume that the weight grows at a linear rate depending on `x`.
	#[benchmark]
	fn sort_vector(x: Linear<0, 10_000>) {
		let mut vector = setup_vector(x);

		// The benchmark execution phase could also be a closure with custom code:
		#[block]
		{
			vector.sort();
		}

		// Check that it was sorted correctly. This will not be benchmarked and is just for
		// verification.
		vector.windows(2).for_each(|w| assert!(w[0] <= w[1]));
	}

	// This line generates test cases for benchmarking, and could be run by:
	//   `cargo test -p pallet-example-basic --all-features`, you will see one line per case:
	//   `test benchmarking::bench_sort_vector ... ok`
	//   `test benchmarking::bench_accumulate_dummy ... ok`
	//   `test benchmarking::bench_set_dummy_benchmark ... ok` in the result.
	//
	// The line generates three steps per benchmark, with repeat=1 and the three steps are
	//   [low, mid, high] of the range.
	impl_benchmark_test_suite!(Pallet, crate::tests::new_test_ext(), crate::tests::Test);
}
