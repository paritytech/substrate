// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

// Benchmarks for Utility Pallet

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_system::{RawOrigin, EventRecord};
use frame_benchmarking::{benchmarks, account};

const SEED: u32 = 0;

fn assert_last_event<T: Trait>(generic_event: <T as Trait>::Event) {
	let events = frame_system::Module::<T>::events();
	let system_event: <T as frame_system::Trait>::Event = generic_event.into();
	// compare to the last event record
	let EventRecord { event, .. } = &events[events.len() - 1];
	assert_eq!(event, &system_event);
}

benchmarks! {
	_ { }

	batch {
		let c in 0 .. 1000;
		let mut calls: Vec<<T as Trait>::Call> = Vec::new();
		for i in 0 .. c {
			let call = frame_system::Call::remark(vec![]).into();
			calls.push(call);
		}
		let caller = account("caller", 0, SEED);
	}: _(RawOrigin::Signed(caller), calls)
	verify {
		assert_last_event::<T>(Event::BatchCompleted.into())
	}

	as_derivative {
		let u in 0 .. 1000;
		let caller = account("caller", u, SEED);
		let call = Box::new(frame_system::Call::remark(vec![]).into());
	}: _(RawOrigin::Signed(caller), u as u16, call)
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_batch::<Test>());
			assert_ok!(test_benchmark_as_derivative::<Test>());
		});
	}
}
