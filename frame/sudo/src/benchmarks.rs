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

//! Sudo pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_system::EventRecord;

fn assert_last_event<T: Trait>(generic_event: <T as Trait>::Event) {
	let events = frame_system::Module::<T>::events();
	let system_event: <T as frame_system::Trait>::Event = generic_event.into();
	// compare to the last event record
	let EventRecord { event, .. } = &events[events.len() - 1];
	assert_eq!(event, &system_event);
}

benchmarks! {
	_ { }

	sudo {
		let c in 0 .. T::MaximumBlockLength::get();
		let caller: T::AccountId = whitelisted_caller();
		Key::<T>::put(caller.clone());

		let bytes = vec![0u8; c as usize];
		let noop = frame_system::Call::<T>::noop_root(bytes);

	}: _(RawOrigin::Signed(caller), Box::new(noop.into()))
	verify {
		assert_last_event::<T>(RawEvent::Sudid(Ok(())).into())
	}

}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mock::{Test, new_test_ext};
	use frame_support::assert_ok;

	#[test]
	fn sudo() {
		new_test_ext(1).execute_with(|| {
			assert_ok!(test_benchmark_sudo::<Test>());
		});
	}

}
