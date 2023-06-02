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

use super::{Pallet as TxPause, *};
use frame_benchmarking::v2::*;

#[benchmarks]
mod benchmarks {
	use super::*;

	#[benchmark]
	fn pause() {
		let origin = T::PauseOrigin::try_successful_origin()
			.expect("Tx-pause pallet is not usable without pause origin");
		let full_name = name::<T>();

		#[extrinsic_call]
		_(origin as T::RuntimeOrigin, full_name.clone());

		assert!(PausedCalls::<T>::get(full_name).is_some());
	}

	#[benchmark]
	fn unpause() {
		let unpause_origin = T::UnpauseOrigin::try_successful_origin()
			.expect("Tx-pause pallet is not usable without pause origin");
		let full_name = name::<T>();
		TxPause::<T>::do_pause(full_name.clone()).unwrap();

		#[extrinsic_call]
		_(unpause_origin as T::RuntimeOrigin, full_name.clone());

		assert!(PausedCalls::<T>::get(full_name).is_none());
	}

	impl_benchmark_test_suite!(TxPause, crate::mock::new_test_ext(), crate::mock::Test);
}

/// Longest possible name.
fn name<T: Config>() -> RuntimeCallNameOf<T> {
	let max_len = T::MaxNameLen::get() as usize;
	(vec![1; max_len].try_into().unwrap(), vec![1; max_len].try_into().unwrap())
}
