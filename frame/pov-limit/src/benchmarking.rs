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

//! Pov-limit pallet benchmarking.

#[cfg(feature = "runtime-benchmarks")]
use super::*;

use frame_benchmarking::benchmarks;
use frame_system::RawOrigin as SystemOrigin;

use crate::Pallet as PovLimit;

benchmarks! {
	hash_value {

	}: {
		PovLimit::<T>::hash_value(1u64);
	}

	on_idle {
		let _ = PovLimit::<T>::set_compute(SystemOrigin::Root.into(), Perbill::from_percent(100));
		let _ = PovLimit::<T>::set_storage(SystemOrigin::Root.into(), 10_000);
	}: {
		PovLimit::<T>::on_idle(0u32.into(), Weight::from_ref_time(20_000_000));
	}

	impl_benchmark_test_suite!(PovLimit, crate::mock::new_test_ext(), crate::mock::Test);
}
