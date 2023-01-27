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

//! Glutton pallet benchmarking.

#[cfg(feature = "runtime-benchmarks")]
use super::*;

use frame_benchmarking::benchmarks;
use frame_support::{pallet_prelude::*, weights::constants::*};
use frame_system::RawOrigin as SystemOrigin;

use crate::Pallet as Glutton;
use frame_system::Pallet as System;

benchmarks! {
	waste_ref_time {
		let n in 0 .. 1024;
	}: {
		Glutton::<T>::waste_ref_time(n);
	}

	waste_proof_size_some {
		let n in 0 .. 1024;

		(0..n).for_each(|i| TrashData::<T>::insert(i, i));
	}: {
		TrashData::<T>::get(n);
	}

	waste_proof_size_none {
		let n in 0 .. 1024;
	}: {
		TrashData::<T>::get(n);
	}

	on_idle {
		(0..5000).for_each(|i| TrashData::<T>::insert(i, i));
		let _ = Glutton::<T>::set_compute(SystemOrigin::Root.into(), Perbill::from_percent(100));
		let _ = Glutton::<T>::set_storage(SystemOrigin::Root.into(), Perbill::from_percent(100));
	}: {
		let weight = Glutton::<T>::on_idle(System::<T>::block_number(), Weight::from_parts(WEIGHT_REF_TIME_PER_MILLIS * 10, WEIGHT_PROOF_SIZE_PER_MB));
	}

	empty_on_idle {
		let _ = Glutton::<T>::set_compute(SystemOrigin::Root.into(), Perbill::from_percent(100));
		let _ = Glutton::<T>::set_storage(SystemOrigin::Root.into(), Perbill::from_percent(100));
	}: {
		let weight = Glutton::<T>::on_idle(System::<T>::block_number(), T::DbWeight::get().reads(1));
	}

	impl_benchmark_test_suite!(Glutton, crate::mock::new_test_ext(), crate::mock::Test);
}
