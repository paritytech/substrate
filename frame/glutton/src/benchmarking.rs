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
//!
//! Has to be compiled and run twice to calibrate on new hardware.

#[cfg(feature = "runtime-benchmarks")]
use super::*;

use frame_benchmarking::benchmarks;
use frame_support::{pallet_prelude::*, weights::constants::*};
use frame_system::RawOrigin as SystemOrigin;
use sp_runtime::{traits::One, Perbill};

use crate::Pallet as Glutton;
use frame_system::Pallet as System;

benchmarks! {
	initialize_pallet_grow {
		let n in 0 .. 1_000;
	}: {
		Glutton::<T>::initialize_pallet(SystemOrigin::Root.into(), n, None).unwrap()
	} verify {
		assert_eq!(TrashDataCount::<T>::get(), n);
	}

	initialize_pallet_shrink {
		let n in 0 .. 1_000;

		Glutton::<T>::initialize_pallet(SystemOrigin::Root.into(), n, None).unwrap();
	}: {
		Glutton::<T>::initialize_pallet(SystemOrigin::Root.into(), 0, Some(n)).unwrap()
	} verify {
		assert_eq!(TrashDataCount::<T>::get(), 0);
	}

	waste_ref_time_iter {
		let i in 0..100_000;
	}: {
		Glutton::<T>::waste_ref_time_iter(vec![0u8; 64], i);
	}

	waste_proof_size_some {
		let i in 0..5_000;

		(0..5000).for_each(|i| TrashData::<T>::insert(i, [i as u8; 1024]));
	}: {
		(0..i).for_each(|i| {
			TrashData::<T>::get(i);
		})
	}

	// For manual verification only.
	on_idle_high_proof_waste {
		(0..5000).for_each(|i| TrashData::<T>::insert(i, [i as u8; 1024]));
		let _ = Glutton::<T>::set_compute(SystemOrigin::Root.into(), One::one());
		let _ = Glutton::<T>::set_storage(SystemOrigin::Root.into(), One::one());
	}: {
		let weight = Glutton::<T>::on_idle(System::<T>::block_number(), Weight::from_parts(WEIGHT_REF_TIME_PER_MILLIS * 100, WEIGHT_PROOF_SIZE_PER_MB * 5));
	}

	// For manual verification only.
	on_idle_low_proof_waste {
		(0..5000).for_each(|i| TrashData::<T>::insert(i, [i as u8; 1024]));
		let _ = Glutton::<T>::set_compute(SystemOrigin::Root.into(), One::one());
		let _ = Glutton::<T>::set_storage(SystemOrigin::Root.into(), One::one());
	}: {
		let weight = Glutton::<T>::on_idle(System::<T>::block_number(), Weight::from_parts(WEIGHT_REF_TIME_PER_MILLIS * 100, WEIGHT_PROOF_SIZE_PER_KB * 20));
	}

	empty_on_idle {
	}: {
		// Enough weight do do nothing.
		Glutton::<T>::on_idle(System::<T>::block_number(), T::WeightInfo::empty_on_idle());
	}

	set_compute {
	}: _(SystemOrigin::Root, FixedU64::from_perbill(Perbill::from_percent(50)))

	set_storage {
	}: _(SystemOrigin::Root, FixedU64::from_perbill(Perbill::from_percent(50)))

	impl_benchmark_test_suite!(Glutton, crate::mock::new_test_ext(), crate::mock::Test);
}
