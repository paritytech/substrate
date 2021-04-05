// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Benchmarks for the MMR pallet.

#![cfg_attr(not(feature = "std"), no_std)]

use crate::*;
use frame_support::traits::OnInitialize;
use frame_benchmarking::{benchmarks, impl_benchmark_test_suite};

benchmarks! {
	on_initialize {
		let x in 1 .. 1_000;

		let leaves = x as u64;
	}: {
		for b in 0..leaves {
			Module::<T>::on_initialize((b as u32).into());
		}
	} verify {
		assert_eq!(crate::NumberOfLeaves::<DefaultInstance>::get(), leaves);
	}
}

impl_benchmark_test_suite!(
	Module,
	crate::tests::new_test_ext(),
	crate::mock::Test,
);
