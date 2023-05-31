// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use super::*;

use frame_benchmarking::v2::*;
use frame_support::migrations::STEPPED_MIGRATION_CURSOR_LEN as CURSOR_LEN;
use frame_system::{Pallet as System, RawOrigin};

#[benchmarks]
mod benches {
	use super::*;
	use frame_support::traits::Hooks;

	#[benchmark]
	fn on_runtime_upgrade_bail() {
		Cursor::<T>::set(Some(cursor(0)));
		assert!(Cursor::<T>::exists());

		#[block]
		{
			Pallet::<T>::on_runtime_upgrade();
		}
	}

	#[benchmark]
	fn on_runtime_upgrade() {
		assert!(!Cursor::<T>::exists());

		#[block]
		{
			Pallet::<T>::on_runtime_upgrade();
		}
	}

	#[benchmark]
	fn on_init_loop_base() {
		Cursor::<T>::set(Some(cursor(0)));
		System::<T>::set_block_number(1u32.into());
		Pallet::<T>::on_runtime_upgrade();

		#[block]
		{
			Pallet::<T>::on_initialize(1u32.into());
		}
	}

	/// Benchmarks the slowest path of `change_value`.
	#[benchmark]
	fn force_set_cursor() {
		Cursor::<T>::set(Some(cursor(0)));

		#[extrinsic_call]
		_(RawOrigin::Root, Some(cursor(1)));
	}

	fn cursor(i: u32) -> MigrationCursor {
		MigrationCursor::Active(
			u32::MAX - i,
			Some(vec![1u8; CURSOR_LEN as usize].try_into().expect("Static length is good")),
		)
	}

	// Implements a test for each benchmark. Execute with:
	// `cargo test -p pallet-migrations --features runtime-benchmarks`.
	impl_benchmark_test_suite!(Pallet, crate::mock::new_test_ext(), crate::mock::Test);
}
