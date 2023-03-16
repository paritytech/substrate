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

//! The crate's benchmarks.

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use crate::Pallet as TreasuryOracle;
use frame_benchmarking::v2::*;
use frame_support::assert_ok;
use frame_system::RawOrigin;

const ASSET_ID: u32 = 1;

fn default_conversion_rate() -> FixedU128 {
	FixedU128::from_float(0.1)
}

#[benchmarks(where <T as Config>::AssetId: From<u32>)]
mod benchmarks {
	use super::*;

	#[benchmark]
	fn create() -> Result<(), BenchmarkError> {
		#[extrinsic_call]
		_(RawOrigin::Root, ASSET_ID.into(), default_conversion_rate());

		assert_eq!(
			TreasuryOracle::<T>::conversion_rate_to_native::<<T as Config>::AssetId>(
				ASSET_ID.into()
			),
			Some(default_conversion_rate())
		);
		Ok(())
	}

	#[benchmark]
	fn update() -> Result<(), BenchmarkError> {
		assert_ok!(TreasuryOracle::<T>::create(
			RawOrigin::Root.into(),
			ASSET_ID.into(),
			default_conversion_rate()
		));

		#[extrinsic_call]
		_(RawOrigin::Root, ASSET_ID.into(), FixedU128::from_float(1.5));

		assert_eq!(
			TreasuryOracle::<T>::conversion_rate_to_native::<<T as Config>::AssetId>(
				ASSET_ID.into()
			),
			Some(FixedU128::from_float(1.5))
		);
		Ok(())
	}

	#[benchmark]
	fn remove() -> Result<(), BenchmarkError> {
		assert_ok!(TreasuryOracle::<T>::create(
			RawOrigin::Root.into(),
			ASSET_ID.into(),
			default_conversion_rate()
		));

		#[extrinsic_call]
		_(RawOrigin::Root, ASSET_ID.into());

		assert!(TreasuryOracle::<T>::conversion_rate_to_native::<<T as Config>::AssetId>(
			ASSET_ID.into()
		)
		.is_none());
		Ok(())
	}

	impl_benchmark_test_suite! { TreasuryOracle, crate::mock::new_test_ext(), crate::mock::Test }
}
