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

use super::*;
use crate::{pallet as pallet_asset_rate, Pallet as AssetRate};

use frame_benchmarking::v2::*;
use frame_support::assert_ok;
use frame_system::RawOrigin;

const ASSET_ID: u32 = 1;

fn default_conversion_rate() -> FixedU128 {
	FixedU128::from_u32(1u32)
}

#[benchmarks(where <T as Config>::AssetId: From<u32>)]
mod benchmarks {
	use super::*;

	#[benchmark]
	fn create() -> Result<(), BenchmarkError> {
		let asset_id: T::AssetId = ASSET_ID.into();
		#[extrinsic_call]
		_(RawOrigin::Root, asset_id.clone(), default_conversion_rate());

		assert_eq!(
			pallet_asset_rate::ConversionRateToNative::<T>::get(asset_id),
			Some(default_conversion_rate())
		);
		Ok(())
	}

	#[benchmark]
	fn update() -> Result<(), BenchmarkError> {
		let asset_id: T::AssetId = ASSET_ID.into();
		assert_ok!(AssetRate::<T>::create(
			RawOrigin::Root.into(),
			asset_id.clone(),
			default_conversion_rate()
		));

		#[extrinsic_call]
		_(RawOrigin::Root, asset_id.clone(), FixedU128::from_u32(2));

		assert_eq!(
			pallet_asset_rate::ConversionRateToNative::<T>::get(asset_id),
			Some(FixedU128::from_u32(2))
		);
		Ok(())
	}

	#[benchmark]
	fn remove() -> Result<(), BenchmarkError> {
		let asset_id: T::AssetId = ASSET_ID.into();
		assert_ok!(AssetRate::<T>::create(
			RawOrigin::Root.into(),
			ASSET_ID.into(),
			default_conversion_rate()
		));

		#[extrinsic_call]
		_(RawOrigin::Root, asset_id.clone());

		assert!(pallet_asset_rate::ConversionRateToNative::<T>::get(asset_id).is_none());
		Ok(())
	}

	impl_benchmark_test_suite! { AssetRate, crate::mock::new_test_ext(), crate::mock::Test }
}
