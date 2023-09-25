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

use codec::Encode;
use frame_benchmarking::v2::*;
use frame_support::assert_ok;
use frame_system::RawOrigin;
use sp_core::crypto::FromEntropy;
use sp_std::vec;

/// Trait describing the factory function for the `AssetKind` parameter.
pub trait AssetKindFactory<AssetKind> {
	fn create_asset_kind(seed: u32) -> AssetKind;
}
impl<AssetKind> AssetKindFactory<AssetKind> for ()
where
	AssetKind: FromEntropy,
{
	fn create_asset_kind(seed: u32) -> AssetKind {
		AssetKind::from_entropy(&mut seed.encode().as_slice()).unwrap()
	}
}

const SEED: u32 = 1;

fn default_conversion_rate() -> FixedU128 {
	FixedU128::from_u32(1u32)
}

#[benchmarks]
mod benchmarks {
	use super::*;

	#[benchmark]
	fn create() -> Result<(), BenchmarkError> {
		let asset_kind: T::AssetKind = T::BenchmarkHelper::create_asset_kind(SEED);
		#[extrinsic_call]
		_(RawOrigin::Root, asset_kind.clone(), default_conversion_rate());

		assert_eq!(
			pallet_asset_rate::ConversionRateToNative::<T>::get(asset_kind),
			Some(default_conversion_rate())
		);
		Ok(())
	}

	#[benchmark]
	fn update() -> Result<(), BenchmarkError> {
		let asset_kind: T::AssetKind = T::BenchmarkHelper::create_asset_kind(SEED);
		assert_ok!(AssetRate::<T>::create(
			RawOrigin::Root.into(),
			asset_kind.clone(),
			default_conversion_rate()
		));

		#[extrinsic_call]
		_(RawOrigin::Root, asset_kind.clone(), FixedU128::from_u32(2));

		assert_eq!(
			pallet_asset_rate::ConversionRateToNative::<T>::get(asset_kind),
			Some(FixedU128::from_u32(2))
		);
		Ok(())
	}

	#[benchmark]
	fn remove() -> Result<(), BenchmarkError> {
		let asset_kind: T::AssetKind = T::BenchmarkHelper::create_asset_kind(SEED);
		assert_ok!(AssetRate::<T>::create(
			RawOrigin::Root.into(),
			asset_kind.clone(),
			default_conversion_rate()
		));

		#[extrinsic_call]
		_(RawOrigin::Root, asset_kind.clone());

		assert!(pallet_asset_rate::ConversionRateToNative::<T>::get(asset_kind).is_none());
		Ok(())
	}

	impl_benchmark_test_suite! { AssetRate, crate::mock::new_test_ext(), crate::mock::Test }
}
