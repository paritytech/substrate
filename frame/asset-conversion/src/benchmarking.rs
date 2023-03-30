// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Asset Conversion pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_support::{
	assert_ok,
	storage::bounded_vec::BoundedVec,
	traits::{
		fungible::{Inspect as InspectFungible, Unbalanced},
		fungibles::{Create, Inspect, Mutate},
	},
};
use frame_system::RawOrigin as SystemOrigin;
use sp_runtime::traits::{Bounded, StaticLookup};
use sp_std::prelude::*;

use crate::Pallet as AssetConversion;

const INITIAL_ASSET_BALANCE: u128 = 1_000_000_000_000;
type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;
type BalanceOf<T> =
	<<T as Config>::Currency as InspectFungible<<T as frame_system::Config>::AccountId>>::Balance;

fn get_lp_token_id<T: Config>() -> T::PoolAssetId
where
	T::PoolAssetId: Into<u32>,
{
	let next_id: u32 = AssetConversion::<T>::get_next_pool_asset_id().into();
	(next_id - 1).into()
}

fn create_asset<T: Config>(asset: T::MultiAssetId) -> (T::AccountId, AccountIdLookupOf<T>)
where
	T::AssetBalance: From<u128>,
	T::Currency: Unbalanced<T::AccountId>,
	T::Assets: Create<T::AccountId> + Mutate<T::AccountId>,
{
	let caller: T::AccountId = whitelisted_caller();
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	if let Ok(asset_id) = T::MultiAssetIdConverter::try_convert(asset) {
		assert_ok!(T::Currency::write_balance(&caller, BalanceOf::<T>::max_value()));
		assert_ok!(T::Assets::create(asset_id, caller.clone(), true, 1.into()));
		assert_ok!(T::Assets::mint_into(asset_id, &caller, INITIAL_ASSET_BALANCE.into()));
	}
	(caller, caller_lookup)
}

fn create_asset_and_pool<T: Config>(
	asset1: T::MultiAssetId,
	asset2: T::MultiAssetId,
) -> (T::PoolAssetId, T::AccountId, AccountIdLookupOf<T>)
where
	T::AssetBalance: From<u128>,
	T::Currency: Unbalanced<T::AccountId>,
	T::Assets: Create<T::AccountId> + Mutate<T::AccountId>,
	T::PoolAssetId: Into<u32>,
{
	let (_, _) = create_asset::<T>(asset1);
	let (caller, caller_lookup) = create_asset::<T>(asset2);

	assert_ok!(AssetConversion::<T>::create_pool(
		SystemOrigin::Signed(caller.clone()).into(),
		asset1,
		asset2
	));
	let lp_token = get_lp_token_id::<T>();

	(lp_token, caller, caller_lookup)
}

fn assert_last_event<T: Config>(generic_event: <T as Config>::RuntimeEvent) {
	let events = frame_system::Pallet::<T>::events();
	let system_event: <T as frame_system::Config>::RuntimeEvent = generic_event.into();
	// compare to the last event record
	let frame_system::EventRecord { event, .. } = &events[events.len() - 1];
	assert_eq!(event, &system_event);
}

benchmarks! {
	where_clause {
		where
			T::AssetBalance: From<u128> + Into<u128>,
			T::Currency: Unbalanced<T::AccountId>,
			T::Balance: From<u128> + Into<u128>,
			T::Assets: Create<T::AccountId> + Mutate<T::AccountId>,
			T::PoolAssetId: Into<u32>,
			T::AssetId: From<u32>,
	}

	create_pool {
		let asset1 = T::MultiAssetIdConverter::get_native();
		let asset2 = T::MultiAssetIdConverter::into_multiasset_id(0_u32.into());
		let (caller, _) = create_asset::<T>(asset2);
	}: _(SystemOrigin::Signed(caller.clone()), asset1, asset2)
	verify {
		let lp_token = get_lp_token_id::<T>();
		let pool_id = (asset1, asset2);
		assert_last_event::<T>(Event::PoolCreated { creator: caller.clone(), pool_id, lp_token }.into());
	}

	add_liquidity {
		let asset1 = T::MultiAssetIdConverter::get_native();
		let asset2 = T::MultiAssetIdConverter::into_multiasset_id(0.into());
		let (lp_token, caller, _) = create_asset_and_pool::<T>(asset1, asset2);
		let ed: u128 = T::Currency::minimum_balance().into();
		let add_amount = 1000 + ed;
	}: _(SystemOrigin::Signed(caller.clone()), asset1, asset2, add_amount.into(), 1000.into(), 0.into(), 0.into(), caller.clone())
	verify {
		let pool_id = (asset1, asset2);
		let lp_minted = AssetConversion::<T>::calc_lp_amount_for_zero_supply(&add_amount.into(), &1000.into()).unwrap().into();
		assert_eq!(
			T::PoolAssets::balance(lp_token, &caller),
			lp_minted.into()
		);
		assert_eq!(
			T::Currency::balance(&AssetConversion::<T>::get_pool_account(pool_id)),
			add_amount.into()
		);
		assert_eq!(
			T::Assets::balance(0.into(), &AssetConversion::<T>::get_pool_account(pool_id)),
			1000.into()
		);
	}

	remove_liquidity {
		let asset1 = T::MultiAssetIdConverter::get_native();
		let asset2 = T::MultiAssetIdConverter::into_multiasset_id(0.into());
		let (lp_token, caller, _) = create_asset_and_pool::<T>(asset1, asset2);
		let ed: u128 = T::Currency::minimum_balance().into();
		let add_amount = 1000 + ed;
		let lp_minted = AssetConversion::<T>::calc_lp_amount_for_zero_supply(&add_amount.into(), &1000.into()).unwrap().into();
		let remove_lp_amount = lp_minted - 4;

		AssetConversion::<T>::add_liquidity(
			SystemOrigin::Signed(caller.clone()).into(),
			asset1,
			asset2,
			add_amount.into(),
			1000.into(),
			0.into(),
			0.into(),
			caller.clone(),
		)?;
		let total_supply = <T::PoolAssets as Inspect<T::AccountId>>::total_issuance(lp_token);
	}: _(SystemOrigin::Signed(caller.clone()), asset1, asset2, remove_lp_amount.into(), 0.into(), 0.into(), caller.clone())
	verify {
		let new_total_supply = <T::PoolAssets as Inspect<T::AccountId>>::total_issuance(lp_token);
		assert_eq!(
			new_total_supply,
			total_supply - remove_lp_amount.into()
		);
	}

	swap_exact_tokens_for_tokens {
		let asset1 = T::MultiAssetIdConverter::get_native();
		let asset2 = T::MultiAssetIdConverter::into_multiasset_id(0.into());
		let asset3 = T::MultiAssetIdConverter::into_multiasset_id(1.into());

		let (_, caller, _) = create_asset_and_pool::<T>(asset1, asset2);
		let (_, _) = create_asset::<T>(asset3);
		AssetConversion::<T>::create_pool(SystemOrigin::Signed(caller.clone()).into(), asset2, asset3)?;

		let path: BoundedVec<_, T::MaxSwapPathLength> =
			BoundedVec::try_from(vec![asset1, asset2, asset3]).unwrap();
		let ed: u128 = T::Currency::minimum_balance().into();
		let add_amount1 = 1000 + ed;

		AssetConversion::<T>::add_liquidity(
			SystemOrigin::Signed(caller.clone()).into(),
			asset1,
			asset2,
			add_amount1.into(),
			200.into(),
			0.into(),
			0.into(),
			caller.clone(),
		)?;
		AssetConversion::<T>::add_liquidity(
			SystemOrigin::Signed(caller.clone()).into(),
			asset2,
			asset3,
			200.into(),
			2000.into(),
			0.into(),
			0.into(),
			caller.clone(),
		)?;
		let asset1_balance = T::Currency::balance(&caller);
	}: _(SystemOrigin::Signed(caller.clone()), path.clone(), 100.into(), 1.into(), caller.clone(), false)
	verify {
		let new_asset1_balance = T::Currency::balance(&caller);
		assert_eq!(
			new_asset1_balance,
			asset1_balance - 100.into()
		);
	}

	swap_tokens_for_exact_tokens {
		let asset1 = T::MultiAssetIdConverter::get_native();
		let asset2 = T::MultiAssetIdConverter::into_multiasset_id(0.into());
		let asset3 = T::MultiAssetIdConverter::into_multiasset_id(1.into());

		let (_, caller, _) = create_asset_and_pool::<T>(asset1, asset2);
		let (_, _) = create_asset::<T>(asset3);
		AssetConversion::<T>::create_pool(SystemOrigin::Signed(caller.clone()).into(), asset2, asset3)?;

		let path: BoundedVec<_, T::MaxSwapPathLength> =
			BoundedVec::try_from(vec![asset1, asset2, asset3]).unwrap();
		let ed: u128 = T::Currency::minimum_balance().into();
		let add_amount1 = 1000 + ed;

		AssetConversion::<T>::add_liquidity(
			SystemOrigin::Signed(caller.clone()).into(),
			asset1,
			asset2,
			add_amount1.into(),
			200.into(),
			0.into(),
			0.into(),
			caller.clone(),
		)?;
		AssetConversion::<T>::add_liquidity(
			SystemOrigin::Signed(caller.clone()).into(),
			asset2,
			asset3,
			200.into(),
			2000.into(),
			0.into(),
			0.into(),
			caller.clone(),
		)?;
		let asset3_balance = T::Assets::balance(1.into(), &caller);
	}: _(SystemOrigin::Signed(caller.clone()), path.clone(), 100.into(), add_amount1.into(), caller.clone(), false)
	verify {
		let new_asset3_balance = T::Assets::balance(1.into(), &caller);
		assert_eq!(
			new_asset3_balance,
			asset3_balance + 100.into()
		);
	}

	impl_benchmark_test_suite!(AssetConversion, crate::mock::new_test_ext(), crate::mock::Test);
}
