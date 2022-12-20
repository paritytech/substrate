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

//! Dex pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_support::{
	assert_ok,
	storage::bounded_vec::BoundedVec,
	traits::{
		fungible::Unbalanced,
		fungibles::{Create, Mutate},
	},
};
use frame_system::RawOrigin as SystemOrigin;
use sp_runtime::traits::{Bounded, StaticLookup};
use sp_std::prelude::*;

use crate::Pallet as Dex;

const INITIAL_ASSET_BALANCE: u64 = 1_000_000_000;
type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

fn get_lp_token_id<T: Config>() -> T::PoolAssetId
where
	T::PoolAssetId: Into<u32>,
{
	let next_id: u32 = Dex::<T>::get_next_pool_asset_id().into();
	(next_id - 1).into()
}

fn create_asset<T: Config>(asset: MultiAssetId<T::AssetId>) -> (T::AccountId, AccountIdLookupOf<T>)
where
	T::AssetBalance: From<u64>,
	T::Currency: Unbalanced<T::AccountId>,
	T::Assets: Create<T::AccountId> + Mutate<T::AccountId>,
{
	let caller: T::AccountId = whitelisted_caller();
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	if let MultiAssetId::Asset(asset_id) = asset {
		assert_ok!(T::Currency::set_balance(&caller, BalanceOf::<T>::max_value()));
		assert_ok!(T::Assets::create(asset_id, caller.clone(), true, 1.into()));
		assert_ok!(T::Assets::mint_into(asset_id, &caller, INITIAL_ASSET_BALANCE.into()));
	}
	(caller, caller_lookup)
}

fn create_asset_and_pool<T: Config>(
	asset1: MultiAssetId<T::AssetId>,
	asset2: MultiAssetId<T::AssetId>,
) -> (T::PoolAssetId, T::AccountId, AccountIdLookupOf<T>)
where
	T::AssetBalance: From<u64>,
	T::Currency: Unbalanced<T::AccountId>,
	T::Assets: Create<T::AccountId> + Mutate<T::AccountId>,
	T::PoolAssetId: Into<u32>,
{
	let (_, _) = create_asset::<T>(asset1);
	let (caller, caller_lookup) = create_asset::<T>(asset2);

	assert_ok!(Dex::<T>::create_pool(SystemOrigin::Signed(caller.clone()).into(), asset1, asset2));
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
			T::AssetBalance: From<u64>,
			T::Currency: Unbalanced<T::AccountId>,
			T::Assets: Create<T::AccountId> + Mutate<T::AccountId>,
			T::PoolAssetId: Into<u32>,
	}

	create_pool {
		let asset1 = MultiAssetId::Native;
		let asset2 = MultiAssetId::Asset(0.into());
		let (caller, _) = create_asset::<T>(asset2);
	}: _(SystemOrigin::Signed(caller.clone()), asset1, asset2)
	verify {
		let lp_token = get_lp_token_id::<T>();
		let pool_id = (asset1, asset2);
		assert_last_event::<T>(Event::PoolCreated { creator: caller.clone(), pool_id, lp_token }.into());
	}

	add_liquidity {
		let asset1 = MultiAssetId::Native;
		let asset2 = MultiAssetId::Asset(0.into());
		let (lp_token, caller, _) = create_asset_and_pool::<T>(asset1, asset2);
		let deadline = T::BlockNumber::max_value();
	}: _(SystemOrigin::Signed(caller.clone()), asset1, asset2, 10.into(), 10.into(), 10.into(), 10.into(), caller.clone(), deadline, false)
	verify {
		let pool_id = (asset1, asset2);
		assert_last_event::<T>(Event::LiquidityAdded {
			who: caller.clone(),
			mint_to: caller.clone(),
			pool_id,
			amount1_provided: 10.into(),
			amount2_provided: 10.into(),
			lp_token,
			lp_token_minted: 9.into(),
		}.into());
	}

	remove_liquidity {
		let asset1 = MultiAssetId::Native;
		let asset2 = MultiAssetId::Asset(0.into());
		let (lp_token, caller, _) = create_asset_and_pool::<T>(asset1, asset2);
		let deadline = T::BlockNumber::max_value();

		Dex::<T>::add_liquidity(
			SystemOrigin::Signed(caller.clone()).into(),
			asset1,
			asset2,
			10.into(),
			10.into(),
			10.into(),
			10.into(),
			caller.clone(),
			deadline,
			false,
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), asset1, asset2, 8.into(), 1.into(), 1.into(), caller.clone(), deadline)
	verify {
		let pool_id = (asset1, asset2);
		assert_last_event::<T>(Event::LiquidityRemoved {
			who: caller.clone(),
			withdraw_to: caller.clone(),
			pool_id,
			amount1: 8.into(),
			amount2: 8.into(),
			lp_token,
			lp_token_burned: 8.into(),
		}.into());
	}

	swap_exact_tokens_for_tokens {
		let asset1 = MultiAssetId::Native;
		let asset2 = MultiAssetId::Asset(0.into());
		let asset3 = MultiAssetId::Asset(1.into());
		let (_, caller, _) = create_asset_and_pool::<T>(asset1, asset2);
		let (_, _) = create_asset::<T>(asset3);
		Dex::<T>::create_pool(SystemOrigin::Signed(caller.clone()).into(), asset2, asset3)?;
		let deadline = T::BlockNumber::max_value();
		let path: BoundedVec<_, T::MaxSwapPathLength> =
			BoundedVec::try_from(vec![asset1, asset2, asset3]).unwrap();

		Dex::<T>::add_liquidity(
			SystemOrigin::Signed(caller.clone()).into(),
			asset1,
			asset2,
			10000.into(),
			200.into(),
			10.into(),
			10.into(),
			caller.clone(),
			deadline,
			false,
		)?;
		Dex::<T>::add_liquidity(
			SystemOrigin::Signed(caller.clone()).into(),
			asset2,
			asset3,
			200.into(),
			2000.into(),
			10.into(),
			10.into(),
			caller.clone(),
			deadline,
			false,
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), path.clone(), 500.into(), 80.into(), caller.clone(), deadline, false)
	verify {
		let pool_id = (asset1, asset2);
		assert_last_event::<T>(Event::SwapExecuted {
			who: caller.clone(),
			send_to: caller.clone(),
			path,
			amount_in: 500.into(),
			amount_out: 85.into(),
		}.into());
	}

	swap_tokens_for_exact_tokens {
		let asset1 = MultiAssetId::Native;
		let asset2 = MultiAssetId::Asset(0.into());
		let asset3 = MultiAssetId::Asset(1.into());
		let (_, caller, _) = create_asset_and_pool::<T>(asset1, asset2);
		let (_, _) = create_asset::<T>(asset3);
		Dex::<T>::create_pool(SystemOrigin::Signed(caller.clone()).into(), asset2, asset3)?;
		let deadline = T::BlockNumber::max_value();
		let path: BoundedVec<_, T::MaxSwapPathLength> =
			BoundedVec::try_from(vec![asset1, asset2, asset3]).unwrap();

		Dex::<T>::add_liquidity(
			SystemOrigin::Signed(caller.clone()).into(),
			asset1,
			asset2,
			10000.into(),
			200.into(),
			10.into(),
			10.into(),
			caller.clone(),
			deadline,
			false,
		)?;
		Dex::<T>::add_liquidity(
			SystemOrigin::Signed(caller.clone()).into(),
			asset2,
			asset3,
			200.into(),
			2000.into(),
			10.into(),
			10.into(),
			caller.clone(),
			deadline,
			false,
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), path.clone(), 100.into(), 1000.into(), caller.clone(), deadline, false)
	verify {
		let pool_id = (asset1, asset2);
		assert_last_event::<T>(Event::SwapExecuted {
			who: caller.clone(),
			send_to: caller.clone(),
			path,
			amount_in: 584.into(),
			amount_out: 100.into(),
		}.into());
	}

	impl_benchmark_test_suite!(Dex, crate::mock::new_test_ext(), crate::mock::Test);
}
