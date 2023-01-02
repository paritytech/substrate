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

//! Nft fractionalization pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_support::{
	assert_ok,
	traits::{
		fungible::{Inspect as InspectFungible, Unbalanced},
		tokens::nonfungibles_v2::{Create, Mutate},
	},
};
use frame_system::RawOrigin as SystemOrigin;
use pallet_nfts::{CollectionConfig, CollectionSettings, ItemConfig, MintSettings};
use sp_runtime::traits::{Bounded, StaticLookup};
use sp_std::prelude::*;

use crate::Pallet as NftFractions;

type BalanceOf<T> =
	<<T as Config>::Currency as InspectFungible<<T as SystemConfig>::AccountId>>::Balance;

type CollectionConfigOf<T> = CollectionConfig<
	BalanceOf<T>,
	<T as SystemConfig>::BlockNumber,
	<T as Config>::NftCollectionId,
>;

fn default_collection_config<T: Config>() -> CollectionConfigOf<T>
where
	T::Currency: InspectFungible<T::AccountId>,
{
	CollectionConfig {
		settings: CollectionSettings::all_enabled(),
		max_supply: None,
		mint_settings: MintSettings::default(),
	}
}

fn mint_nft<T: Config>(nft_id: T::NftId) -> (T::AccountId, AccountIdLookupOf<T>)
where
	T::NftCollectionId: From<u32>,
	T::Currency: Unbalanced<T::AccountId>,
	T::Nfts: Create<T::AccountId, CollectionConfig<BalanceOf<T>, T::BlockNumber, T::NftCollectionId>>
		+ Mutate<T::AccountId, ItemConfig>,
{
	let caller: T::AccountId = whitelisted_caller();
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	assert_ok!(T::Currency::set_balance(&caller, BalanceOf::<T>::max_value()));
	assert_ok!(T::Nfts::create_collection(&caller, &caller, &default_collection_config::<T>()));
	assert_ok!(T::Nfts::mint_into(&0.into(), &nft_id, &caller, &ItemConfig::default(), true));
	(caller, caller_lookup)
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
			T::NftCollectionId: From<u32>,
			T::NftId: From<u32>,
			T::Currency: Unbalanced<T::AccountId>,
			T::Nfts: Create<T::AccountId, CollectionConfig<BalanceOf<T>, T::BlockNumber, T::NftCollectionId>>
				+ Mutate<T::AccountId, ItemConfig>,
	}

	fractionalize {
		let (caller, caller_lookup) = mint_nft::<T>(0.into());
	}: _(SystemOrigin::Signed(caller.clone()), 0.into(), 0.into(), 0.into(), caller_lookup, 1000u32.into())
	verify {
		assert_last_event::<T>(
			Event::NftFractionalized {
				nft_collection: 0.into(),
				nft: 0.into(),
				fractions: 1000u32.into(),
				asset: 0.into(),
				beneficiary: caller,
			}.into()
		);
	}

	unify {
		let (caller, caller_lookup) = mint_nft::<T>(0.into());
		NftFractions::<T>::fractionalize(
			SystemOrigin::Signed(caller.clone()).into(),
			0.into(),
			0.into(),
			0.into(),
			caller_lookup.clone(),
			1000u32.into(),
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), 0.into(), 0.into(), 0.into(), caller_lookup)
	verify {
		assert_last_event::<T>(
			Event::NftUnified {
				nft_collection: 0.into(),
				nft: 0.into(),
				asset: 0.into(),
				beneficiary: caller,
			}.into()
		);
	}

	impl_benchmark_test_suite!(NftFractions, crate::mock::new_test_ext(), crate::mock::Test);
}
