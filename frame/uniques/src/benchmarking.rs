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

//! Uniques pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_benchmarking::v1::{
	account, benchmarks_instance_pallet, whitelist_account, whitelisted_caller, BenchmarkError,
};
use frame_support::{
	traits::{EnsureOrigin, Get, UnfilteredDispatchable},
	BoundedVec,
};
use frame_system::RawOrigin as SystemOrigin;
use sp_runtime::traits::Bounded;
use sp_std::prelude::*;

use crate::Pallet as Uniques;

const SEED: u32 = 0;

fn create_collection<T: Config<I>, I: 'static>(
) -> (T::CollectionId, T::AccountId, AccountIdLookupOf<T>) {
	let caller: T::AccountId = whitelisted_caller();
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	let collection = T::Helper::collection(0);
	T::Currency::make_free_balance_be(&caller, DepositBalanceOf::<T, I>::max_value());
	assert!(Uniques::<T, I>::force_create(
		SystemOrigin::Root.into(),
		collection.clone(),
		caller_lookup.clone(),
		false,
	)
	.is_ok());
	(collection, caller, caller_lookup)
}

fn add_collection_metadata<T: Config<I>, I: 'static>() -> (T::AccountId, AccountIdLookupOf<T>) {
	let caller = Collection::<T, I>::get(T::Helper::collection(0)).unwrap().owner;
	if caller != whitelisted_caller() {
		whitelist_account!(caller);
	}
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	assert!(Uniques::<T, I>::set_collection_metadata(
		SystemOrigin::Signed(caller.clone()).into(),
		T::Helper::collection(0),
		vec![0; T::StringLimit::get() as usize].try_into().unwrap(),
		false,
	)
	.is_ok());
	(caller, caller_lookup)
}

fn mint_item<T: Config<I>, I: 'static>(
	index: u16,
) -> (T::ItemId, T::AccountId, AccountIdLookupOf<T>) {
	let caller = Collection::<T, I>::get(T::Helper::collection(0)).unwrap().admin;
	if caller != whitelisted_caller() {
		whitelist_account!(caller);
	}
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	let item = T::Helper::item(index);
	assert!(Uniques::<T, I>::mint(
		SystemOrigin::Signed(caller.clone()).into(),
		T::Helper::collection(0),
		item,
		caller_lookup.clone(),
	)
	.is_ok());
	(item, caller, caller_lookup)
}

fn add_item_metadata<T: Config<I>, I: 'static>(
	item: T::ItemId,
) -> (T::AccountId, AccountIdLookupOf<T>) {
	let caller = Collection::<T, I>::get(T::Helper::collection(0)).unwrap().owner;
	if caller != whitelisted_caller() {
		whitelist_account!(caller);
	}
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	assert!(Uniques::<T, I>::set_metadata(
		SystemOrigin::Signed(caller.clone()).into(),
		T::Helper::collection(0),
		item,
		vec![0; T::StringLimit::get() as usize].try_into().unwrap(),
		false,
	)
	.is_ok());
	(caller, caller_lookup)
}

fn add_item_attribute<T: Config<I>, I: 'static>(
	item: T::ItemId,
) -> (BoundedVec<u8, T::KeyLimit>, T::AccountId, AccountIdLookupOf<T>) {
	let caller = Collection::<T, I>::get(T::Helper::collection(0)).unwrap().owner;
	if caller != whitelisted_caller() {
		whitelist_account!(caller);
	}
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	let key: BoundedVec<_, _> = vec![0; T::KeyLimit::get() as usize].try_into().unwrap();
	assert!(Uniques::<T, I>::set_attribute(
		SystemOrigin::Signed(caller.clone()).into(),
		T::Helper::collection(0),
		Some(item),
		key.clone(),
		vec![0; T::ValueLimit::get() as usize].try_into().unwrap(),
	)
	.is_ok());
	(key, caller, caller_lookup)
}

fn assert_last_event<T: Config<I>, I: 'static>(generic_event: <T as Config<I>>::RuntimeEvent) {
	let events = frame_system::Pallet::<T>::events();
	let system_event: <T as frame_system::Config>::RuntimeEvent = generic_event.into();
	// compare to the last event record
	let frame_system::EventRecord { event, .. } = &events[events.len() - 1];
	assert_eq!(event, &system_event);
}

benchmarks_instance_pallet! {
	create {
		let collection = T::Helper::collection(0);
		let origin = T::CreateOrigin::try_successful_origin(&collection)
			.map_err(|_| BenchmarkError::Weightless)?;
		let caller = T::CreateOrigin::ensure_origin(origin.clone(), &collection).unwrap();
		whitelist_account!(caller);
		let admin = T::Lookup::unlookup(caller.clone());
		T::Currency::make_free_balance_be(&caller, DepositBalanceOf::<T, I>::max_value());
		let call = Call::<T, I>::create { collection, admin };
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_last_event::<T, I>(Event::Created { collection: T::Helper::collection(0), creator: caller.clone(), owner: caller }.into());
	}

	force_create {
		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup = T::Lookup::unlookup(caller.clone());
	}: _(SystemOrigin::Root, T::Helper::collection(0), caller_lookup, true)
	verify {
		assert_last_event::<T, I>(Event::ForceCreated { collection: T::Helper::collection(0), owner: caller }.into());
	}

	destroy {
		let n in 0 .. 1_000;
		let m in 0 .. 1_000;
		let a in 0 .. 1_000;

		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		add_collection_metadata::<T, I>();
		for i in 0..n {
			mint_item::<T, I>(i as u16);
		}
		for i in 0..m {
			add_item_metadata::<T, I>(T::Helper::item(i as u16));
		}
		for i in 0..a {
			add_item_attribute::<T, I>(T::Helper::item(i as u16));
		}
		let witness = Collection::<T, I>::get(collection.clone()).unwrap().destroy_witness();
	}: _(SystemOrigin::Signed(caller), collection.clone(), witness)
	verify {
		assert_last_event::<T, I>(Event::Destroyed { collection: collection.clone() }.into());
	}

	mint {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let item = T::Helper::item(0);
	}: _(SystemOrigin::Signed(caller.clone()), collection.clone(), item, caller_lookup)
	verify {
		assert_last_event::<T, I>(Event::Issued { collection: collection.clone(), item, owner: caller }.into());
	}

	burn {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
	}: _(SystemOrigin::Signed(caller.clone()), collection.clone(), item, Some(caller_lookup))
	verify {
		assert_last_event::<T, I>(Event::Burned { collection: collection.clone(), item, owner: caller }.into());
	}

	transfer {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);

		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller.clone()), collection.clone(), item, target_lookup)
	verify {
		assert_last_event::<T, I>(Event::Transferred { collection: collection.clone(), item, from: caller, to: target }.into());
	}

	redeposit {
		let i in 0 .. 5_000;
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let items = (0..i).map(|x| mint_item::<T, I>(x as u16).0).collect::<Vec<_>>();
		Uniques::<T, I>::force_item_status(
			SystemOrigin::Root.into(),
			collection.clone(),
			caller_lookup.clone(),
			caller_lookup.clone(),
			caller_lookup.clone(),
			caller_lookup,
			true,
			false,
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), collection.clone(), items.clone())
	verify {
		assert_last_event::<T, I>(Event::Redeposited { collection: collection.clone(), successful_items: items }.into());
	}

	freeze {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
	}: _(SystemOrigin::Signed(caller.clone()), T::Helper::collection(0), T::Helper::item(0))
	verify {
		assert_last_event::<T, I>(Event::Frozen { collection: T::Helper::collection(0), item: T::Helper::item(0) }.into());
	}

	thaw {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		Uniques::<T, I>::freeze(
			SystemOrigin::Signed(caller.clone()).into(),
			collection.clone(),
			item,
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), collection.clone(), item)
	verify {
		assert_last_event::<T, I>(Event::Thawed { collection: collection.clone(), item }.into());
	}

	freeze_collection {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
	}: _(SystemOrigin::Signed(caller.clone()), collection.clone())
	verify {
		assert_last_event::<T, I>(Event::CollectionFrozen { collection: collection.clone() }.into());
	}

	thaw_collection {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let origin = SystemOrigin::Signed(caller.clone()).into();
		Uniques::<T, I>::freeze_collection(origin, collection.clone())?;
	}: _(SystemOrigin::Signed(caller.clone()), collection.clone())
	verify {
		assert_last_event::<T, I>(Event::CollectionThawed { collection: collection.clone() }.into());
	}

	transfer_ownership {
		let (collection, caller, _) = create_collection::<T, I>();
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
		T::Currency::make_free_balance_be(&target, T::Currency::minimum_balance());
		let origin = SystemOrigin::Signed(target.clone()).into();
		Uniques::<T, I>::set_accept_ownership(origin, Some(collection.clone()))?;
	}: _(SystemOrigin::Signed(caller), collection.clone(), target_lookup)
	verify {
		assert_last_event::<T, I>(Event::OwnerChanged { collection: collection.clone(), new_owner: target }.into());
	}

	set_team {
		let (collection, caller, _) = create_collection::<T, I>();
		let target0 = T::Lookup::unlookup(account("target", 0, SEED));
		let target1 = T::Lookup::unlookup(account("target", 1, SEED));
		let target2 = T::Lookup::unlookup(account("target", 2, SEED));
	}: _(SystemOrigin::Signed(caller), collection.clone(), target0, target1, target2)
	verify {
		assert_last_event::<T, I>(Event::TeamChanged{
			collection: collection.clone(),
			issuer: account("target", 0, SEED),
			admin: account("target", 1, SEED),
			freezer: account("target", 2, SEED),
		}.into());
	}

	force_item_status {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let origin =
			T::ForceOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
		let call = Call::<T, I>::force_item_status {
			collection: collection.clone(),
			owner: caller_lookup.clone(),
			issuer: caller_lookup.clone(),
			admin: caller_lookup.clone(),
			freezer: caller_lookup,
			free_holding: true,
			is_frozen: false,
		};
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_last_event::<T, I>(Event::ItemStatusChanged { collection: collection.clone() }.into());
	}

	set_attribute {
		let key: BoundedVec<_, _> = vec![0u8; T::KeyLimit::get() as usize].try_into().unwrap();
		let value: BoundedVec<_, _> = vec![0u8; T::ValueLimit::get() as usize].try_into().unwrap();

		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		add_item_metadata::<T, I>(item);
	}: _(SystemOrigin::Signed(caller), collection.clone(), Some(item), key.clone(), value.clone())
	verify {
		assert_last_event::<T, I>(Event::AttributeSet { collection: collection.clone(), maybe_item: Some(item), key, value }.into());
	}

	clear_attribute {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		add_item_metadata::<T, I>(item);
		let (key, ..) = add_item_attribute::<T, I>(item);
	}: _(SystemOrigin::Signed(caller), collection.clone(), Some(item), key.clone())
	verify {
		assert_last_event::<T, I>(Event::AttributeCleared { collection: collection.clone(), maybe_item: Some(item), key }.into());
	}

	set_metadata {
		let data: BoundedVec<_, _> = vec![0u8; T::StringLimit::get() as usize].try_into().unwrap();

		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
	}: _(SystemOrigin::Signed(caller), collection.clone(), item, data.clone(), false)
	verify {
		assert_last_event::<T, I>(Event::MetadataSet { collection: collection.clone(), item, data, is_frozen: false }.into());
	}

	clear_metadata {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		add_item_metadata::<T, I>(item);
	}: _(SystemOrigin::Signed(caller), collection.clone(), item)
	verify {
		assert_last_event::<T, I>(Event::MetadataCleared { collection: collection.clone(), item }.into());
	}

	set_collection_metadata {
		let data: BoundedVec<_, _> = vec![0u8; T::StringLimit::get() as usize].try_into().unwrap();

		let (collection, caller, _) = create_collection::<T, I>();
	}: _(SystemOrigin::Signed(caller), collection.clone(), data.clone(), false)
	verify {
		assert_last_event::<T, I>(Event::CollectionMetadataSet { collection: collection.clone(), data, is_frozen: false }.into());
	}

	clear_collection_metadata {
		let (collection, caller, _) = create_collection::<T, I>();
		add_collection_metadata::<T, I>();
	}: _(SystemOrigin::Signed(caller), collection.clone())
	verify {
		assert_last_event::<T, I>(Event::CollectionMetadataCleared { collection: collection.clone() }.into());
	}

	approve_transfer {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		let delegate: T::AccountId = account("delegate", 0, SEED);
		let delegate_lookup = T::Lookup::unlookup(delegate.clone());
	}: _(SystemOrigin::Signed(caller.clone()), collection.clone(), item, delegate_lookup)
	verify {
		assert_last_event::<T, I>(Event::ApprovedTransfer { collection: collection.clone(), item, owner: caller, delegate }.into());
	}

	cancel_approval {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		let delegate: T::AccountId = account("delegate", 0, SEED);
		let delegate_lookup = T::Lookup::unlookup(delegate.clone());
		let origin = SystemOrigin::Signed(caller.clone()).into();
		Uniques::<T, I>::approve_transfer(origin, collection.clone(), item, delegate_lookup.clone())?;
	}: _(SystemOrigin::Signed(caller.clone()), collection.clone(), item, Some(delegate_lookup))
	verify {
		assert_last_event::<T, I>(Event::ApprovalCancelled { collection: collection.clone(), item, owner: caller, delegate }.into());
	}

	set_accept_ownership {
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, DepositBalanceOf::<T, I>::max_value());
		let collection = T::Helper::collection(0);
	}: _(SystemOrigin::Signed(caller.clone()), Some(collection.clone()))
	verify {
		assert_last_event::<T, I>(Event::OwnershipAcceptanceChanged {
			who: caller,
			maybe_collection: Some(collection),
		}.into());
	}

	set_collection_max_supply {
		let (collection, caller, _) = create_collection::<T, I>();
	}: _(SystemOrigin::Signed(caller.clone()), collection.clone(), u32::MAX)
	verify {
		assert_last_event::<T, I>(Event::CollectionMaxSupplySet {
			collection: collection.clone(),
			max_supply: u32::MAX,
		}.into());
	}

	set_price {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		let delegate: T::AccountId = account("delegate", 0, SEED);
		let delegate_lookup = T::Lookup::unlookup(delegate.clone());
		let price = ItemPrice::<T, I>::from(100u32);
	}: _(SystemOrigin::Signed(caller.clone()), collection.clone(), item, Some(price), Some(delegate_lookup))
	verify {
		assert_last_event::<T, I>(Event::ItemPriceSet {
			collection: collection.clone(),
			item,
			price,
			whitelisted_buyer: Some(delegate),
		}.into());
	}

	buy_item {
		let (collection, seller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		let buyer: T::AccountId = account("buyer", 0, SEED);
		let buyer_lookup = T::Lookup::unlookup(buyer.clone());
		let price = ItemPrice::<T, I>::from(0u32);
		let origin = SystemOrigin::Signed(seller.clone()).into();
		Uniques::<T, I>::set_price(origin, collection.clone(), item, Some(price.clone()), Some(buyer_lookup))?;
		T::Currency::make_free_balance_be(&buyer, DepositBalanceOf::<T, I>::max_value());
	}: _(SystemOrigin::Signed(buyer.clone()), collection.clone(), item, price.clone())
	verify {
		assert_last_event::<T, I>(Event::ItemBought {
			collection: collection.clone(),
			item,
			price,
			seller,
			buyer,
		}.into());
	}

	impl_benchmark_test_suite!(Uniques, crate::mock::new_test_ext(), crate::mock::Test);
}
