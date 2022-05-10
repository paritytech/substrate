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

//! Assets pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_benchmarking::{
	account, benchmarks_instance_pallet, whitelist_account, whitelisted_caller,
};
use frame_support::{
	dispatch::UnfilteredDispatchable,
	traits::{EnsureOrigin, Get},
	BoundedVec,
};
use frame_system::RawOrigin as SystemOrigin;
use sp_runtime::traits::Bounded;
use sp_std::prelude::*;

use crate::Pallet as Uniques;

const SEED: u32 = 0;

fn create_collection<T: Config<I>, I: 'static>(
) -> (T::CollectionId, T::AccountId, <T::Lookup as StaticLookup>::Source) {
	let caller: T::AccountId = whitelisted_caller();
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	let collection = T::Helper::collection(0);
	T::Currency::make_free_balance_be(&caller, DepositBalanceOf::<T, I>::max_value());
	assert!(Uniques::<T, I>::force_create(
		SystemOrigin::Root.into(),
		collection,
		caller_lookup.clone(),
		false,
	)
	.is_ok());
	(collection, caller, caller_lookup)
}

fn add_collection_metadata<T: Config<I>, I: 'static>(
) -> (T::AccountId, <T::Lookup as StaticLookup>::Source) {
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

fn mint_instance<T: Config<I>, I: 'static>(
	index: u16,
) -> (T::InstanceId, T::AccountId, <T::Lookup as StaticLookup>::Source) {
	let caller = Collection::<T, I>::get(T::Helper::collection(0)).unwrap().admin;
	if caller != whitelisted_caller() {
		whitelist_account!(caller);
	}
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	let instance = T::Helper::instance(index);
	assert!(Uniques::<T, I>::mint(
		SystemOrigin::Signed(caller.clone()).into(),
		T::Helper::collection(0),
		instance,
		caller_lookup.clone(),
	)
	.is_ok());
	(instance, caller, caller_lookup)
}

fn add_instance_metadata<T: Config<I>, I: 'static>(
	instance: T::InstanceId,
) -> (T::AccountId, <T::Lookup as StaticLookup>::Source) {
	let caller = Collection::<T, I>::get(T::Helper::collection(0)).unwrap().owner;
	if caller != whitelisted_caller() {
		whitelist_account!(caller);
	}
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	assert!(Uniques::<T, I>::set_metadata(
		SystemOrigin::Signed(caller.clone()).into(),
		T::Helper::collection(0),
		instance,
		vec![0; T::StringLimit::get() as usize].try_into().unwrap(),
		false,
	)
	.is_ok());
	(caller, caller_lookup)
}

fn add_instance_attribute<T: Config<I>, I: 'static>(
	instance: T::InstanceId,
) -> (BoundedVec<u8, T::KeyLimit>, T::AccountId, <T::Lookup as StaticLookup>::Source) {
	let caller = Collection::<T, I>::get(T::Helper::collection(0)).unwrap().owner;
	if caller != whitelisted_caller() {
		whitelist_account!(caller);
	}
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	let key: BoundedVec<_, _> = vec![0; T::KeyLimit::get() as usize].try_into().unwrap();
	assert!(Uniques::<T, I>::set_attribute(
		SystemOrigin::Signed(caller.clone()).into(),
		T::Helper::collection(0),
		Some(instance),
		key.clone(),
		vec![0; T::ValueLimit::get() as usize].try_into().unwrap(),
	)
	.is_ok());
	(key, caller, caller_lookup)
}

fn assert_last_event<T: Config<I>, I: 'static>(generic_event: <T as Config<I>>::Event) {
	let events = frame_system::Pallet::<T>::events();
	let system_event: <T as frame_system::Config>::Event = generic_event.into();
	// compare to the last event record
	let frame_system::EventRecord { event, .. } = &events[events.len() - 1];
	assert_eq!(event, &system_event);
}

benchmarks_instance_pallet! {
	create {
		let collection = T::Helper::collection(0);
		let origin = T::CreateOrigin::successful_origin(&collection);
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
			mint_instance::<T, I>(i as u16);
		}
		for i in 0..m {
			add_instance_metadata::<T, I>(T::Helper::instance(i as u16));
		}
		for i in 0..a {
			add_instance_attribute::<T, I>(T::Helper::instance(i as u16));
		}
		let witness = Collection::<T, I>::get(collection).unwrap().destroy_witness();
	}: _(SystemOrigin::Signed(caller), collection, witness)
	verify {
		assert_last_event::<T, I>(Event::Destroyed { collection }.into());
	}

	mint {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let instance = T::Helper::instance(0);
	}: _(SystemOrigin::Signed(caller.clone()), collection, instance, caller_lookup)
	verify {
		assert_last_event::<T, I>(Event::Issued { collection, instance, owner: caller }.into());
	}

	burn {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);
	}: _(SystemOrigin::Signed(caller.clone()), collection, instance, Some(caller_lookup))
	verify {
		assert_last_event::<T, I>(Event::Burned { collection, instance, owner: caller }.into());
	}

	transfer {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);

		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller.clone()), collection, instance, target_lookup)
	verify {
		assert_last_event::<T, I>(Event::Transferred { collection, instance, from: caller, to: target }.into());
	}

	redeposit {
		let i in 0 .. 5_000;
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let instances = (0..i).map(|x| mint_instance::<T, I>(x as u16).0).collect::<Vec<_>>();
		Uniques::<T, I>::force_asset_status(
			SystemOrigin::Root.into(),
			collection,
			caller_lookup.clone(),
			caller_lookup.clone(),
			caller_lookup.clone(),
			caller_lookup,
			true,
			false,
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), collection, instances.clone())
	verify {
		assert_last_event::<T, I>(Event::Redeposited { collection, successful_instances: instances }.into());
	}

	freeze {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);
	}: _(SystemOrigin::Signed(caller.clone()), T::Helper::collection(0), T::Helper::instance(0))
	verify {
		assert_last_event::<T, I>(Event::Frozen { collection: T::Helper::collection(0), instance: T::Helper::instance(0) }.into());
	}

	thaw {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);
		Uniques::<T, I>::freeze(
			SystemOrigin::Signed(caller.clone()).into(),
			collection,
			instance,
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), collection, instance)
	verify {
		assert_last_event::<T, I>(Event::Thawed { collection, instance }.into());
	}

	freeze_collection {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
	}: _(SystemOrigin::Signed(caller.clone()), collection)
	verify {
		assert_last_event::<T, I>(Event::CollectionFrozen { collection }.into());
	}

	thaw_collection {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let origin = SystemOrigin::Signed(caller.clone()).into();
		Uniques::<T, I>::freeze_collection(origin, collection)?;
	}: _(SystemOrigin::Signed(caller.clone()), collection)
	verify {
		assert_last_event::<T, I>(Event::CollectionThawed { collection }.into());
	}

	transfer_ownership {
		let (collection, caller, _) = create_collection::<T, I>();
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
		T::Currency::make_free_balance_be(&target, T::Currency::minimum_balance());
		let origin = SystemOrigin::Signed(target.clone()).into();
		Uniques::<T, I>::set_accept_ownership(origin, Some(collection))?;
	}: _(SystemOrigin::Signed(caller), collection, target_lookup)
	verify {
		assert_last_event::<T, I>(Event::OwnerChanged { collection, new_owner: target }.into());
	}

	set_team {
		let (collection, caller, _) = create_collection::<T, I>();
		let target0 = T::Lookup::unlookup(account("target", 0, SEED));
		let target1 = T::Lookup::unlookup(account("target", 1, SEED));
		let target2 = T::Lookup::unlookup(account("target", 2, SEED));
	}: _(SystemOrigin::Signed(caller), collection, target0, target1, target2)
	verify {
		assert_last_event::<T, I>(Event::TeamChanged{
			collection,
			issuer: account("target", 0, SEED),
			admin: account("target", 1, SEED),
			freezer: account("target", 2, SEED),
		}.into());
	}

	force_asset_status {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let origin = T::ForceOrigin::successful_origin();
		let call = Call::<T, I>::force_asset_status {
			collection,
			owner: caller_lookup.clone(),
			issuer: caller_lookup.clone(),
			admin: caller_lookup.clone(),
			freezer: caller_lookup,
			free_holding: true,
			is_frozen: false,
		};
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_last_event::<T, I>(Event::AssetStatusChanged { collection }.into());
	}

	set_attribute {
		let key: BoundedVec<_, _> = vec![0u8; T::KeyLimit::get() as usize].try_into().unwrap();
		let value: BoundedVec<_, _> = vec![0u8; T::ValueLimit::get() as usize].try_into().unwrap();

		let (collection, caller, _) = create_collection::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);
		add_instance_metadata::<T, I>(instance);
	}: _(SystemOrigin::Signed(caller), collection, Some(instance), key.clone(), value.clone())
	verify {
		assert_last_event::<T, I>(Event::AttributeSet { collection, maybe_instance: Some(instance), key, value }.into());
	}

	clear_attribute {
		let (collection, caller, _) = create_collection::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);
		add_instance_metadata::<T, I>(instance);
		let (key, ..) = add_instance_attribute::<T, I>(instance);
	}: _(SystemOrigin::Signed(caller), collection, Some(instance), key.clone())
	verify {
		assert_last_event::<T, I>(Event::AttributeCleared { collection, maybe_instance: Some(instance), key }.into());
	}

	set_metadata {
		let data: BoundedVec<_, _> = vec![0u8; T::StringLimit::get() as usize].try_into().unwrap();

		let (collection, caller, _) = create_collection::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);
	}: _(SystemOrigin::Signed(caller), collection, instance, data.clone(), false)
	verify {
		assert_last_event::<T, I>(Event::MetadataSet { collection, instance, data, is_frozen: false }.into());
	}

	clear_metadata {
		let (collection, caller, _) = create_collection::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);
		add_instance_metadata::<T, I>(instance);
	}: _(SystemOrigin::Signed(caller), collection, instance)
	verify {
		assert_last_event::<T, I>(Event::MetadataCleared { collection, instance }.into());
	}

	set_collection_metadata {
		let data: BoundedVec<_, _> = vec![0u8; T::StringLimit::get() as usize].try_into().unwrap();

		let (collection, caller, _) = create_collection::<T, I>();
	}: _(SystemOrigin::Signed(caller), collection, data.clone(), false)
	verify {
		assert_last_event::<T, I>(Event::CollectionMetadataSet { collection, data, is_frozen: false }.into());
	}

	clear_collection_metadata {
		let (collection, caller, _) = create_collection::<T, I>();
		add_collection_metadata::<T, I>();
	}: _(SystemOrigin::Signed(caller), collection)
	verify {
		assert_last_event::<T, I>(Event::CollectionMetadataCleared { collection }.into());
	}

	approve_transfer {
		let (collection, caller, _) = create_collection::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);
		let delegate: T::AccountId = account("delegate", 0, SEED);
		let delegate_lookup = T::Lookup::unlookup(delegate.clone());
	}: _(SystemOrigin::Signed(caller.clone()), collection, instance, delegate_lookup)
	verify {
		assert_last_event::<T, I>(Event::ApprovedTransfer { collection, instance, owner: caller, delegate }.into());
	}

	cancel_approval {
		let (collection, caller, _) = create_collection::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);
		let delegate: T::AccountId = account("delegate", 0, SEED);
		let delegate_lookup = T::Lookup::unlookup(delegate.clone());
		let origin = SystemOrigin::Signed(caller.clone()).into();
		Uniques::<T, I>::approve_transfer(origin, collection, instance, delegate_lookup.clone())?;
	}: _(SystemOrigin::Signed(caller.clone()), collection, instance, Some(delegate_lookup))
	verify {
		assert_last_event::<T, I>(Event::ApprovalCancelled { collection, instance, owner: caller, delegate }.into());
	}

	set_accept_ownership {
		let caller: T::AccountId = whitelisted_caller();
		T::Currency::make_free_balance_be(&caller, DepositBalanceOf::<T, I>::max_value());
		let collection = T::Helper::collection(0);
	}: _(SystemOrigin::Signed(caller.clone()), Some(collection))
	verify {
		assert_last_event::<T, I>(Event::OwnershipAcceptanceChanged {
			who: caller,
			maybe_collection: Some(collection),
		}.into());
	}

	impl_benchmark_test_suite!(Uniques, crate::mock::new_test_ext(), crate::mock::Test);
}
