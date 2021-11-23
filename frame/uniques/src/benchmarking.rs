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
use sp_std::{convert::TryInto, prelude::*};

use crate::Pallet as Uniques;

const SEED: u32 = 0;

fn create_class<T: Config<I>, I: 'static>(
) -> (T::ClassId, T::AccountId, <T::Lookup as StaticLookup>::Source) {
	let caller: T::AccountId = whitelisted_caller();
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	let class = Default::default();
	T::Currency::make_free_balance_be(&caller, DepositBalanceOf::<T, I>::max_value());
	assert!(Uniques::<T, I>::create(
		SystemOrigin::Signed(caller.clone()).into(),
		class,
		caller_lookup.clone(),
	)
	.is_ok());
	(class, caller, caller_lookup)
}

fn add_class_metadata<T: Config<I>, I: 'static>(
) -> (T::AccountId, <T::Lookup as StaticLookup>::Source) {
	let caller = Class::<T, I>::get(T::ClassId::default()).unwrap().owner;
	if caller != whitelisted_caller() {
		whitelist_account!(caller);
	}
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	assert!(Uniques::<T, I>::set_class_metadata(
		SystemOrigin::Signed(caller.clone()).into(),
		Default::default(),
		vec![0; T::StringLimit::get() as usize].try_into().unwrap(),
		false,
	)
	.is_ok());
	(caller, caller_lookup)
}

fn mint_instance<T: Config<I>, I: 'static>(
	index: u16,
) -> (T::InstanceId, T::AccountId, <T::Lookup as StaticLookup>::Source) {
	let caller = Class::<T, I>::get(T::ClassId::default()).unwrap().admin;
	if caller != whitelisted_caller() {
		whitelist_account!(caller);
	}
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	let instance = index.into();
	assert!(Uniques::<T, I>::mint(
		SystemOrigin::Signed(caller.clone()).into(),
		Default::default(),
		instance,
		caller_lookup.clone(),
	)
	.is_ok());
	(instance, caller, caller_lookup)
}

fn add_instance_metadata<T: Config<I>, I: 'static>(
	instance: T::InstanceId,
) -> (T::AccountId, <T::Lookup as StaticLookup>::Source) {
	let caller = Class::<T, I>::get(T::ClassId::default()).unwrap().owner;
	if caller != whitelisted_caller() {
		whitelist_account!(caller);
	}
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	assert!(Uniques::<T, I>::set_metadata(
		SystemOrigin::Signed(caller.clone()).into(),
		Default::default(),
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
	let caller = Class::<T, I>::get(T::ClassId::default()).unwrap().owner;
	if caller != whitelisted_caller() {
		whitelist_account!(caller);
	}
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	let key: BoundedVec<_, _> = vec![0; T::KeyLimit::get() as usize].try_into().unwrap();
	assert!(Uniques::<T, I>::set_attribute(
		SystemOrigin::Signed(caller.clone()).into(),
		Default::default(),
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
		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup = T::Lookup::unlookup(caller.clone());
		T::Currency::make_free_balance_be(&caller, DepositBalanceOf::<T, I>::max_value());
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), caller_lookup)
	verify {
		assert_last_event::<T, I>(Event::Created { class: Default::default(), creator: caller.clone(), owner: caller }.into());
	}

	force_create {
		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup = T::Lookup::unlookup(caller.clone());
	}: _(SystemOrigin::Root, Default::default(), caller_lookup, true)
	verify {
		assert_last_event::<T, I>(Event::ForceCreated { class: Default::default(), owner: caller }.into());
	}

	destroy {
		let n in 0 .. 1_000;
		let m in 0 .. 1_000;
		let a in 0 .. 1_000;

		let (class, caller, caller_lookup) = create_class::<T, I>();
		add_class_metadata::<T, I>();
		for i in 0..n {
			mint_instance::<T, I>(i as u16);
		}
		for i in 0..m {
			add_instance_metadata::<T, I>((i as u16).into());
		}
		for i in 0..a {
			add_instance_attribute::<T, I>((i as u16).into());
		}
		let witness = Class::<T, I>::get(class).unwrap().destroy_witness();
	}: _(SystemOrigin::Signed(caller), class, witness)
	verify {
		assert_last_event::<T, I>(Event::Destroyed { class: class }.into());
	}

	mint {
		let (class, caller, caller_lookup) = create_class::<T, I>();
		let instance = Default::default();
	}: _(SystemOrigin::Signed(caller.clone()), class, instance, caller_lookup)
	verify {
		assert_last_event::<T, I>(Event::Issued { class, instance, owner: caller }.into());
	}

	burn {
		let (class, caller, caller_lookup) = create_class::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);
	}: _(SystemOrigin::Signed(caller.clone()), class, instance, Some(caller_lookup))
	verify {
		assert_last_event::<T, I>(Event::Burned { class, instance, owner: caller }.into());
	}

	transfer {
		let (class, caller, caller_lookup) = create_class::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(Default::default());

		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller.clone()), class, instance, target_lookup)
	verify {
		assert_last_event::<T, I>(Event::Transferred { class, instance, from: caller, to: target }.into());
	}

	redeposit {
		let i in 0 .. 5_000;
		let (class, caller, caller_lookup) = create_class::<T, I>();
		let instances = (0..i).map(|x| mint_instance::<T, I>(x as u16).0).collect::<Vec<_>>();
		Uniques::<T, I>::force_asset_status(
			SystemOrigin::Root.into(),
			class,
			caller_lookup.clone(),
			caller_lookup.clone(),
			caller_lookup.clone(),
			caller_lookup.clone(),
			true,
			false,
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), class, instances.clone())
	verify {
		assert_last_event::<T, I>(Event::Redeposited { class, successful_instances: instances }.into());
	}

	freeze {
		let (class, caller, caller_lookup) = create_class::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(Default::default());
	}: _(SystemOrigin::Signed(caller.clone()), Default::default(), Default::default())
	verify {
		assert_last_event::<T, I>(Event::Frozen { class: Default::default(), instance: Default::default() }.into());
	}

	thaw {
		let (class, caller, caller_lookup) = create_class::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(Default::default());
		Uniques::<T, I>::freeze(
			SystemOrigin::Signed(caller.clone()).into(),
			class,
			instance,
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), class, instance)
	verify {
		assert_last_event::<T, I>(Event::Thawed { class, instance }.into());
	}

	freeze_class {
		let (class, caller, caller_lookup) = create_class::<T, I>();
	}: _(SystemOrigin::Signed(caller.clone()), class)
	verify {
		assert_last_event::<T, I>(Event::ClassFrozen { class }.into());
	}

	thaw_class {
		let (class, caller, caller_lookup) = create_class::<T, I>();
		let origin = SystemOrigin::Signed(caller.clone()).into();
		Uniques::<T, I>::freeze_class(origin, class)?;
	}: _(SystemOrigin::Signed(caller.clone()), class)
	verify {
		assert_last_event::<T, I>(Event::ClassThawed { class }.into());
	}

	transfer_ownership {
		let (class, caller, _) = create_class::<T, I>();
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
		T::Currency::make_free_balance_be(&target, T::Currency::minimum_balance());
	}: _(SystemOrigin::Signed(caller), class, target_lookup)
	verify {
		assert_last_event::<T, I>(Event::OwnerChanged { class, new_owner: target }.into());
	}

	set_team {
		let (class, caller, _) = create_class::<T, I>();
		let target0 = T::Lookup::unlookup(account("target", 0, SEED));
		let target1 = T::Lookup::unlookup(account("target", 1, SEED));
		let target2 = T::Lookup::unlookup(account("target", 2, SEED));
	}: _(SystemOrigin::Signed(caller), Default::default(), target0.clone(), target1.clone(), target2.clone())
	verify {
		assert_last_event::<T, I>(Event::TeamChanged{
			class,
			issuer: account("target", 0, SEED),
			admin: account("target", 1, SEED),
			freezer: account("target", 2, SEED),
		}.into());
	}

	force_asset_status {
		let (class, caller, caller_lookup) = create_class::<T, I>();
		let origin = T::ForceOrigin::successful_origin();
		let call = Call::<T, I>::force_asset_status {
			class,
			owner: caller_lookup.clone(),
			issuer: caller_lookup.clone(),
			admin: caller_lookup.clone(),
			freezer: caller_lookup.clone(),
			free_holding: true,
			is_frozen: false,
		};
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_last_event::<T, I>(Event::AssetStatusChanged { class }.into());
	}

	set_attribute {
		let key: BoundedVec<_, _> = vec![0u8; T::KeyLimit::get() as usize].try_into().unwrap();
		let value: BoundedVec<_, _> = vec![0u8; T::ValueLimit::get() as usize].try_into().unwrap();

		let (class, caller, _) = create_class::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);
		add_instance_metadata::<T, I>(instance);
	}: _(SystemOrigin::Signed(caller), class, Some(instance), key.clone(), value.clone())
	verify {
		assert_last_event::<T, I>(Event::AttributeSet { class, maybe_instance: Some(instance), key, value }.into());
	}

	clear_attribute {
		let (class, caller, _) = create_class::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);
		add_instance_metadata::<T, I>(instance);
		let (key, ..) = add_instance_attribute::<T, I>(instance);
	}: _(SystemOrigin::Signed(caller), class, Some(instance), key.clone())
	verify {
		assert_last_event::<T, I>(Event::AttributeCleared { class, maybe_instance: Some(instance), key }.into());
	}

	set_metadata {
		let data: BoundedVec<_, _> = vec![0u8; T::StringLimit::get() as usize].try_into().unwrap();

		let (class, caller, _) = create_class::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);
	}: _(SystemOrigin::Signed(caller), class, instance, data.clone(), false)
	verify {
		assert_last_event::<T, I>(Event::MetadataSet { class, instance, data, is_frozen: false }.into());
	}

	clear_metadata {
		let (class, caller, _) = create_class::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);
		add_instance_metadata::<T, I>(instance);
	}: _(SystemOrigin::Signed(caller), class, instance)
	verify {
		assert_last_event::<T, I>(Event::MetadataCleared { class, instance }.into());
	}

	set_class_metadata {
		let data: BoundedVec<_, _> = vec![0u8; T::StringLimit::get() as usize].try_into().unwrap();

		let (class, caller, _) = create_class::<T, I>();
	}: _(SystemOrigin::Signed(caller), class, data.clone(), false)
	verify {
		assert_last_event::<T, I>(Event::ClassMetadataSet { class, data, is_frozen: false }.into());
	}

	clear_class_metadata {
		let (class, caller, _) = create_class::<T, I>();
		add_class_metadata::<T, I>();
	}: _(SystemOrigin::Signed(caller), class)
	verify {
		assert_last_event::<T, I>(Event::ClassMetadataCleared { class }.into());
	}

	approve_transfer {
		let (class, caller, _) = create_class::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);
		let delegate: T::AccountId = account("delegate", 0, SEED);
		let delegate_lookup = T::Lookup::unlookup(delegate.clone());
	}: _(SystemOrigin::Signed(caller.clone()), class, instance, delegate_lookup)
	verify {
		assert_last_event::<T, I>(Event::ApprovedTransfer { class, instance, owner: caller, delegate }.into());
	}

	cancel_approval {
		let (class, caller, _) = create_class::<T, I>();
		let (instance, ..) = mint_instance::<T, I>(0);
		let delegate: T::AccountId = account("delegate", 0, SEED);
		let delegate_lookup = T::Lookup::unlookup(delegate.clone());
		let origin = SystemOrigin::Signed(caller.clone()).into();
		Uniques::<T, I>::approve_transfer(origin, class, instance, delegate_lookup.clone())?;
	}: _(SystemOrigin::Signed(caller.clone()), class, instance, Some(delegate_lookup))
	verify {
		assert_last_event::<T, I>(Event::ApprovalCancelled { class, instance, owner: caller, delegate }.into());
	}

	impl_benchmark_test_suite!(Uniques, crate::mock::new_test_ext(), crate::mock::Test);
}
