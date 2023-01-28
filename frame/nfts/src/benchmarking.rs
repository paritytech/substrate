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

//! Nfts pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use enumflags2::{BitFlag, BitFlags};
use frame_benchmarking::v1::{
	account, benchmarks_instance_pallet, whitelist_account, whitelisted_caller,
};
use frame_support::{
	assert_ok,
	dispatch::UnfilteredDispatchable,
	traits::{EnsureOrigin, Get},
	BoundedVec,
};
use frame_system::RawOrigin as SystemOrigin;
use sp_runtime::traits::{Bounded, One};
use sp_std::prelude::*;

use crate::Pallet as Nfts;

const SEED: u32 = 0;

fn create_collection<T: Config<I>, I: 'static>(
) -> (T::CollectionId, T::AccountId, AccountIdLookupOf<T>) {
	let caller: T::AccountId = whitelisted_caller();
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	let collection = T::Helper::collection(0);
	T::Currency::make_free_balance_be(&caller, DepositBalanceOf::<T, I>::max_value());
	assert_ok!(Nfts::<T, I>::force_create(
		SystemOrigin::Root.into(),
		caller_lookup.clone(),
		default_collection_config::<T, I>()
	));
	(collection, caller, caller_lookup)
}

fn add_collection_metadata<T: Config<I>, I: 'static>() -> (T::AccountId, AccountIdLookupOf<T>) {
	let caller = Collection::<T, I>::get(T::Helper::collection(0)).unwrap().owner;
	if caller != whitelisted_caller() {
		whitelist_account!(caller);
	}
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	assert_ok!(Nfts::<T, I>::set_collection_metadata(
		SystemOrigin::Signed(caller.clone()).into(),
		T::Helper::collection(0),
		vec![0; T::StringLimit::get() as usize].try_into().unwrap(),
	));
	(caller, caller_lookup)
}

fn mint_item<T: Config<I>, I: 'static>(
	index: u16,
) -> (T::ItemId, T::AccountId, AccountIdLookupOf<T>) {
	let caller = Collection::<T, I>::get(T::Helper::collection(0)).unwrap().owner;
	if caller != whitelisted_caller() {
		whitelist_account!(caller);
	}
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	let item = T::Helper::item(index);
	assert_ok!(Nfts::<T, I>::mint(
		SystemOrigin::Signed(caller.clone()).into(),
		T::Helper::collection(0),
		item,
		caller_lookup.clone(),
		None,
	));
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
	assert_ok!(Nfts::<T, I>::set_metadata(
		SystemOrigin::Signed(caller.clone()).into(),
		T::Helper::collection(0),
		item,
		vec![0; T::StringLimit::get() as usize].try_into().unwrap(),
	));
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
	assert_ok!(Nfts::<T, I>::set_attribute(
		SystemOrigin::Signed(caller.clone()).into(),
		T::Helper::collection(0),
		Some(item),
		AttributeNamespace::CollectionOwner,
		key.clone(),
		vec![0; T::ValueLimit::get() as usize].try_into().unwrap(),
	));
	(key, caller, caller_lookup)
}

fn assert_last_event<T: Config<I>, I: 'static>(generic_event: <T as Config<I>>::RuntimeEvent) {
	let events = frame_system::Pallet::<T>::events();
	let system_event: <T as frame_system::Config>::RuntimeEvent = generic_event.into();
	// compare to the last event record
	let frame_system::EventRecord { event, .. } = &events[events.len() - 1];
	assert_eq!(event, &system_event);
}

fn make_collection_config<T: Config<I>, I: 'static>(
	disable_settings: BitFlags<CollectionSetting>,
) -> CollectionConfigFor<T, I> {
	CollectionConfig {
		settings: CollectionSettings::from_disabled(disable_settings),
		max_supply: None,
		mint_settings: MintSettings::default(),
	}
}

fn default_collection_config<T: Config<I>, I: 'static>() -> CollectionConfigFor<T, I> {
	make_collection_config::<T, I>(CollectionSetting::empty())
}

fn default_item_config() -> ItemConfig {
	ItemConfig { settings: ItemSettings::all_enabled() }
}

benchmarks_instance_pallet! {
	create {
		let collection = T::Helper::collection(0);
		let origin = T::CreateOrigin::successful_origin(&collection);
		let caller = T::CreateOrigin::ensure_origin(origin.clone(), &collection).unwrap();
		whitelist_account!(caller);
		let admin = T::Lookup::unlookup(caller.clone());
		T::Currency::make_free_balance_be(&caller, DepositBalanceOf::<T, I>::max_value());
		let call = Call::<T, I>::create { admin, config: default_collection_config::<T, I>() };
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_last_event::<T, I>(Event::Created { collection: T::Helper::collection(0), creator: caller.clone(), owner: caller }.into());
	}

	force_create {
		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup = T::Lookup::unlookup(caller.clone());
	}: _(SystemOrigin::Root, caller_lookup, default_collection_config::<T, I>())
	verify {
		assert_last_event::<T, I>(Event::ForceCreated { collection: T::Helper::collection(0), owner: caller }.into());
	}

	destroy {
		let n in 0 .. 1_000;
		let m in 0 .. 1_000;
		let a in 0 .. 1_000;

		let (collection, caller, _) = create_collection::<T, I>();
		add_collection_metadata::<T, I>();
		for i in 0..n {
			mint_item::<T, I>(i as u16);
		}
		for i in 0..m {
			if !Item::<T, I>::contains_key(collection, T::Helper::item(i as u16)) {
				mint_item::<T, I>(i as u16);
			}
			add_item_metadata::<T, I>(T::Helper::item(i as u16));
		}
		for i in 0..a {
			if !Item::<T, I>::contains_key(collection, T::Helper::item(i as u16)) {
				mint_item::<T, I>(i as u16);
			}
			add_item_attribute::<T, I>(T::Helper::item(i as u16));
		}
		let witness = Collection::<T, I>::get(collection).unwrap().destroy_witness();
	}: _(SystemOrigin::Signed(caller), collection, witness)
	verify {
		assert_last_event::<T, I>(Event::Destroyed { collection }.into());
	}

	mint {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let item = T::Helper::item(0);
	}: _(SystemOrigin::Signed(caller.clone()), collection, item, caller_lookup, None)
	verify {
		assert_last_event::<T, I>(Event::Issued { collection, item, owner: caller }.into());
	}

	force_mint {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let item = T::Helper::item(0);
	}: _(SystemOrigin::Signed(caller.clone()), collection, item, caller_lookup, default_item_config())
	verify {
		assert_last_event::<T, I>(Event::Issued { collection, item, owner: caller }.into());
	}

	burn {
		let (collection, caller, caller_lookup) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
	}: _(SystemOrigin::Signed(caller.clone()), collection, item, Some(caller_lookup))
	verify {
		assert_last_event::<T, I>(Event::Burned { collection, item, owner: caller }.into());
	}

	transfer {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);

		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
		T::Currency::make_free_balance_be(&target, T::Currency::minimum_balance());
	}: _(SystemOrigin::Signed(caller.clone()), collection, item, target_lookup)
	verify {
		assert_last_event::<T, I>(Event::Transferred { collection, item, from: caller, to: target }.into());
	}

	redeposit {
		let i in 0 .. 5_000;
		let (collection, caller, _) = create_collection::<T, I>();
		let items = (0..i).map(|x| mint_item::<T, I>(x as u16).0).collect::<Vec<_>>();
		Nfts::<T, I>::force_collection_config(
			SystemOrigin::Root.into(),
			collection,
			make_collection_config::<T, I>(CollectionSetting::DepositRequired.into()),
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), collection, items.clone())
	verify {
		assert_last_event::<T, I>(Event::Redeposited { collection, successful_items: items }.into());
	}

	lock_item_transfer {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
	}: _(SystemOrigin::Signed(caller.clone()), T::Helper::collection(0), T::Helper::item(0))
	verify {
		assert_last_event::<T, I>(Event::ItemTransferLocked { collection: T::Helper::collection(0), item: T::Helper::item(0) }.into());
	}

	unlock_item_transfer {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		Nfts::<T, I>::lock_item_transfer(
			SystemOrigin::Signed(caller.clone()).into(),
			collection,
			item,
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), collection, item)
	verify {
		assert_last_event::<T, I>(Event::ItemTransferUnlocked { collection, item }.into());
	}

	lock_collection {
		let (collection, caller, _) = create_collection::<T, I>();
		let lock_settings = CollectionSettings::from_disabled(
			CollectionSetting::TransferableItems |
				CollectionSetting::UnlockedMetadata |
				CollectionSetting::UnlockedAttributes |
				CollectionSetting::UnlockedMaxSupply,
		);
	}: _(SystemOrigin::Signed(caller.clone()), collection, lock_settings)
	verify {
		assert_last_event::<T, I>(Event::CollectionLocked { collection }.into());
	}

	transfer_ownership {
		let (collection, caller, _) = create_collection::<T, I>();
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
		T::Currency::make_free_balance_be(&target, T::Currency::minimum_balance());
		let origin = SystemOrigin::Signed(target.clone()).into();
		Nfts::<T, I>::set_accept_ownership(origin, Some(collection))?;
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

	force_collection_owner {
		let (collection, _, _) = create_collection::<T, I>();
		let origin = T::ForceOrigin::successful_origin();
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
		T::Currency::make_free_balance_be(&target, T::Currency::minimum_balance());
		let call = Call::<T, I>::force_collection_owner {
			collection,
			owner: target_lookup,
		};
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_last_event::<T, I>(Event::OwnerChanged { collection, new_owner: target }.into());
	}

	force_collection_config {
		let (collection, caller, _) = create_collection::<T, I>();
		let origin = T::ForceOrigin::successful_origin();
		let call = Call::<T, I>::force_collection_config {
			collection,
			config: make_collection_config::<T, I>(CollectionSetting::DepositRequired.into()),
		};
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_last_event::<T, I>(Event::CollectionConfigChanged { collection }.into());
	}

	lock_item_properties {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		let lock_metadata = true;
		let lock_attributes = true;
	}: _(SystemOrigin::Signed(caller), collection, item, lock_metadata, lock_attributes)
	verify {
		assert_last_event::<T, I>(Event::ItemPropertiesLocked { collection, item, lock_metadata, lock_attributes }.into());
	}

	set_attribute {
		let key: BoundedVec<_, _> = vec![0u8; T::KeyLimit::get() as usize].try_into().unwrap();
		let value: BoundedVec<_, _> = vec![0u8; T::ValueLimit::get() as usize].try_into().unwrap();

		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
	}: _(SystemOrigin::Signed(caller), collection, Some(item), AttributeNamespace::CollectionOwner, key.clone(), value.clone())
	verify {
		assert_last_event::<T, I>(
			Event::AttributeSet {
				collection,
				maybe_item: Some(item),
				namespace: AttributeNamespace::CollectionOwner,
				key,
				value,
			}
			.into(),
		);
	}

	force_set_attribute {
		let key: BoundedVec<_, _> = vec![0u8; T::KeyLimit::get() as usize].try_into().unwrap();
		let value: BoundedVec<_, _> = vec![0u8; T::ValueLimit::get() as usize].try_into().unwrap();

		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
	}: _(SystemOrigin::Root, Some(caller), collection, Some(item), AttributeNamespace::CollectionOwner, key.clone(), value.clone())
	verify {
		assert_last_event::<T, I>(
			Event::AttributeSet {
				collection,
				maybe_item: Some(item),
				namespace: AttributeNamespace::CollectionOwner,
				key,
				value,
			}
			.into(),
		);
	}

	clear_attribute {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		add_item_metadata::<T, I>(item);
		let (key, ..) = add_item_attribute::<T, I>(item);
	}: _(SystemOrigin::Signed(caller), collection, Some(item), AttributeNamespace::CollectionOwner, key.clone())
	verify {
		assert_last_event::<T, I>(
			Event::AttributeCleared {
				collection,
				maybe_item: Some(item),
				namespace: AttributeNamespace::CollectionOwner,
				key,
			}.into(),
		);
	}

	approve_item_attributes {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller), collection, item, target_lookup)
	verify {
		assert_last_event::<T, I>(
			Event::ItemAttributesApprovalAdded {
				collection,
				item,
				delegate: target,
			}
			.into(),
		);
	}

	cancel_item_attributes_approval {
		let n in 0 .. 1_000;

		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
		Nfts::<T, I>::approve_item_attributes(
			SystemOrigin::Signed(caller.clone()).into(),
			collection,
			item,
			target_lookup.clone(),
		)?;
		T::Currency::make_free_balance_be(&target, DepositBalanceOf::<T, I>::max_value());
		let value: BoundedVec<_, _> = vec![0u8; T::ValueLimit::get() as usize].try_into().unwrap();
		for i in 0..n {
			let mut key = vec![0u8; T::KeyLimit::get() as usize];
			let mut s = Vec::from((i as u16).to_be_bytes());
			key.truncate(s.len());
			key.append(&mut s);

			Nfts::<T, I>::set_attribute(
				SystemOrigin::Signed(target.clone()).into(),
				T::Helper::collection(0),
				Some(item),
				AttributeNamespace::Account(target.clone()),
				key.try_into().unwrap(),
				value.clone(),
			)?;
		}
		let witness = CancelAttributesApprovalWitness { account_attributes: n };
	}: _(SystemOrigin::Signed(caller), collection, item, target_lookup, witness)
	verify {
		assert_last_event::<T, I>(
			Event::ItemAttributesApprovalRemoved {
				collection,
				item,
				delegate: target,
			}
			.into(),
		);
	}

	set_metadata {
		let data: BoundedVec<_, _> = vec![0u8; T::StringLimit::get() as usize].try_into().unwrap();

		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
	}: _(SystemOrigin::Signed(caller), collection, item, data.clone())
	verify {
		assert_last_event::<T, I>(Event::ItemMetadataSet { collection, item, data }.into());
	}

	clear_metadata {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		add_item_metadata::<T, I>(item);
	}: _(SystemOrigin::Signed(caller), collection, item)
	verify {
		assert_last_event::<T, I>(Event::ItemMetadataCleared { collection, item }.into());
	}

	set_collection_metadata {
		let data: BoundedVec<_, _> = vec![0u8; T::StringLimit::get() as usize].try_into().unwrap();

		let (collection, caller, _) = create_collection::<T, I>();
	}: _(SystemOrigin::Signed(caller), collection, data.clone())
	verify {
		assert_last_event::<T, I>(Event::CollectionMetadataSet { collection, data }.into());
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
		let (item, ..) = mint_item::<T, I>(0);
		let delegate: T::AccountId = account("delegate", 0, SEED);
		let delegate_lookup = T::Lookup::unlookup(delegate.clone());
		let deadline = T::BlockNumber::max_value();
	}: _(SystemOrigin::Signed(caller.clone()), collection, item, delegate_lookup, Some(deadline))
	verify {
		assert_last_event::<T, I>(Event::TransferApproved { collection, item, owner: caller, delegate, deadline: Some(deadline) }.into());
	}

	cancel_approval {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		let delegate: T::AccountId = account("delegate", 0, SEED);
		let delegate_lookup = T::Lookup::unlookup(delegate.clone());
		let origin = SystemOrigin::Signed(caller.clone()).into();
		let deadline = T::BlockNumber::max_value();
		Nfts::<T, I>::approve_transfer(origin, collection, item, delegate_lookup.clone(), Some(deadline))?;
	}: _(SystemOrigin::Signed(caller.clone()), collection, item, delegate_lookup)
	verify {
		assert_last_event::<T, I>(Event::ApprovalCancelled { collection, item, owner: caller, delegate }.into());
	}

	clear_all_transfer_approvals {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		let delegate: T::AccountId = account("delegate", 0, SEED);
		let delegate_lookup = T::Lookup::unlookup(delegate.clone());
		let origin = SystemOrigin::Signed(caller.clone()).into();
		let deadline = T::BlockNumber::max_value();
		Nfts::<T, I>::approve_transfer(origin, collection, item, delegate_lookup.clone(), Some(deadline))?;
	}: _(SystemOrigin::Signed(caller.clone()), collection, item)
	verify {
		assert_last_event::<T, I>(Event::AllApprovalsCancelled {collection, item, owner: caller}.into());
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

	set_collection_max_supply {
		let (collection, caller, _) = create_collection::<T, I>();
	}: _(SystemOrigin::Signed(caller.clone()), collection, u32::MAX)
	verify {
		assert_last_event::<T, I>(Event::CollectionMaxSupplySet {
			collection,
			max_supply: u32::MAX,
		}.into());
	}

	update_mint_settings {
		let (collection, caller, _) = create_collection::<T, I>();
		let mint_settings = MintSettings {
			mint_type: MintType::HolderOf(T::Helper::collection(0)),
			start_block: Some(One::one()),
			end_block: Some(One::one()),
			price: Some(ItemPrice::<T, I>::from(1u32)),
			default_item_settings: ItemSettings::all_enabled(),
		};
	}: _(SystemOrigin::Signed(caller.clone()), collection, mint_settings)
	verify {
		assert_last_event::<T, I>(Event::CollectionMintSettingsUpdated { collection }.into());
	}

	set_price {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item, ..) = mint_item::<T, I>(0);
		let delegate: T::AccountId = account("delegate", 0, SEED);
		let delegate_lookup = T::Lookup::unlookup(delegate.clone());
		let price = ItemPrice::<T, I>::from(100u32);
	}: _(SystemOrigin::Signed(caller.clone()), collection, item, Some(price), Some(delegate_lookup))
	verify {
		assert_last_event::<T, I>(Event::ItemPriceSet {
			collection,
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
		Nfts::<T, I>::set_price(origin, collection, item, Some(price.clone()), Some(buyer_lookup))?;
		T::Currency::make_free_balance_be(&buyer, DepositBalanceOf::<T, I>::max_value());
	}: _(SystemOrigin::Signed(buyer.clone()), collection, item, price.clone())
	verify {
		assert_last_event::<T, I>(Event::ItemBought {
			collection,
			item,
			price,
			seller,
			buyer,
		}.into());
	}

	pay_tips {
		let n in 0 .. T::MaxTips::get() as u32;
		let amount = BalanceOf::<T, I>::from(100u32);
		let caller: T::AccountId = whitelisted_caller();
		let collection = T::Helper::collection(0);
		let item = T::Helper::item(0);
		let tips: BoundedVec<_, _> = vec![
			ItemTip
				{ collection, item, receiver: caller.clone(), amount }; n as usize
		].try_into().unwrap();
	}: _(SystemOrigin::Signed(caller.clone()), tips)
	verify {
		if !n.is_zero() {
			assert_last_event::<T, I>(Event::TipSent {
				collection,
				item,
				sender: caller.clone(),
				receiver: caller.clone(),
				amount,
			}.into());
		}
	}

	create_swap {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item1, ..) = mint_item::<T, I>(0);
		let (item2, ..) = mint_item::<T, I>(1);
		let price = ItemPrice::<T, I>::from(100u32);
		let price_direction = PriceDirection::Receive;
		let price_with_direction = PriceWithDirection { amount: price, direction: price_direction };
		let duration = T::MaxDeadlineDuration::get();
		frame_system::Pallet::<T>::set_block_number(One::one());
	}: _(SystemOrigin::Signed(caller.clone()), collection, item1, collection, Some(item2), Some(price_with_direction.clone()), duration)
	verify {
		let current_block = frame_system::Pallet::<T>::block_number();
		assert_last_event::<T, I>(Event::SwapCreated {
			offered_collection: collection,
			offered_item: item1,
			desired_collection: collection,
			desired_item: Some(item2),
			price: Some(price_with_direction),
			deadline: current_block.saturating_add(duration),
		}.into());
	}

	cancel_swap {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item1, ..) = mint_item::<T, I>(0);
		let (item2, ..) = mint_item::<T, I>(1);
		let price = ItemPrice::<T, I>::from(100u32);
		let origin = SystemOrigin::Signed(caller.clone()).into();
		let duration = T::MaxDeadlineDuration::get();
		let price_direction = PriceDirection::Receive;
		let price_with_direction = PriceWithDirection { amount: price, direction: price_direction };
		frame_system::Pallet::<T>::set_block_number(One::one());
		Nfts::<T, I>::create_swap(origin, collection, item1, collection, Some(item2), Some(price_with_direction.clone()), duration)?;
	}: _(SystemOrigin::Signed(caller.clone()), collection, item1)
	verify {
		assert_last_event::<T, I>(Event::SwapCancelled {
			offered_collection: collection,
			offered_item: item1,
			desired_collection: collection,
			desired_item: Some(item2),
			price: Some(price_with_direction),
			deadline: duration.saturating_add(One::one()),
		}.into());
	}

	claim_swap {
		let (collection, caller, _) = create_collection::<T, I>();
		let (item1, ..) = mint_item::<T, I>(0);
		let (item2, ..) = mint_item::<T, I>(1);
		let price = ItemPrice::<T, I>::from(0u32);
		let price_direction = PriceDirection::Receive;
		let price_with_direction = PriceWithDirection { amount: price, direction: price_direction };
		let duration = T::MaxDeadlineDuration::get();
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
		T::Currency::make_free_balance_be(&target, T::Currency::minimum_balance());
		let origin = SystemOrigin::Signed(caller.clone());
		frame_system::Pallet::<T>::set_block_number(One::one());
		Nfts::<T, I>::transfer(origin.clone().into(), collection, item2, target_lookup)?;
		Nfts::<T, I>::create_swap(
			origin.clone().into(),
			collection,
			item1,
			collection,
			Some(item2),
			Some(price_with_direction.clone()),
			duration,
		)?;
	}: _(SystemOrigin::Signed(target.clone()), collection, item2, collection, item1, Some(price_with_direction.clone()))
	verify {
		let current_block = frame_system::Pallet::<T>::block_number();
		assert_last_event::<T, I>(Event::SwapClaimed {
			sent_collection: collection,
			sent_item: item2,
			sent_item_owner: target,
			received_collection: collection,
			received_item: item1,
			received_item_owner: caller,
			price: Some(price_with_direction),
			deadline: duration.saturating_add(One::one()),
		}.into());
	}

	impl_benchmark_test_suite!(Nfts, crate::mock::new_test_ext(), crate::mock::Test);
}
