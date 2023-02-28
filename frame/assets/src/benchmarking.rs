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

//! Assets pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_benchmarking::v1::{
	account, benchmarks_instance_pallet, whitelist_account, whitelisted_caller, BenchmarkError,
};
use frame_support::{
	dispatch::UnfilteredDispatchable,
	traits::{EnsureOrigin, Get},
};
use frame_system::RawOrigin as SystemOrigin;
use sp_runtime::traits::Bounded;
use sp_std::prelude::*;

use crate::Pallet as Assets;

const SEED: u32 = 0;

fn default_asset_id<T: Config<I>, I: 'static>() -> T::AssetIdParameter {
	T::BenchmarkHelper::create_asset_id_parameter(0)
}

fn create_default_asset<T: Config<I>, I: 'static>(
	is_sufficient: bool,
) -> (T::AssetIdParameter, T::AccountId, AccountIdLookupOf<T>) {
	let asset_id = default_asset_id::<T, I>();
	let caller: T::AccountId = whitelisted_caller();
	let caller_lookup = T::Lookup::unlookup(caller.clone());
	let root = SystemOrigin::Root.into();
	assert!(Assets::<T, I>::force_create(
		root,
		asset_id,
		caller_lookup.clone(),
		is_sufficient,
		1u32.into(),
	)
	.is_ok());
	(asset_id, caller, caller_lookup)
}

fn create_default_minted_asset<T: Config<I>, I: 'static>(
	is_sufficient: bool,
	amount: T::Balance,
) -> (T::AssetIdParameter, T::AccountId, AccountIdLookupOf<T>) {
	let (asset_id, caller, caller_lookup) = create_default_asset::<T, I>(is_sufficient);
	if !is_sufficient {
		T::Currency::make_free_balance_be(&caller, T::Currency::minimum_balance());
	}
	assert!(Assets::<T, I>::mint(
		SystemOrigin::Signed(caller.clone()).into(),
		asset_id,
		caller_lookup.clone(),
		amount,
	)
	.is_ok());
	(asset_id, caller, caller_lookup)
}

fn swap_is_sufficient<T: Config<I>, I: 'static>(s: &mut bool) {
	let asset_id = default_asset_id::<T, I>();
	Asset::<T, I>::mutate(&asset_id.into(), |maybe_a| {
		if let Some(ref mut a) = maybe_a {
			sp_std::mem::swap(s, &mut a.is_sufficient)
		}
	});
}

fn add_sufficients<T: Config<I>, I: 'static>(minter: T::AccountId, n: u32) {
	let asset_id = default_asset_id::<T, I>();
	let origin = SystemOrigin::Signed(minter);
	let mut s = true;
	swap_is_sufficient::<T, I>(&mut s);
	for i in 0..n {
		let target = account("sufficient", i, SEED);
		let target_lookup = T::Lookup::unlookup(target);
		assert!(Assets::<T, I>::mint(
			origin.clone().into(),
			asset_id,
			target_lookup,
			100u32.into()
		)
		.is_ok());
	}
	swap_is_sufficient::<T, I>(&mut s);
}

fn add_approvals<T: Config<I>, I: 'static>(minter: T::AccountId, n: u32) {
	let asset_id = default_asset_id::<T, I>();
	T::Currency::deposit_creating(&minter, T::ApprovalDeposit::get() * n.into());
	let minter_lookup = T::Lookup::unlookup(minter.clone());
	let origin = SystemOrigin::Signed(minter);
	Assets::<T, I>::mint(origin.clone().into(), asset_id, minter_lookup, (100 * (n + 1)).into())
		.unwrap();
	for i in 0..n {
		let target = account("approval", i, SEED);
		T::Currency::make_free_balance_be(&target, T::Currency::minimum_balance());
		let target_lookup = T::Lookup::unlookup(target);
		Assets::<T, I>::approve_transfer(
			origin.clone().into(),
			asset_id,
			target_lookup,
			100u32.into(),
		)
		.unwrap();
	}
}

fn assert_last_event<T: Config<I>, I: 'static>(generic_event: <T as Config<I>>::RuntimeEvent) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

fn assert_event<T: Config<I>, I: 'static>(generic_event: <T as Config<I>>::RuntimeEvent) {
	frame_system::Pallet::<T>::assert_has_event(generic_event.into());
}

benchmarks_instance_pallet! {
	create {
		let asset_id = default_asset_id::<T, I>();
		let origin = T::CreateOrigin::try_successful_origin(&asset_id.into())
			.map_err(|_| BenchmarkError::Weightless)?;
		let caller = T::CreateOrigin::ensure_origin(origin, &asset_id.into()).unwrap();
		let caller_lookup = T::Lookup::unlookup(caller.clone());
		T::Currency::make_free_balance_be(&caller, DepositBalanceOf::<T, I>::max_value());
	}: _(SystemOrigin::Signed(caller.clone()), asset_id, caller_lookup, 1u32.into())
	verify {
		assert_last_event::<T, I>(Event::Created { asset_id: asset_id.into(), creator: caller.clone(), owner: caller }.into());
	}

	force_create {
		let asset_id = default_asset_id::<T, I>();
		let caller: T::AccountId = whitelisted_caller();
		let caller_lookup = T::Lookup::unlookup(caller.clone());
	}: _(SystemOrigin::Root, asset_id, caller_lookup, true, 1u32.into())
	verify {
		assert_last_event::<T, I>(Event::ForceCreated { asset_id: asset_id.into(), owner: caller }.into());
	}

	start_destroy {
		let (asset_id, caller, caller_lookup) = create_default_minted_asset::<T, I>(true, 100u32.into());
		Assets::<T, I>::freeze_asset(
			SystemOrigin::Signed(caller.clone()).into(),
			asset_id,
		)?;
	}:_(SystemOrigin::Signed(caller), asset_id)
	verify {
		assert_last_event::<T, I>(Event::DestructionStarted { asset_id: asset_id.into() }.into());
	}

	destroy_accounts {
		let c in 0 .. T::RemoveItemsLimit::get();
		let (asset_id, caller, _) = create_default_asset::<T, I>(true);
		add_sufficients::<T, I>(caller.clone(), c);
		Assets::<T, I>::freeze_asset(
			SystemOrigin::Signed(caller.clone()).into(),
			asset_id,
		)?;
		Assets::<T,I>::start_destroy(SystemOrigin::Signed(caller.clone()).into(), asset_id)?;
	}:_(SystemOrigin::Signed(caller), asset_id)
	verify {
		assert_last_event::<T, I>(Event::AccountsDestroyed {
			asset_id: asset_id.into(),
			accounts_destroyed: c,
			accounts_remaining: 0,
		}.into());
	}

	destroy_approvals {
		let a in 0 .. T::RemoveItemsLimit::get();
		let (asset_id, caller, _) = create_default_minted_asset::<T, I>(true, 100u32.into());
		add_approvals::<T, I>(caller.clone(), a);
		Assets::<T, I>::freeze_asset(
			SystemOrigin::Signed(caller.clone()).into(),
			asset_id,
		)?;
		Assets::<T,I>::start_destroy(SystemOrigin::Signed(caller.clone()).into(), asset_id)?;
	}:_(SystemOrigin::Signed(caller), asset_id)
	verify {
		assert_last_event::<T, I>(Event::ApprovalsDestroyed {
			asset_id: asset_id.into(),
			approvals_destroyed: a,
			approvals_remaining: 0,
		}.into());
	}

	finish_destroy {
		let (asset_id, caller, caller_lookup) = create_default_asset::<T, I>(true);
		Assets::<T, I>::freeze_asset(
			SystemOrigin::Signed(caller.clone()).into(),
			asset_id,
		)?;
		Assets::<T,I>::start_destroy(SystemOrigin::Signed(caller.clone()).into(), asset_id)?;
	}:_(SystemOrigin::Signed(caller), asset_id)
	verify {
		assert_last_event::<T, I>(Event::Destroyed {
			asset_id: asset_id.into(),
		}.into()
		);
	}

	mint {
		let (asset_id, caller, caller_lookup) = create_default_asset::<T, I>(true);
		let amount = T::Balance::from(100u32);
	}: _(SystemOrigin::Signed(caller.clone()), asset_id, caller_lookup, amount)
	verify {
		assert_last_event::<T, I>(Event::Issued { asset_id: asset_id.into(), owner: caller, amount }.into());
	}

	burn {
		let amount = T::Balance::from(100u32);
		let (asset_id, caller, caller_lookup) = create_default_minted_asset::<T, I>(true, amount);
	}: _(SystemOrigin::Signed(caller.clone()), asset_id, caller_lookup, amount)
	verify {
		assert_last_event::<T, I>(Event::Burned { asset_id: asset_id.into(), owner: caller, balance: amount }.into());
	}

	transfer {
		let amount = T::Balance::from(100u32);
		let (asset_id, caller, caller_lookup) = create_default_minted_asset::<T, I>(true, amount);
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller.clone()), asset_id, target_lookup, amount)
	verify {
		assert_last_event::<T, I>(Event::Transferred { asset_id: asset_id.into(), from: caller, to: target, amount }.into());
	}

	transfer_keep_alive {
		let mint_amount = T::Balance::from(200u32);
		let amount = T::Balance::from(100u32);
		let (asset_id, caller, caller_lookup) = create_default_minted_asset::<T, I>(true, mint_amount);
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller.clone()), asset_id, target_lookup, amount)
	verify {
		assert!(frame_system::Pallet::<T>::account_exists(&caller));
		assert_last_event::<T, I>(Event::Transferred { asset_id: asset_id.into(), from: caller, to: target, amount }.into());
	}

	force_transfer {
		let amount = T::Balance::from(100u32);
		let (asset_id, caller, caller_lookup) = create_default_minted_asset::<T, I>(true, amount);
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller.clone()), asset_id, caller_lookup, target_lookup, amount)
	verify {
		assert_last_event::<T, I>(
			Event::Transferred { asset_id: asset_id.into(), from: caller, to: target, amount }.into()
		);
	}

	freeze {
		let (asset_id, caller, caller_lookup) = create_default_minted_asset::<T, I>(true, 100u32.into());
	}: _(SystemOrigin::Signed(caller.clone()), asset_id, caller_lookup)
	verify {
		assert_last_event::<T, I>(Event::Frozen { asset_id: asset_id.into(), who: caller }.into());
	}

	thaw {
		let (asset_id, caller, caller_lookup) = create_default_minted_asset::<T, I>(true, 100u32.into());
		Assets::<T, I>::freeze(
			SystemOrigin::Signed(caller.clone()).into(),
			asset_id,
			caller_lookup.clone(),
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), asset_id, caller_lookup)
	verify {
		assert_last_event::<T, I>(Event::Thawed { asset_id: asset_id.into(), who: caller }.into());
	}

	freeze_asset {
		let (asset_id, caller, caller_lookup) = create_default_minted_asset::<T, I>(true, 100u32.into());
	}: _(SystemOrigin::Signed(caller.clone()), asset_id)
	verify {
		assert_last_event::<T, I>(Event::AssetFrozen { asset_id: asset_id.into() }.into());
	}

	thaw_asset {
		let (asset_id, caller, caller_lookup) = create_default_minted_asset::<T, I>(true, 100u32.into());
		Assets::<T, I>::freeze_asset(
			SystemOrigin::Signed(caller.clone()).into(),
			asset_id,
		)?;
	}: _(SystemOrigin::Signed(caller.clone()), asset_id)
	verify {
		assert_last_event::<T, I>(Event::AssetThawed { asset_id: asset_id.into() }.into());
	}

	transfer_ownership {
		let (asset_id, caller, _) = create_default_asset::<T, I>(true);
		let target: T::AccountId = account("target", 0, SEED);
		let target_lookup = T::Lookup::unlookup(target.clone());
	}: _(SystemOrigin::Signed(caller), asset_id, target_lookup)
	verify {
		assert_last_event::<T, I>(Event::OwnerChanged { asset_id: asset_id.into(), owner: target }.into());
	}

	set_team {
		let (asset_id, caller, _) = create_default_asset::<T, I>(true);
		let target0 = T::Lookup::unlookup(account("target", 0, SEED));
		let target1 = T::Lookup::unlookup(account("target", 1, SEED));
		let target2 = T::Lookup::unlookup(account("target", 2, SEED));
	}: _(SystemOrigin::Signed(caller), asset_id, target0, target1, target2)
	verify {
		assert_last_event::<T, I>(Event::TeamChanged {
			asset_id: asset_id.into(),
			issuer: account("target", 0, SEED),
			admin: account("target", 1, SEED),
			freezer: account("target", 2, SEED),
		}.into());
	}

	set_metadata {
		let n in 0 .. T::StringLimit::get();
		let s in 0 .. T::StringLimit::get();

		let name = vec![0u8; n as usize];
		let symbol = vec![0u8; s as usize];
		let decimals = 12;

		let (asset_id, caller, _) = create_default_asset::<T, I>(true);
		T::Currency::make_free_balance_be(&caller, DepositBalanceOf::<T, I>::max_value());
	}: _(SystemOrigin::Signed(caller), asset_id, name.clone(), symbol.clone(), decimals)
	verify {
		assert_last_event::<T, I>(Event::MetadataSet { asset_id: asset_id.into(), name, symbol, decimals, is_frozen: false }.into());
	}

	clear_metadata {
		let (asset_id, caller, _) = create_default_asset::<T, I>(true);
		T::Currency::make_free_balance_be(&caller, DepositBalanceOf::<T, I>::max_value());
		let dummy = vec![0u8; T::StringLimit::get() as usize];
		let origin = SystemOrigin::Signed(caller.clone()).into();
		Assets::<T, I>::set_metadata(origin, asset_id, dummy.clone(), dummy, 12)?;
	}: _(SystemOrigin::Signed(caller), asset_id)
	verify {
		assert_last_event::<T, I>(Event::MetadataCleared { asset_id: asset_id.into() }.into());
	}

	force_set_metadata {
		let n in 0 .. T::StringLimit::get();
		let s in 0 .. T::StringLimit::get();

		let name = vec![0u8; n as usize];
		let symbol = vec![0u8; s as usize];
		let decimals = 12;

		let (asset_id, _, _) = create_default_asset::<T, I>(true);

		let origin =
			T::ForceOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
		let call = Call::<T, I>::force_set_metadata {
			id: asset_id,
			name: name.clone(),
			symbol: symbol.clone(),
			decimals,
			is_frozen: false,
		};
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_last_event::<T, I>(Event::MetadataSet { asset_id: asset_id.into(), name, symbol, decimals, is_frozen: false }.into());
	}

	force_clear_metadata {
		let (asset_id, caller, _) = create_default_asset::<T, I>(true);
		T::Currency::make_free_balance_be(&caller, DepositBalanceOf::<T, I>::max_value());
		let dummy = vec![0u8; T::StringLimit::get() as usize];
		let origin = SystemOrigin::Signed(caller).into();
		Assets::<T, I>::set_metadata(origin, asset_id, dummy.clone(), dummy, 12)?;

		let origin =
			T::ForceOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
		let call = Call::<T, I>::force_clear_metadata { id: asset_id };
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_last_event::<T, I>(Event::MetadataCleared { asset_id: asset_id.into() }.into());
	}

	force_asset_status {
		let (asset_id, caller, caller_lookup) = create_default_asset::<T, I>(true);

		let origin =
			T::ForceOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?;
		let call = Call::<T, I>::force_asset_status {
			id: asset_id,
			owner: caller_lookup.clone(),
			issuer: caller_lookup.clone(),
			admin: caller_lookup.clone(),
			freezer: caller_lookup,
			min_balance: 100u32.into(),
			is_sufficient: true,
			is_frozen: false,
		};
	}: { call.dispatch_bypass_filter(origin)? }
	verify {
		assert_last_event::<T, I>(Event::AssetStatusChanged { asset_id: asset_id.into() }.into());
	}

	approve_transfer {
		let (asset_id, caller, _) = create_default_minted_asset::<T, I>(true, 100u32.into());
		T::Currency::make_free_balance_be(&caller, DepositBalanceOf::<T, I>::max_value());

		let delegate: T::AccountId = account("delegate", 0, SEED);
		let delegate_lookup = T::Lookup::unlookup(delegate.clone());
		let amount = 100u32.into();
	}: _(SystemOrigin::Signed(caller.clone()), asset_id, delegate_lookup, amount)
	verify {
		assert_last_event::<T, I>(Event::ApprovedTransfer { asset_id: asset_id.into(), source: caller, delegate, amount }.into());
	}

	transfer_approved {
		let (asset_id, owner, owner_lookup) = create_default_minted_asset::<T, I>(true, 100u32.into());
		T::Currency::make_free_balance_be(&owner, DepositBalanceOf::<T, I>::max_value());

		let delegate: T::AccountId = account("delegate", 0, SEED);
		whitelist_account!(delegate);
		let delegate_lookup = T::Lookup::unlookup(delegate.clone());
		let amount = 100u32.into();
		let origin = SystemOrigin::Signed(owner.clone()).into();
		Assets::<T, I>::approve_transfer(origin, asset_id, delegate_lookup, amount)?;

		let dest: T::AccountId = account("dest", 0, SEED);
		let dest_lookup = T::Lookup::unlookup(dest.clone());
	}: _(SystemOrigin::Signed(delegate.clone()), asset_id, owner_lookup, dest_lookup, amount)
	verify {
		assert!(T::Currency::reserved_balance(&owner).is_zero());
		assert_event::<T, I>(Event::Transferred { asset_id: asset_id.into(), from: owner, to: dest, amount }.into());
	}

	cancel_approval {
		let (asset_id, caller, _) = create_default_minted_asset::<T, I>(true, 100u32.into());
		T::Currency::make_free_balance_be(&caller, DepositBalanceOf::<T, I>::max_value());

		let delegate: T::AccountId = account("delegate", 0, SEED);
		let delegate_lookup = T::Lookup::unlookup(delegate.clone());
		let amount = 100u32.into();
		let origin = SystemOrigin::Signed(caller.clone()).into();
		Assets::<T, I>::approve_transfer(origin, asset_id, delegate_lookup.clone(), amount)?;
	}: _(SystemOrigin::Signed(caller.clone()), asset_id, delegate_lookup)
	verify {
		assert_last_event::<T, I>(Event::ApprovalCancelled { asset_id: asset_id.into(), owner: caller, delegate }.into());
	}

	force_cancel_approval {
		let (asset_id, caller, caller_lookup) = create_default_minted_asset::<T, I>(true, 100u32.into());
		T::Currency::make_free_balance_be(&caller, DepositBalanceOf::<T, I>::max_value());

		let delegate: T::AccountId = account("delegate", 0, SEED);
		let delegate_lookup = T::Lookup::unlookup(delegate.clone());
		let amount = 100u32.into();
		let origin = SystemOrigin::Signed(caller.clone()).into();
		Assets::<T, I>::approve_transfer(origin, asset_id, delegate_lookup.clone(), amount)?;
	}: _(SystemOrigin::Signed(caller.clone()), asset_id, caller_lookup, delegate_lookup)
	verify {
		assert_last_event::<T, I>(Event::ApprovalCancelled { asset_id: asset_id.into(), owner: caller, delegate }.into());
	}

	set_min_balance {
		let (asset_id, caller, caller_lookup) = create_default_asset::<T, I>(true);
	}: _(SystemOrigin::Signed(caller.clone()), asset_id, 50u32.into())
	verify {
		assert_last_event::<T, I>(Event::AssetMinBalanceChanged { asset_id: asset_id.into(), new_min_balance: 50u32.into() }.into());
	}

	impl_benchmark_test_suite!(Assets, crate::mock::new_test_ext(), crate::mock::Test)
}
