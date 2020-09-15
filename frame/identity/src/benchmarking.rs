// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Identity pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account, whitelisted_caller};
use sp_runtime::traits::Bounded;

use crate::Module as Identity;

const SEED: u32 = 0;

// Adds `r` registrars to the Identity Pallet. These registrars will have set fees and fields.
fn add_registrars<T: Trait>(r: u32) -> Result<(), &'static str> {
	for i in 0..r {
		let registrar: T::AccountId = account("registrar", i, SEED);
		let _ = T::Currency::make_free_balance_be(&registrar, BalanceOf::<T>::max_value());
		Identity::<T>::add_registrar(RawOrigin::Root.into(), registrar.clone())?;
		Identity::<T>::set_fee(RawOrigin::Signed(registrar.clone()).into(), i.into(), 10.into())?;
		let fields = IdentityFields(
			IdentityField::Display | IdentityField::Legal | IdentityField::Web | IdentityField::Riot
			| IdentityField::Email | IdentityField::PgpFingerprint | IdentityField::Image | IdentityField::Twitter
		);
		Identity::<T>::set_fields(RawOrigin::Signed(registrar.clone()).into(), i.into(), fields)?;
	}

	assert_eq!(Registrars::<T>::get().len(), r as usize);
	Ok(())
}

// Create `s` sub-accounts for the identity of `who` and return them.
// Each will have 32 bytes of raw data added to it.
fn create_sub_accounts<T: Trait>(who: &T::AccountId, s: u32) -> Result<Vec<(T::AccountId, Data)>, &'static str> {
	let mut subs = Vec::new();
	let who_origin = RawOrigin::Signed(who.clone());
	let data = Data::Raw(vec![0; 32]);

	for i in 0..s {
		let sub_account = account("sub", i, SEED);
		subs.push((sub_account, data.clone()));
	}

	// Set identity so `set_subs` does not fail.
	let _ = T::Currency::make_free_balance_be(&who, BalanceOf::<T>::max_value());
	let info = create_identity_info::<T>(1);
	Identity::<T>::set_identity(who_origin.clone().into(), info)?;

	Ok(subs)
}

// Adds `s` sub-accounts to the identity of `who`. Each will have 32 bytes of raw data added to it.
// This additionally returns the vector of sub-accounts so it can be modified if needed.
fn add_sub_accounts<T: Trait>(who: &T::AccountId, s: u32) -> Result<Vec<(T::AccountId, Data)>, &'static str> {
	let who_origin = RawOrigin::Signed(who.clone());
	let subs = create_sub_accounts::<T>(who, s)?;

	Identity::<T>::set_subs(who_origin.into(), subs.clone())?;

	Ok(subs)
}

// This creates an `IdentityInfo` object with `num_fields` extra fields.
// All data is pre-populated with some arbitrary bytes.
fn create_identity_info<T: Trait>(num_fields: u32) -> IdentityInfo {
	let data = Data::Raw(vec![0; 32]);

	let info = IdentityInfo {
		additional: vec![(data.clone(), data.clone()); num_fields as usize],
		display: data.clone(),
		legal: data.clone(),
		web: data.clone(),
		riot: data.clone(),
		email: data.clone(),
		pgp_fingerprint: Some([0; 20]),
		image: data.clone(),
		twitter: data.clone(),
	};

	return info
}

benchmarks! {
	// These are the common parameters along with their instancing.
	_ {
		let r in 1 .. T::MaxRegistrars::get() => add_registrars::<T>(r)?;
		// extra parameter for the set_subs bench for previous sub accounts
		let p in 1 .. T::MaxSubAccounts::get() => ();
		let s in 1 .. T::MaxSubAccounts::get() => {
			// Give them s many sub accounts
			let caller: T::AccountId = whitelisted_caller();
			let _ = add_sub_accounts::<T>(&caller, s)?;
		};
		let x in 1 .. T::MaxAdditionalFields::get() => {
			// Create their main identity with x additional fields
			let info = create_identity_info::<T>(x);
			let caller: T::AccountId = whitelisted_caller();
			let caller_origin = <T as frame_system::Trait>::Origin::from(RawOrigin::Signed(caller));
			Identity::<T>::set_identity(caller_origin, info)?;
		};
	}

	add_registrar {
		let r in 1 .. T::MaxRegistrars::get() - 1 => add_registrars::<T>(r)?;
	}: _(RawOrigin::Root, account("registrar", r + 1, SEED))

	set_identity {
		let r in ...;
		// This X doesn't affect the caller ID up front like with the others, so we don't use the
		// standard preparation.
		let x in _ .. _ => ();
		let caller = {
			// The target user
			let caller: T::AccountId = whitelisted_caller();
			let caller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(caller.clone());
			let caller_origin: <T as frame_system::Trait>::Origin = RawOrigin::Signed(caller.clone()).into();
			let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

			// Add an initial identity
			let initial_info = create_identity_info::<T>(1);
			Identity::<T>::set_identity(caller_origin.clone(), initial_info)?;

			// User requests judgement from all the registrars, and they approve
			for i in 0..r {
				Identity::<T>::request_judgement(caller_origin.clone(), i, 10.into())?;
				Identity::<T>::provide_judgement(
					RawOrigin::Signed(account("registrar", i, SEED)).into(),
					i,
					caller_lookup.clone(),
					Judgement::Reasonable
				)?;
			}
			caller
		};
	}: _(
		RawOrigin::Signed(caller),
		create_identity_info::<T>(x)
	)

	// We need to split `set_subs` into two benchmarks to accurately isolate the potential
	// writes caused by new or old sub accounts. The actual weight should simply be
	// the greater of these two weights.
	set_subs_new_subs {
		let caller: T::AccountId = whitelisted_caller();
		// Create a new subs vec with s sub accounts
		let s in 1 .. T::MaxSubAccounts::get() => ();
		let subs = create_sub_accounts::<T>(&caller, s)?;
	}: set_subs(RawOrigin::Signed(caller), subs)

	set_subs_old_subs {
		let caller: T::AccountId = whitelisted_caller();
		// Give them p many previous sub accounts.
		let p in 1 .. T::MaxSubAccounts::get() => {
			let _ = add_sub_accounts::<T>(&caller, p)?;
		};
		// Remove all subs.
		let subs = create_sub_accounts::<T>(&caller, 0)?;

	}: set_subs(RawOrigin::Signed(caller), subs)

	add_sub {
		let caller: T::AccountId = whitelisted_caller();

		// Give them p many previous sub accounts.
		let p in 1 .. T::MaxSubAccounts::get() - 1 => {
			let _ = add_sub_accounts::<T>(&caller, p)?;
		};
		let sub = account("new_sub", 0, SEED);
		let data = Data::Raw(vec![0; 32]);
	}: _(RawOrigin::Signed(caller), T::Lookup::unlookup(sub), data)

	rename_sub {
		let caller: T::AccountId = whitelisted_caller();

		let p in 1 .. T::MaxSubAccounts::get();

		// Give them p many previous sub accounts.
		let (sub, _) = add_sub_accounts::<T>(&caller, p)?.remove(0);
		let data = Data::Raw(vec![1; 32]);

	}: _(RawOrigin::Signed(caller), T::Lookup::unlookup(sub), data)

	remove_sub {
		let caller: T::AccountId = whitelisted_caller();

		// Give them p many previous sub accounts.
		let p in 1 .. T::MaxSubAccounts::get();
		let (sub, _) = add_sub_accounts::<T>(&caller, p)?.remove(0);
	}: _(RawOrigin::Signed(caller), T::Lookup::unlookup(sub))

	quit_sub {
		let caller: T::AccountId = whitelisted_caller();
		let sup = account("super", 0, SEED);

		// Give them p many previous sub accounts.
		let p in 1 .. T::MaxSubAccounts::get() - 1 => {
			let _ = add_sub_accounts::<T>(&sup, p)?;
		};
		let sup_origin = RawOrigin::Signed(sup).into();
		Identity::<T>::add_sub(sup_origin, T::Lookup::unlookup(caller.clone()), Data::Raw(vec![0; 32]))?;
	}: _(RawOrigin::Signed(caller))

	clear_identity {
		let caller: T::AccountId = whitelisted_caller();
		let caller_origin = <T as frame_system::Trait>::Origin::from(RawOrigin::Signed(caller.clone()));
		let caller_lookup = <T::Lookup as StaticLookup>::unlookup(caller.clone());
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r in ...;
		let s in ...;
		let x in ...;

		// User requests judgement from all the registrars, and they approve
		for i in 0..r {
			Identity::<T>::request_judgement(caller_origin.clone(), i, 10.into())?;
			Identity::<T>::provide_judgement(
				RawOrigin::Signed(account("registrar", i, SEED)).into(),
				i,
				caller_lookup.clone(),
				Judgement::Reasonable
			)?;
		}
	}: _(RawOrigin::Signed(caller))

	request_judgement {
		let caller: T::AccountId = whitelisted_caller();
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r in ...;
		let x in ...;
	}: _(RawOrigin::Signed(caller), r - 1, 10.into())

	cancel_request {
		let caller: T::AccountId = whitelisted_caller();
		let caller_origin = <T as frame_system::Trait>::Origin::from(RawOrigin::Signed(caller.clone()));
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r in ...;
		let x in ...;

		Identity::<T>::request_judgement(caller_origin, r - 1, 10.into())?;
	}: _(RawOrigin::Signed(caller), r - 1)

	set_fee {
		let caller: T::AccountId = whitelisted_caller();

		let r in 1 .. T::MaxRegistrars::get() - 1 => add_registrars::<T>(r)?;

		Identity::<T>::add_registrar(RawOrigin::Root.into(), caller.clone())?;
	}: _(RawOrigin::Signed(caller), r, 10.into())

	set_account_id {
		let caller: T::AccountId = whitelisted_caller();
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r in 1 .. T::MaxRegistrars::get() - 1 => add_registrars::<T>(r)?;

		Identity::<T>::add_registrar(RawOrigin::Root.into(), caller.clone())?;
	}: _(RawOrigin::Signed(caller), r, account("new", 0, SEED))

	set_fields {
		let caller: T::AccountId = whitelisted_caller();
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r in 1 .. T::MaxRegistrars::get() - 1 => add_registrars::<T>(r)?;

		Identity::<T>::add_registrar(RawOrigin::Root.into(), caller.clone())?;
		let fields = IdentityFields(
			IdentityField::Display | IdentityField::Legal | IdentityField::Web | IdentityField::Riot
			| IdentityField::Email | IdentityField::PgpFingerprint | IdentityField::Image | IdentityField::Twitter
		);
	}: _(RawOrigin::Signed(caller), r, fields)

	provide_judgement {
		// The user
		let user: T::AccountId = account("user", r, SEED);
		let user_origin = <T as frame_system::Trait>::Origin::from(RawOrigin::Signed(user.clone()));
		let user_lookup = <T::Lookup as StaticLookup>::unlookup(user.clone());
		let _ = T::Currency::make_free_balance_be(&user, BalanceOf::<T>::max_value());

		let caller: T::AccountId = whitelisted_caller();
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r in 1 .. T::MaxRegistrars::get() - 1 => add_registrars::<T>(r)?;
		// For this x, it's the user identity that gts the fields, not the caller.
		let x in _ .. _ => {
			let info = create_identity_info::<T>(x);
			Identity::<T>::set_identity(user_origin.clone(), info)?;
		};

		Identity::<T>::add_registrar(RawOrigin::Root.into(), caller.clone())?;
		Identity::<T>::request_judgement(user_origin.clone(), r, 10.into())?;
	}: _(RawOrigin::Signed(caller), r, user_lookup, Judgement::Reasonable)

	kill_identity {
		let caller: T::AccountId = whitelisted_caller();
		let caller_origin: <T as frame_system::Trait>::Origin = RawOrigin::Signed(caller.clone()).into();
		let caller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(caller.clone());
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r in ...;
		let s in ...;
		let x in ...;

		// User requests judgement from all the registrars, and they approve
		for i in 0..r {
			Identity::<T>::request_judgement(caller_origin.clone(), i, 10.into())?;
			Identity::<T>::provide_judgement(
				RawOrigin::Signed(account("registrar", i, SEED)).into(),
				i,
				caller_lookup.clone(),
				Judgement::Reasonable
			)?;
		}
	}: _(RawOrigin::Root, caller_lookup)
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_add_registrar::<Test>());
			assert_ok!(test_benchmark_set_identity::<Test>());
			assert_ok!(test_benchmark_set_subs::<Test>());
			assert_ok!(test_benchmark_clear_identity::<Test>());
			assert_ok!(test_benchmark_request_judgement::<Test>());
			assert_ok!(test_benchmark_cancel_request::<Test>());
			assert_ok!(test_benchmark_set_fee::<Test>());
			assert_ok!(test_benchmark_set_account_id::<Test>());
			assert_ok!(test_benchmark_set_fields::<Test>());
			assert_ok!(test_benchmark_provide_judgement::<Test>());
			assert_ok!(test_benchmark_kill_identity::<Test>());
		});
	}
}
