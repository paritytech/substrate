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

//! Identity pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_system::{EventRecord, RawOrigin};
use frame_benchmarking::{benchmarks, account, whitelisted_caller, impl_benchmark_test_suite};
use sp_runtime::traits::Bounded;

use crate::Module as Identity;

const SEED: u32 = 0;

fn assert_last_event<T: Config>(generic_event: <T as Config>::Event) {
	let events = frame_system::Module::<T>::events();
	let system_event: <T as frame_system::Config>::Event = generic_event.into();
	// compare to the last event record
	let EventRecord { event, .. } = &events[events.len() - 1];
	assert_eq!(event, &system_event);
}

// Adds `r` registrars to the Identity Pallet. These registrars will have set fees and fields.
fn add_registrars<T: Config>(r: u32) -> Result<(), &'static str> {
	for i in 0..r {
		let registrar: T::AccountId = account("registrar", i, SEED);
		let _ = T::Currency::make_free_balance_be(&registrar, BalanceOf::<T>::max_value());
		Identity::<T>::add_registrar(RawOrigin::Root.into(), registrar.clone())?;
		Identity::<T>::set_fee(RawOrigin::Signed(registrar.clone()).into(), i.into(), 10u32.into())?;
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
fn create_sub_accounts<T: Config>(who: &T::AccountId, s: u32) -> Result<Vec<(T::AccountId, Data)>, &'static str> {
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
fn add_sub_accounts<T: Config>(who: &T::AccountId, s: u32) -> Result<Vec<(T::AccountId, Data)>, &'static str> {
	let who_origin = RawOrigin::Signed(who.clone());
	let subs = create_sub_accounts::<T>(who, s)?;

	Identity::<T>::set_subs(who_origin.into(), subs.clone())?;

	Ok(subs)
}

// This creates an `IdentityInfo` object with `num_fields` extra fields.
// All data is pre-populated with some arbitrary bytes.
fn create_identity_info<T: Config>(num_fields: u32) -> IdentityInfo {
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
	add_registrar {
		let r in 1 .. T::MaxRegistrars::get() - 1 => add_registrars::<T>(r)?;
		ensure!(Registrars::<T>::get().len() as u32 == r, "Registrars not set up correctly.");
	}: _(RawOrigin::Root, account("registrar", r + 1, SEED))
	verify {
		ensure!(Registrars::<T>::get().len() as u32 == r + 1, "Registrars not added.");
	}

	set_identity {
		let r in 1 .. T::MaxRegistrars::get() => add_registrars::<T>(r)?;
		let x in 1 .. T::MaxAdditionalFields::get();
		let caller = {
			// The target user
			let caller: T::AccountId = whitelisted_caller();
			let caller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(caller.clone());
			let caller_origin: <T as frame_system::Config>::Origin = RawOrigin::Signed(caller.clone()).into();
			let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

			// Add an initial identity
			let initial_info = create_identity_info::<T>(1);
			Identity::<T>::set_identity(caller_origin.clone(), initial_info)?;

			// User requests judgement from all the registrars, and they approve
			for i in 0..r {
				Identity::<T>::request_judgement(caller_origin.clone(), i, 10u32.into())?;
				Identity::<T>::provide_judgement(
					RawOrigin::Signed(account("registrar", i, SEED)).into(),
					i,
					caller_lookup.clone(),
					Judgement::Reasonable
				)?;
			}
			caller
		};
	}: _(RawOrigin::Signed(caller.clone()), create_identity_info::<T>(x))
	verify {
		assert_last_event::<T>(Event::<T>::IdentitySet(caller).into());
	}

	// We need to split `set_subs` into two benchmarks to accurately isolate the potential
	// writes caused by new or old sub accounts. The actual weight should simply be
	// the sum of these two weights.
	set_subs_new {
		let caller: T::AccountId = whitelisted_caller();
		// Create a new subs vec with s sub accounts
		let s in 1 .. T::MaxSubAccounts::get() => ();
		let subs = create_sub_accounts::<T>(&caller, s)?;
		ensure!(SubsOf::<T>::get(&caller).1.len() == 0, "Caller already has subs");
	}: set_subs(RawOrigin::Signed(caller.clone()), subs)
	verify {
		ensure!(SubsOf::<T>::get(&caller).1.len() as u32 == s, "Subs not added");
	}

	set_subs_old {
		let caller: T::AccountId = whitelisted_caller();
		// Give them p many previous sub accounts.
		let p in 1 .. T::MaxSubAccounts::get() => {
			let _ = add_sub_accounts::<T>(&caller, p)?;
		};
		// Remove all subs.
		let subs = create_sub_accounts::<T>(&caller, 0)?;
		ensure!(
			SubsOf::<T>::get(&caller).1.len() as u32 == p,
			"Caller does have subs",
		);
	}: set_subs(RawOrigin::Signed(caller.clone()), subs)
	verify {
		ensure!(SubsOf::<T>::get(&caller).1.len() == 0, "Subs not removed");
	}

	clear_identity {
		let caller: T::AccountId = whitelisted_caller();
		let caller_origin = <T as frame_system::Config>::Origin::from(RawOrigin::Signed(caller.clone()));
		let caller_lookup = <T::Lookup as StaticLookup>::unlookup(caller.clone());
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r in 1 .. T::MaxRegistrars::get() => add_registrars::<T>(r)?;
		let s in 1 .. T::MaxSubAccounts::get() => {
			// Give them s many sub accounts
			let caller: T::AccountId = whitelisted_caller();
			let _ = add_sub_accounts::<T>(&caller, s)?;
		};
		let x in 1 .. T::MaxAdditionalFields::get() => {
			// Create their main identity with x additional fields
			let info = create_identity_info::<T>(x);
			let caller: T::AccountId = whitelisted_caller();
			let caller_origin = <T as frame_system::Config>::Origin::from(RawOrigin::Signed(caller));
			Identity::<T>::set_identity(caller_origin, info)?;
		};

		// User requests judgement from all the registrars, and they approve
		for i in 0..r {
			Identity::<T>::request_judgement(caller_origin.clone(), i, 10u32.into())?;
			Identity::<T>::provide_judgement(
				RawOrigin::Signed(account("registrar", i, SEED)).into(),
				i,
				caller_lookup.clone(),
				Judgement::Reasonable
			)?;
		}
		ensure!(IdentityOf::<T>::contains_key(&caller), "Identity does not exist.");
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		ensure!(!IdentityOf::<T>::contains_key(&caller), "Identity not cleared.");
	}

	request_judgement {
		let caller: T::AccountId = whitelisted_caller();
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r in 1 .. T::MaxRegistrars::get() => add_registrars::<T>(r)?;
		let x in 1 .. T::MaxAdditionalFields::get() => {
			// Create their main identity with x additional fields
			let info = create_identity_info::<T>(x);
			let caller: T::AccountId = whitelisted_caller();
			let caller_origin = <T as frame_system::Config>::Origin::from(RawOrigin::Signed(caller));
			Identity::<T>::set_identity(caller_origin, info)?;
		};
	}: _(RawOrigin::Signed(caller.clone()), r - 1, 10u32.into())
	verify {
		assert_last_event::<T>(Event::<T>::JudgementRequested(caller, r-1).into());
	}

	cancel_request {
		let caller: T::AccountId = whitelisted_caller();
		let caller_origin = <T as frame_system::Config>::Origin::from(RawOrigin::Signed(caller.clone()));
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r in 1 .. T::MaxRegistrars::get() => add_registrars::<T>(r)?;
		let x in 1 .. T::MaxAdditionalFields::get() => {
			// Create their main identity with x additional fields
			let info = create_identity_info::<T>(x);
			let caller: T::AccountId = whitelisted_caller();
			let caller_origin = <T as frame_system::Config>::Origin::from(RawOrigin::Signed(caller));
			Identity::<T>::set_identity(caller_origin, info)?;
		};

		Identity::<T>::request_judgement(caller_origin, r - 1, 10u32.into())?;
	}: _(RawOrigin::Signed(caller.clone()), r - 1)
	verify {
		assert_last_event::<T>(Event::<T>::JudgementUnrequested(caller, r-1).into());
	}

	set_fee {
		let caller: T::AccountId = whitelisted_caller();

		let r in 1 .. T::MaxRegistrars::get() - 1 => add_registrars::<T>(r)?;

		Identity::<T>::add_registrar(RawOrigin::Root.into(), caller.clone())?;
		let registrars = Registrars::<T>::get();
		ensure!(registrars[r as usize].as_ref().unwrap().fee == 0u32.into(), "Fee already set.");
	}: _(RawOrigin::Signed(caller), r, 100u32.into())
	verify {
		let registrars = Registrars::<T>::get();
		ensure!(registrars[r as usize].as_ref().unwrap().fee == 100u32.into(), "Fee not changed.");
	}

	set_account_id {
		let caller: T::AccountId = whitelisted_caller();
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r in 1 .. T::MaxRegistrars::get() - 1 => add_registrars::<T>(r)?;

		Identity::<T>::add_registrar(RawOrigin::Root.into(), caller.clone())?;
		let registrars = Registrars::<T>::get();
		ensure!(registrars[r as usize].as_ref().unwrap().account == caller.clone(), "id not set.");
	}: _(RawOrigin::Signed(caller), r, account("new", 0, SEED))
	verify {
		let registrars = Registrars::<T>::get();
		ensure!(registrars[r as usize].as_ref().unwrap().account == account("new", 0, SEED), "id not changed.");
	}

	set_fields {
		let caller: T::AccountId = whitelisted_caller();
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r in 1 .. T::MaxRegistrars::get() - 1 => add_registrars::<T>(r)?;

		Identity::<T>::add_registrar(RawOrigin::Root.into(), caller.clone())?;
		let fields = IdentityFields(
			IdentityField::Display | IdentityField::Legal | IdentityField::Web | IdentityField::Riot
			| IdentityField::Email | IdentityField::PgpFingerprint | IdentityField::Image | IdentityField::Twitter
		);
		let registrars = Registrars::<T>::get();
		ensure!(registrars[r as usize].as_ref().unwrap().fields == Default::default(), "fields already set.");
	}: _(RawOrigin::Signed(caller), r, fields)
	verify {
		let registrars = Registrars::<T>::get();
		ensure!(registrars[r as usize].as_ref().unwrap().fields != Default::default(), "fields not set.");
	}

	provide_judgement {
		// The user
		let user: T::AccountId = account("user", r, SEED);
		let user_origin = <T as frame_system::Config>::Origin::from(RawOrigin::Signed(user.clone()));
		let user_lookup = <T::Lookup as StaticLookup>::unlookup(user.clone());
		let _ = T::Currency::make_free_balance_be(&user, BalanceOf::<T>::max_value());

		let caller: T::AccountId = whitelisted_caller();
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r in 1 .. T::MaxRegistrars::get() - 1 => add_registrars::<T>(r)?;
		let x in 1 .. T::MaxAdditionalFields::get() => {
			let info = create_identity_info::<T>(x);
			Identity::<T>::set_identity(user_origin.clone(), info)?;
		};

		Identity::<T>::add_registrar(RawOrigin::Root.into(), caller.clone())?;
		Identity::<T>::request_judgement(user_origin.clone(), r, 10u32.into())?;
	}: _(RawOrigin::Signed(caller), r, user_lookup, Judgement::Reasonable)
	verify {
		assert_last_event::<T>(Event::<T>::JudgementGiven(user, r).into())
	}

	kill_identity {
		let r in 1 .. T::MaxRegistrars::get() => add_registrars::<T>(r)?;
		let s in 1 .. T::MaxSubAccounts::get();
		let x in 1 .. T::MaxAdditionalFields::get();

		let target: T::AccountId = account("target", 0, SEED);
		let target_origin: <T as frame_system::Config>::Origin = RawOrigin::Signed(target.clone()).into();
		let target_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(target.clone());
		let _ = T::Currency::make_free_balance_be(&target, BalanceOf::<T>::max_value());

		let info = create_identity_info::<T>(x);
		Identity::<T>::set_identity(target_origin.clone(), info)?;
		let _ = add_sub_accounts::<T>(&target, s)?;

		// User requests judgement from all the registrars, and they approve
		for i in 0..r {
			Identity::<T>::request_judgement(target_origin.clone(), i, 10u32.into())?;
			Identity::<T>::provide_judgement(
				RawOrigin::Signed(account("registrar", i, SEED)).into(),
				i,
				target_lookup.clone(),
				Judgement::Reasonable
			)?;
		}
		ensure!(IdentityOf::<T>::contains_key(&target), "Identity not set");
	}: _(RawOrigin::Root, target_lookup)
	verify {
		ensure!(!IdentityOf::<T>::contains_key(&target), "Identity not removed");
	}

	add_sub {
		let s in 1 .. T::MaxSubAccounts::get() - 1;

		let caller: T::AccountId = whitelisted_caller();
		let _ = add_sub_accounts::<T>(&caller, s)?;
		let sub = account("new_sub", 0, SEED);
		let data = Data::Raw(vec![0; 32]);
		ensure!(SubsOf::<T>::get(&caller).1.len() as u32 == s, "Subs not set.");
	}: _(RawOrigin::Signed(caller.clone()), T::Lookup::unlookup(sub), data)
	verify {
		ensure!(SubsOf::<T>::get(&caller).1.len() as u32 == s + 1, "Subs not added.");
	}

	rename_sub {
		let s in 1 .. T::MaxSubAccounts::get();

		let caller: T::AccountId = whitelisted_caller();
		let (sub, _) = add_sub_accounts::<T>(&caller, s)?.remove(0);
		let data = Data::Raw(vec![1; 32]);
		ensure!(SuperOf::<T>::get(&sub).unwrap().1 != data, "data already set");
	}: _(RawOrigin::Signed(caller), T::Lookup::unlookup(sub.clone()), data.clone())
	verify {
		ensure!(SuperOf::<T>::get(&sub).unwrap().1 == data, "data not set");
	}

	remove_sub {
		let s in 1 .. T::MaxSubAccounts::get();

		let caller: T::AccountId = whitelisted_caller();
		let (sub, _) = add_sub_accounts::<T>(&caller, s)?.remove(0);
		ensure!(SuperOf::<T>::contains_key(&sub), "Sub doesn't exists");
	}: _(RawOrigin::Signed(caller), T::Lookup::unlookup(sub.clone()))
	verify {
		ensure!(!SuperOf::<T>::contains_key(&sub), "Sub not removed");
	}

	quit_sub {
		let s in 1 .. T::MaxSubAccounts::get() - 1;

		let caller: T::AccountId = whitelisted_caller();
		let sup = account("super", 0, SEED);
		let _ = add_sub_accounts::<T>(&sup, s)?;
		let sup_origin = RawOrigin::Signed(sup).into();
		Identity::<T>::add_sub(sup_origin, T::Lookup::unlookup(caller.clone()), Data::Raw(vec![0; 32]))?;
		ensure!(SuperOf::<T>::contains_key(&caller), "Sub doesn't exists");
	}: _(RawOrigin::Signed(caller.clone()))
	verify {
		ensure!(!SuperOf::<T>::contains_key(&caller), "Sub not removed");
	}

}

impl_benchmark_test_suite!(
	Identity,
	crate::tests::new_test_ext(),
	crate::tests::Test,
);
