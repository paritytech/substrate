// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Identity pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;

use frame_system::RawOrigin;
use sp_io::hashing::blake2_256;
use frame_benchmarking::benchmarks;
use sp_runtime::traits::Bounded;

use crate::Module as Identity;

// Support Functions
fn account<T: Trait>(name: &'static str, index: u32) -> T::AccountId {
	let entropy = (name, index).using_encoded(blake2_256);
	T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
}

// Adds `r` registrars to the Identity Pallet. These registrars will have set fees and fields.
fn add_registrars<T: Trait>(r: u32) -> Result<(), &'static str> {
	for i in 0..r {
		let _ = T::Currency::make_free_balance_be(&account::<T>("registrar", i), BalanceOf::<T>::max_value());
		Identity::<T>::add_registrar(RawOrigin::Root.into(), account::<T>("registrar", i))?;
		Identity::<T>::set_fee(RawOrigin::Signed(account::<T>("registrar", i)).into(), i.into(), 10.into())?;
		let fields = IdentityFields(
			IdentityField::Display | IdentityField::Legal | IdentityField::Web | IdentityField::Riot
			| IdentityField::Email | IdentityField::PgpFingerprint | IdentityField::Image | IdentityField::Twitter
		);
		Identity::<T>::set_fields(RawOrigin::Signed(account::<T>("registrar", i)).into(), i.into(), fields)?;
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
		let sub_account = account::<T>("sub", i);
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
			let caller = account::<T>("caller", 0);
			let _ = add_sub_accounts::<T>(&caller, s)?;
		};
		let x in 1 .. T::MaxAdditionalFields::get() => {
			// Create their main identity with x additional fields
			let info = create_identity_info::<T>(x);
			let caller = account::<T>("caller", 0);
			let caller_origin = <T as frame_system::Trait>::Origin::from(RawOrigin::Signed(caller));
			Identity::<T>::set_identity(caller_origin, info)?;
		};
	}

	add_registrar {
		let r in 1 .. T::MaxRegistrars::get() - 1 => add_registrars::<T>(r)?;
	}: _(RawOrigin::Root, account::<T>("registrar", r + 1))

	set_identity {
		let r in ...;
		// This X doesn't affect the caller ID up front like with the others, so we don't use the
		// standard preparation.
		let x in _ .. _ => ();
		let caller = {
			// The target user
			let caller = account::<T>("caller", 0);
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
					RawOrigin::Signed(account::<T>("registrar", i)).into(),
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

	set_subs {
		let caller = account::<T>("caller", 0);

		// Give them p many previous sub accounts.
		let p in 1 .. T::MaxSubAccounts::get() => {
			let _ = add_sub_accounts::<T>(&caller, p)?;
		};
		// Create a new subs vec with s sub accounts
		let s in 1 .. T::MaxSubAccounts::get() => ();
		let subs = create_sub_accounts::<T>(&caller, s)?;

	}: _(RawOrigin::Signed(caller), subs)

	clear_identity {
		let caller = account::<T>("caller", 0);
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
				RawOrigin::Signed(account::<T>("registrar", i)).into(),
				i,
				caller_lookup.clone(),
				Judgement::Reasonable
			)?;
		}
	}: _(RawOrigin::Signed(caller))

	request_judgement {
		let caller = account::<T>("caller", 0);
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r in ...;
		let x in ...;
	}: _(RawOrigin::Signed(caller), r - 1, 10.into())

	cancel_request {
		let caller = account::<T>("caller", 0);
		let caller_origin = <T as frame_system::Trait>::Origin::from(RawOrigin::Signed(caller.clone()));
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r in ...;
		let x in ...;

		Identity::<T>::request_judgement(caller_origin, r - 1, 10.into())?;
	}: _(RawOrigin::Signed(caller), r - 1)

	set_fee {
		let caller = account::<T>("caller", 0);

		let r in 1 .. T::MaxRegistrars::get() - 1 => add_registrars::<T>(r)?;

		Identity::<T>::add_registrar(RawOrigin::Root.into(), caller.clone())?;
	}: _(RawOrigin::Signed(caller), r, 10.into())

	set_account_id {
		let caller = account::<T>("caller", 0);
		let _ = T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());

		let r in 1 .. T::MaxRegistrars::get() - 1 => add_registrars::<T>(r)?;

		Identity::<T>::add_registrar(RawOrigin::Root.into(), caller.clone())?;
	}: _(RawOrigin::Signed(caller), r, account::<T>("new", 0))

	set_fields {
		let caller = account::<T>("caller", 0);
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
		let user = account::<T>("user", r);
		let user_origin = <T as frame_system::Trait>::Origin::from(RawOrigin::Signed(user.clone()));
		let user_lookup = <T::Lookup as StaticLookup>::unlookup(user.clone());
		let _ = T::Currency::make_free_balance_be(&user, BalanceOf::<T>::max_value());

		let caller = account::<T>("caller", 0);
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
		let caller = account::<T>("caller", 0);
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
				RawOrigin::Signed(account::<T>("registrar", i)).into(),
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
