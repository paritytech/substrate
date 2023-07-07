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

//! Benchmarks for the name service pallet.

#![cfg(feature = "runtime-benchmarks")]
#![cfg_attr(not(feature = "std"), no_std)]

use super::{types::*, *};
use frame_benchmarking::{account, benchmarks, whitelisted_caller};
use frame_support::traits::{Currency, Get, ReservableCurrency};
use frame_system::{Pallet as System, RawOrigin};
use sp_runtime::traits::{Bounded, One};
use sp_std::vec;
// use sp_io::hashing::blake2_256;
use crate::Pallet as NameService;

type CurrencyOf<T> = <T as Config>::Currency;

fn safe_mint<T: Config>() -> BalanceOf<T> {
	CommitmentDeposit::<T>::get().unwrap() * 100u32.into()
}

fn run_to_block<T: Config>(n: T::BlockNumber) {
	while System::<T>::block_number() < n {
		NameService::<T>::on_finalize(System::<T>::block_number());
		System::<T>::set_block_number(System::<T>::block_number() + One::one());
		NameService::<T>::on_initialize(System::<T>::block_number());
	}
}

fn register_para<T: Config>() -> (BoundedSuffixOf<T>, u32) {
	let suffix: BoundedVec<u8, _> = BoundedVec::try_from("dot".as_bytes().to_vec()).unwrap();
	let para_id = 1;
	ParaRegistrations::<T>::insert(para_id, suffix.clone());
	ReverseParaRegistrationsLookup::<T>::insert(suffix.clone(), para_id);
	(suffix, para_id)
}

fn register_name_hash<T: Config>(
	owner: T::AccountId,
	name: Vec<u8>,
	do_reveal: bool,
) -> (NameHash, T::AccountId, T::AccountId) {
	let caller = whitelisted_caller();
	let secret = 3_u64;
	T::Currency::make_free_balance_be(&caller, safe_mint::<T>());
	T::Currency::make_free_balance_be(&owner, safe_mint::<T>());

	let commitment_hash: CommitmentHash = NameService::<T>::commitment_hash(&name, secret.clone());
	let origin = RawOrigin::Signed(caller.clone());

	let _ = NameService::<T>::commit(origin.clone().into(), owner.clone(), commitment_hash.clone())
		.expect("Commit succeeds.");

	if do_reveal == true {
		run_to_block::<T>(System::<T>::block_number() + 100u32.into());
		let _ = NameService::<T>::reveal(origin.into(), name.clone(), secret, 100u32.into())
			.expect("Reveal succeeds");
	}

	(NameService::<T>::name_hash(&name), owner, caller)
}

benchmarks! {
	force_register {
		let (name_hash, owner, _) = register_name_hash::<T>(
			account("recipient", 0, 1u32),
			vec![0; T::MaxNameLength::get() as usize],
			true
		);
		let new_owner: T::AccountId = account("new_recipient", 0, 2u32);
		T::Currency::make_free_balance_be(&new_owner, safe_mint::<T>());

		assert_eq!(
			CurrencyOf::<T>::reserved_balance(&owner),
			CommitmentDeposit::<T>::get().unwrap()
		);

		let registration = Registrations::<T>::get(&name_hash).unwrap();
		assert_eq!(registration.deposit.unwrap(), CommitmentDeposit::<T>::get().unwrap());
		assert_eq!(registration.owner, owner);

	}: _(
		RawOrigin::Root,
		name_hash.clone(),
		new_owner.clone(),
		Some(T::BlockNumber::max_value())
	)
	verify {
		assert_eq!(
			Registrations::<T>::get(name_hash).unwrap(),
			Registration {
			owner: new_owner.clone(),
			expiry: Some(T::BlockNumber::max_value()),
			deposit: None,
		});
	}

	force_deregister {
		let recipient: T::AccountId = account("recipient", 0, 1u32);

		let (suffix, para_id) = register_para::<T>();
		let (name_hash, owner, _) = register_name_hash::<T>(
			recipient.clone(),
			vec![0; T::MaxNameLength::get() as usize],
			true
		);

		let origin = RawOrigin::Signed(owner.clone());

		NameService::<T>::set_address(
			origin.clone().into(),
			name_hash.clone(),
			recipient,
			suffix
		).expect("Setting address succeeds.");

		NameService::<T>::set_name(
			origin.clone().into(),
			name_hash.clone(),
			vec![0; T::MaxNameLength::get() as usize].into()
		).expect("Setting name succeeds.");

		NameService::<T>::set_text(
			origin.clone().into(),
			name_hash.clone(),
			vec![0; T::MaxTextLength::get() as usize].into()
		).expect("Setting text succeeds.");

	}: _(RawOrigin::Root, name_hash.clone())
	verify {
		assert!(!Registrations::<T>::contains_key(name_hash));
		assert!(!AddressResolver::<T>::contains_key(name_hash));
		assert!(!NameResolver::<T>::contains_key(name_hash));
		assert!(!TextResolver::<T>::contains_key(name_hash));
	}

	commit {
		let caller = whitelisted_caller();
		let owner: T::AccountId = account("recipient", 0, 1u32);
		T::Currency::make_free_balance_be(&caller, safe_mint::<T>());
		T::Currency::make_free_balance_be(&owner, safe_mint::<T>());

		let name = vec![0; T::MaxNameLength::get() as usize];
		let secret = 3_u64;
		let hash = NameService::<T>::commitment_hash(&name, secret.clone());

	}: _(RawOrigin::Signed(caller.clone()), owner, hash.clone())
	verify {
		// commitment is now being stored.
		assert!(Commitments::<T>::contains_key(hash));
	}

	reveal {
		let l in 3..T::MaxNameLength::get();

		// Fund the account
		let balance = BalanceOf::<T>::max_value();
		let caller = whitelisted_caller();
		let owner: T::AccountId = account("recipient", 0, 1u32);
		T::Currency::make_free_balance_be(&caller, safe_mint::<T>());
		T::Currency::make_free_balance_be(&owner, safe_mint::<T>());

		let name = vec![0; l as usize];
		let secret = 3_u64;

		// Commit
		let hash: CommitmentHash = NameService::<T>::commitment_hash(&name, secret);
		let origin = RawOrigin::Signed(caller.clone());
		NameService::<T>::commit(origin.into(), owner.clone(), hash.clone()).expect("Must commit");
		let run_to: T::BlockNumber = 100u32.into();
		run_to_block::<T>(run_to);

	}: _(RawOrigin::Signed(caller.clone()), name.to_vec(), secret, 100u32.into()
	)
	verify {
		// commitment has been removed.
		assert!(!Commitments::<T>::contains_key(hash));
		// registered name is now stored.
		assert!(
			Registrations::<T>::contains_key(NameService::<T>::name_hash(&name))
		);
		// fees have been deducted from fee payer.
		assert_eq!(
			CurrencyOf::<T>::free_balance(&caller),
			(safe_mint::<T>()) - CommitmentDeposit::<T>::get().unwrap() - 100u32.into()
		);
	}

	remove_commitment {
		let caller = whitelisted_caller();
		let name = vec![0; T::MaxNameLength::get() as usize];
		T::Currency::make_free_balance_be(&caller, safe_mint::<T>());
		let commitment_hash: CommitmentHash = NameService::<T>::commitment_hash(&name, 3_u64);

		let _ = NameService::<T>::commit(
			RawOrigin::Signed(caller.clone()).into(),
			caller.clone(),
			commitment_hash.clone()
		).expect("Commit succeeds.");
		run_to_block::<T>(System::<T>::block_number() + 200u32.into());
	}: _(RawOrigin::Signed(caller.clone()), commitment_hash.clone())
	verify {
		assert!(!Commitments::<T>::contains_key(commitment_hash));
	}

	transfer {
		let (name_hash, owner, _) = register_name_hash::<T>(
			account("recipient", 0, 1u32),
			vec![0; T::MaxNameLength::get() as usize],
			true
		);
		let new_owner: T::AccountId = account("new_recipient", 0, 2u32);
		T::Currency::make_free_balance_be(&new_owner, safe_mint::<T>());

	}: _(RawOrigin::Signed(owner.clone()), new_owner.clone(), name_hash.clone())
	verify {
		assert_eq!(
			Registrations::<T>::get(name_hash).unwrap(),
			Registration {
			owner: new_owner,
			expiry: Some(200u32.into()),
			deposit: Some(CommitmentDeposit::<T>::get().unwrap()),
		});
	}

	renew {
		let (name_hash, owner, _) = register_name_hash::<T>(
			account("recipient", 0, 1u32),
			vec![0; T::MaxNameLength::get() as usize],
			true
		);
	}: _(RawOrigin::Signed(owner.clone()), name_hash.clone(), T::BlockNumber::max_value())
	verify {
		assert_eq!(
			Registrations::<T>::get(name_hash).unwrap(),
			Registration {
			owner: owner,
			expiry: Some(T::BlockNumber::max_value()),
			deposit: Some(CommitmentDeposit::<T>::get().unwrap()),
		});
	}

	deregister {
		let recipient: T::AccountId = account("recipient", 0, 1u32);
		let (suffix, para_id) = register_para::<T>();
		let (name_hash, owner, _) = register_name_hash::<T>(
			recipient.clone(),
			vec![0; T::MaxNameLength::get() as usize],
			true
		);
		let origin = RawOrigin::Signed(owner.clone());
		NameService::<T>::set_address(
			origin.clone().into(),
			name_hash.clone(),
			recipient,
			suffix
		).expect("Setting address succeeds.");

		NameService::<T>::set_name(
			origin.clone().into(),
			name_hash.clone(),
			vec![0; T::MaxNameLength::get() as usize].into()
		).expect("Setting name succeeds.");

		NameService::<T>::set_text(
			origin.clone().into(),
			name_hash.clone(),
			vec![0; T::MaxTextLength::get() as usize].into()
		).expect("Setting text succeeds.");

	}:_(RawOrigin::Signed(owner.clone()), name_hash.clone())
	verify {
		assert!(!Registrations::<T>::contains_key(name_hash));
		assert!(!AddressResolver::<T>::contains_key(name_hash));
		assert!(!NameResolver::<T>::contains_key(name_hash));
		assert!(!TextResolver::<T>::contains_key(name_hash));
	}

	set_subnode_record {
		let l in 3..T::MaxNameLength::get();

		let recipient: T::AccountId = account("recipient", 0, 1u32);
		let (suffix, para_id) = register_para::<T>();
		let (name_hash, owner, _) = register_name_hash::<T>(
			recipient.clone(),
			vec![0; T::MaxNameLength::get() as usize],
			true
		);
		let label = vec![0; l as usize];

		let origin = RawOrigin::Signed(owner.clone());
	}: _(RawOrigin::Signed(owner.clone()), name_hash.clone(), label.clone())
	verify {
		let label_hash = sp_io::hashing::blake2_256(&label);
		let name_hash = NameService::<T>::subnode_hash(name_hash, label_hash);

		assert_eq!(
			Registrations::<T>::get(name_hash).unwrap(),
			Registration {
			owner: owner,
			expiry: None,
			deposit: Some(CommitmentDeposit::<T>::get().unwrap()),
		});
	}

	impl_benchmark_test_suite!(NameService, crate::mock::new_test_ext(), crate::mock::Test);
}
