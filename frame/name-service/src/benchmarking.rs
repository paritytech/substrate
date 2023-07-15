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

use super::{types::*, *};
use crate::Pallet as NameService;
use frame_benchmarking::{account, benchmarks, whitelisted_caller};
use frame_support::traits::{Currency, Get, ReservableCurrency};
use frame_system::{pallet_prelude::BlockNumberFor, Pallet as System, RawOrigin};
use sp_io::hashing::blake2_256;
use sp_runtime::traits::{Bounded, One};
use sp_std::vec;

type CurrencyOf<T> = <T as Config>::Currency;

fn safe_mint<T: Config>() -> BalanceOf<T> {
	CommitmentDeposit::<T>::get().unwrap() * 10000u32.into()
}

fn run_to_block<T: Config>(n: BlockNumberFor<T>) {
	while System::<T>::block_number() < n {
		NameService::<T>::on_finalize(System::<T>::block_number());
		System::<T>::set_block_number(System::<T>::block_number() + One::one());
		NameService::<T>::on_initialize(System::<T>::block_number());
	}
}

fn register_new_para<T: Config>() -> (BoundedSuffixOf<T>, u32) {
	let suffix: BoundedVec<u8, _> = BoundedVec::try_from("1234".as_bytes().to_vec()).unwrap();
	let para_id = u32::max_value();
	DomainRegistrations::<T>::insert(para_id, suffix.clone());
	ReverseDomainsLookup::<T>::insert(suffix.clone(), para_id);
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
		Some(BlockNumberFor::<T>::max_value())
	)
	verify {
		assert_eq!(
			Registrations::<T>::get(name_hash).unwrap(),
			Registration {
			owner: new_owner.clone(),
			expiry: Some(BlockNumberFor::<T>::max_value()),
			deposit: None,
		});
	}

	force_deregister {
		let recipient: T::AccountId = account("recipient", 0, 1u32);
		let (suffix, para_id) = register_new_para::<T>();
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
		let run_to: BlockNumberFor<T> = 100u32.into();
		run_to_block::<T>(run_to);
	}: _(RawOrigin::Signed(caller.clone()), name.to_vec(), secret, T::MaxRegistrationLength::get().into()
	)
	verify {
		// commitment has been removed.
		assert!(!Commitments::<T>::contains_key(hash));
		// registered name is now stored.
		assert!(
			Registrations::<T>::contains_key(NameService::<T>::name_hash(&name))
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
		assert_eq!(Registrations::<T>::get(name_hash).unwrap().owner, new_owner);
	}

	renew {
		let (name_hash, owner, _) = register_name_hash::<T>(
			account("recipient", 0, 1u32),
			vec![0; T::MaxNameLength::get() as usize],
			true
		);
	}: _(RawOrigin::Signed(owner.clone()), name_hash.clone(), T::MaxRegistrationLength::get()
)
	verify {
		assert_eq!(
			Registrations::<T>::get(name_hash).unwrap(),
			Registration {
			owner: owner,
			expiry: Some(BlockNumberFor::<T>::from(10512000u32)),
			deposit: Some(CommitmentDeposit::<T>::get().unwrap()),
		});
	}

	deregister {
		let recipient: T::AccountId = account("recipient", 0, 1u32);
		let (suffix, para_id) = register_new_para::<T>();
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
		let (suffix, para_id) = register_new_para::<T>();
		let (name_hash, owner, _) = register_name_hash::<T>(
			recipient.clone(),
			vec![0; T::MaxNameLength::get() as usize],
			true
		);
		let label = vec![0; l as usize];
	}: _(RawOrigin::Signed(owner.clone()), name_hash.clone(), label.clone())
	verify {
		let label_hash = blake2_256(&label);
		let subnode_hash = NameService::<T>::subnode_hash(name_hash, label_hash);

		assert_eq!(
			Registrations::<T>::get(subnode_hash).unwrap(),
			Registration {
			owner: owner,
			expiry: None,
			deposit: Some(CommitmentDeposit::<T>::get().unwrap()),
		});
	}

	deregister_subnode {
		let recipient: T::AccountId = account("recipient", 0, 1u32);
		let (suffix, para_id) = register_new_para::<T>();
		let (name_hash, owner, _) = register_name_hash::<T>(
			recipient.clone(),
			vec![0; T::MaxNameLength::get() as usize],
			true
		);

		let label = vec![0; T::MaxNameLength::get() as usize];
		let label_hash = blake2_256(&label);
		let origin = RawOrigin::Signed(owner.clone());
		NameService::<T>::set_subnode_record(
			origin.clone().into(),
			name_hash.clone(),
			label.clone(),
		).expect("Setting subnode record succeeds.");

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
	}: _(RawOrigin::Signed(owner.clone()), name_hash.clone(), label_hash.clone())
	verify {
		let subnode_hash = NameService::<T>::subnode_hash(name_hash, label_hash);

		assert!(!Registrations::<T>::contains_key(subnode_hash));
		assert!(!AddressResolver::<T>::contains_key(subnode_hash));
		assert!(!NameResolver::<T>::contains_key(subnode_hash));
		assert!(!TextResolver::<T>::contains_key(subnode_hash));
	}

	set_subnode_owner {
		let new_owner: T::AccountId = account("new_recipient", 0, 2u32);
		T::Currency::make_free_balance_be(&new_owner, safe_mint::<T>());

		let recipient: T::AccountId = account("recipient", 0, 1u32);
		let (suffix, para_id) = register_new_para::<T>();
		let (name_hash, owner, _) = register_name_hash::<T>(
			recipient.clone(),
			vec![0; T::MaxNameLength::get() as usize],
			true
		);
		let label = vec![0; T::MaxNameLength::get() as usize];
		let label_hash = blake2_256(&label);
		let origin = RawOrigin::Signed(owner.clone());
		NameService::<T>::set_subnode_record(
			origin.clone().into(),
			name_hash.clone(),
			label.clone(),
		).expect("Setting subnode record succeeds.");

	}: _(RawOrigin::Signed(owner.clone()), name_hash.clone(), label_hash.clone(), new_owner.clone())
	verify {
		let subnode_hash = NameService::<T>::subnode_hash(name_hash, label_hash);

		assert_eq!(
			Registrations::<T>::get(subnode_hash).unwrap(),
			Registration {
			owner: new_owner,
			expiry: None,
			deposit: Some(CommitmentDeposit::<T>::get().unwrap()),
		});
	}

	set_address {
		let recipient: T::AccountId = account("recipient", 0, 1u32);
		let (suffix, para_id) = register_new_para::<T>();
		let (name_hash, owner, _) = register_name_hash::<T>(
			recipient.clone(),
			vec![0; T::MaxNameLength::get() as usize],
			true
		);

		let origin = RawOrigin::Signed(owner.clone());

		NameService::<T>::set_address(
			origin.clone().into(),
			name_hash.clone(),
			recipient.clone(),
			suffix.clone()
		).expect("Setting address succeeds.");
	}: _(RawOrigin::Signed(owner.clone()), name_hash.clone(), recipient.clone(), suffix)
	verify {
		assert_eq!(
			AddressResolver::<T>::get(name_hash).unwrap(),
			(recipient, para_id)
		);
	}

	set_name {
		let l in 3..T::MaxNameLength::get();
		let name = vec![0; l as usize];

		let recipient: T::AccountId = account("recipient", 0, 1u32);
		let (suffix, para_id) = register_new_para::<T>();
		let (name_hash, owner, _) = register_name_hash::<T>(
			recipient.clone(),
			name.clone(),
			true
		);

		let origin = RawOrigin::Signed(owner.clone());
	}: _(RawOrigin::Signed(owner.clone()), name_hash.clone(), name.clone())
	verify {
		assert_eq!(
			NameService::<T>::name_hash(&NameResolver::<T>::get(name_hash).unwrap().bytes),
			name_hash
		);
	}

	set_text {
		let l in 3..T::MaxTextLength::get();
		let name = vec![0; T::MaxNameLength::get() as usize];
		let text = vec![0; l as usize];

		let recipient: T::AccountId = account("recipient", 0, 1u32);
		let (suffix, para_id) = register_new_para::<T>();
		let (name_hash, owner, _) = register_name_hash::<T>(
			recipient.clone(),
			name.clone(),
			true
		);

		let origin = RawOrigin::Signed(owner.clone());
	}: _(RawOrigin::Signed(owner.clone()), name_hash.clone(), text.clone())
	verify {
		assert_eq!(
			TextResolver::<T>::get(name_hash).unwrap().bytes,
			text
		);
	}

	set_configs {
	}:_(
		RawOrigin::Root,
		ConfigOp::Set(BalanceOf::<T>::max_value()),
		ConfigOp::Set(BalanceOf::<T>::max_value()),
		ConfigOp::Set(BalanceOf::<T>::max_value()),
		ConfigOp::Set(BalanceOf::<T>::max_value()),
		ConfigOp::Set(BalanceOf::<T>::max_value()),
		ConfigOp::Set(BalanceOf::<T>::max_value()),
		ConfigOp::Set(BalanceOf::<T>::max_value())
	) verify {
		assert_eq!(CommitmentDeposit::<T>::get(), Some(BalanceOf::<T>::max_value()));
		assert_eq!(SubNodeDeposit::<T>::get(), Some(BalanceOf::<T>::max_value()));
		assert_eq!(TierThreeLetters::<T>::get(), BalanceOf::<T>::max_value());
		assert_eq!(TierFourLetters::<T>::get(), BalanceOf::<T>::max_value());
		assert_eq!(TierDefault::<T>::get(), BalanceOf::<T>::max_value());
		assert_eq!(RegistrationFeePerBlock::<T>::get(), BalanceOf::<T>::max_value());
		assert_eq!(PerByteFee::<T>::get(), BalanceOf::<T>::max_value());
	}

	register_domain {
		let suffix: BoundedVec<u8, _> = BoundedVec::try_from("1234".as_bytes().to_vec()).unwrap();
		let para_id = u32::max_value();
	}:_(RawOrigin::Root, Domain {
		id: para_id,
		suffix: suffix.clone(),
	})
	verify {
		assert_eq!(DomainRegistrations::<T>::get(para_id).unwrap(), suffix.clone());
		assert_eq!(ReverseDomainsLookup::<T>::get(suffix.clone()).unwrap(), para_id);
	}

	deregister_domain {
		let (suffix, para_id) = register_new_para::<T>();
	}: _(RawOrigin::Root, u32::max_value())
	verify {
		assert!(!DomainRegistrations::<T>::contains_key(para_id));
	}

	impl_benchmark_test_suite!(NameService, crate::mock::new_test_ext(), crate::mock::Test);
}
