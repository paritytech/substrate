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

//! Update the code owner balance, make the storage deposit reserved balance to be held instead.

use crate::{
	exec::AccountIdOf,
	migration::{IsFinished, MigrationStep},
	weights::WeightInfo,
	BalanceOf, CodeHash, Config, Determinism, HoldReason, Pallet, Weight, LOG_TARGET,
};
use codec::{Decode, Encode};
use frame_support::{
	codec,
	pallet_prelude::*,
	storage_alias,
	traits::{fungible::MutateHold, ReservableCurrency},
	DefaultNoBound, Identity,
};
use sp_core::hexdisplay::HexDisplay;
use sp_runtime::Saturating;

mod old {
	use super::*;

	pub type BalanceOf<T, OldCurrency> = <OldCurrency as frame_support::traits::Currency<
		<T as frame_system::Config>::AccountId,
	>>::Balance;

	#[derive(Clone, Encode, Decode, scale_info::TypeInfo, MaxEncodedLen)]
	#[codec(mel_bound())]
	#[scale_info(skip_type_params(T, OldCurrency))]
	pub struct CodeInfo<T: Config, OldCurrency>
	where
		OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId>,
	{
		pub owner: AccountIdOf<T>,
		#[codec(compact)]
		pub deposit: BalanceOf<T, OldCurrency>,
		#[codec(compact)]
		refcount: u64,
		determinism: Determinism,
		pub code_len: u32,
	}

	#[storage_alias]
	pub type CodeInfoOf<T: Config, OldCurrency> =
		StorageMap<Pallet<T>, Identity, CodeHash<T>, CodeInfo<T, OldCurrency>>;
}

#[derive(Encode, Decode, MaxEncodedLen, DefaultNoBound)]
pub struct Migration<T: Config, OldCurrency>
where
	OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId>,
{
	last_code_hash: Option<CodeHash<T>>,
	_phantom: PhantomData<(T, OldCurrency)>,
}

impl<T: Config, OldCurrency: 'static> MigrationStep for Migration<T, OldCurrency>
where
	OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId>,
	BalanceOf<T>: From<old::BalanceOf<T, OldCurrency>>,
{
	const VERSION: u16 = 13;

	fn max_step_weight() -> Weight {
		T::WeightInfo::v9_migration_step(T::MaxCodeLen::get()) // TODO
	}

	fn step(&mut self) -> (IsFinished, Weight) {
		let mut iter = if let Some(last_key) = self.last_code_hash.take() {
			old::CodeInfoOf::<T, OldCurrency>::iter_from(
				old::CodeInfoOf::<T, OldCurrency>::hashed_key_for(last_key),
			)
		} else {
			old::CodeInfoOf::<T, OldCurrency>::iter()
		};

		if let Some((key, code_info)) = iter.next() {
			log::debug!(target: LOG_TARGET, "Migrating storage deposit for {:?}", code_info.owner);
			let len = code_info.code_len as u32;
			let unreserved = OldCurrency::unreserve(&code_info.owner, code_info.deposit);

			if code_info.deposit > unreserved {
				log::warn!(
					target: LOG_TARGET,
					"Code owner's account 0x{:?} for code {:?} has some non-unreservable deposit {:?} from a total of {:?} that will remain in reserved.",
					HexDisplay::from(&code_info.owner.encode()),
					key,
					code_info.deposit.saturating_sub(unreserved),
					code_info.deposit
				);
			}

			T::Currency::hold(
				&HoldReason::StorageDepositReserve.into(),
				&code_info.owner,
				unreserved.into(),
			)
			.map(|_| {
				log::debug!(
					target: LOG_TARGET,
					"{:?} held on the code owner's account 0x{:?} for code {:?}.",
					unreserved,
					HexDisplay::from(&code_info.owner.encode()),
					key,
				);
			})
			.unwrap_or_else(|err| {
				log::error!(
					target: LOG_TARGET,
					"Failed to hold {:?} from the code owner's account 0x{:?} for code {:?}, reason: {:?}.",
					unreserved,
					HexDisplay::from(&code_info.owner.encode()),
					key,
					err
				);
			});

			self.last_code_hash = Some(key);
			(IsFinished::No, T::WeightInfo::v9_migration_step(len)) // TODO
		} else {
			log::debug!(target: LOG_TARGET, "No more storage deposit to migrate");
			(IsFinished::Yes, T::WeightInfo::v9_migration_step(0)) // TODO
		}
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade_step() -> Result<Vec<u8>, TryRuntimeError> {
		let sample: Vec<_> = old::CodeInfoOf::<T, OldCurrency>::iter().take(100).collect();

		log::debug!(target: LOG_TARGET, "Taking sample of {} contracts", sample.len());
		Ok(sample.encode())
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade_step(state: Vec<u8>) -> Result<(), TryRuntimeError> {
		let sample = <Vec<(CodeHash<T>, old::CodeInfoOf<T, OldCurrency>)> as Decode>::decode(
			&mut &state[..],
		)
		.expect("pre_upgrade_step provides a valid state; qed");

		log::debug!(target: LOG_TARGET, "Validating sample of {} contracts", sample.len());

		// Keep the sum of the storage deposits of all codes owned by an owner.
		let mut owner_storage_deposits = HashMap::<T::AccountId, BalanceOf<T>>::new();

		for (_, old_code_info) in sample {
			*owner_storage_deposits
				.entry(old_code_info.owner)
				.or_insert(BalanceOf::<T>::zero()) += old_code_info.deposit.into();
		}

		for (&owner, &reserved) in owner_storage_deposits {
			let held =
				T::Currency::balance_on_hold(&HoldReason::StorageDepositReserve.into(), &owner);
			ensure!(
				held == reserved,
				"Held amount mismatch for owner 0x{:?}: expected {:?}, got {:?}",
				HexDisplay::from(&owner.encode()),
				reserved,
				held
			);
			ensure!(
				OldCurrency::total_balance(owner).into() == T::Currency::balance(owner),
				"Balance mismatch for owner 0x{:?}: old balance {:?}, new balance {:?}",
				HexDisplay::from(&owner.encode()),
				OldCurrency::total_balance(owner),
				T::Currency::balance(owner)
			);
		}

		Ok(())
	}
}
