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

//! Update the code owner balance, make the code upload deposit balance to be held instead of
//! reserved. Since [`Currency`](frame_support::traits::Currency) has been
//! [deprecated](https://github.com/paritytech/substrate/pull/12951), we need the deposits to be
//! handled by the [`frame_support::traits::fungible`] traits.

use crate::{
	exec::AccountIdOf,
	migration::{IsFinished, MigrationStep},
	weights::WeightInfo,
	BalanceOf, CodeHash, Config, Determinism, HoldReason, Pallet, Weight, LOG_TARGET,
};
use codec::{Decode, Encode};
#[cfg(feature = "try-runtime")]
use environmental::Vec;
#[cfg(feature = "try-runtime")]
use frame_support::traits::fungible::{Inspect, InspectHold};
use frame_support::{
	codec,
	pallet_prelude::*,
	storage_alias,
	traits::{fungible::MutateHold, ReservableCurrency},
	DefaultNoBound,
};
use sp_core::hexdisplay::HexDisplay;
#[cfg(feature = "try-runtime")]
use sp_runtime::TryRuntimeError;
use sp_runtime::{traits::Zero, Saturating};
#[cfg(feature = "try-runtime")]
use sp_std::collections::btree_map::BTreeMap;

mod old {
	use super::*;

	pub type BalanceOf<T, OldCurrency> = <OldCurrency as frame_support::traits::Currency<
		<T as frame_system::Config>::AccountId,
	>>::Balance;

	#[derive(Encode, Decode, scale_info::TypeInfo, MaxEncodedLen)]
	#[codec(mel_bound())]
	#[scale_info(skip_type_params(T, OldCurrency))]
	pub struct CodeInfo<T, OldCurrency>
	where
		T: Config,
		OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId>,
	{
		pub owner: AccountIdOf<T>,
		#[codec(compact)]
		pub deposit: old::BalanceOf<T, OldCurrency>,
		#[codec(compact)]
		pub refcount: u64,
		pub determinism: Determinism,
		pub code_len: u32,
	}

	#[storage_alias]
	pub type CodeInfoOf<T: Config, OldCurrency> =
		StorageMap<Pallet<T>, Twox64Concat, CodeHash<T>, CodeInfo<T, OldCurrency>>;
}

#[cfg(feature = "runtime-benchmarks")]
pub fn store_dummy_code<T: Config, OldCurrency>(account: T::AccountId)
where
	T: Config,
	OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId> + 'static,
{
	use sp_runtime::traits::Hash;
	use sp_std::vec;

	let len = T::MaxCodeLen::get();
	let code = vec![42u8; len as usize];
	let hash = T::Hashing::hash(&code);

	let info = old::CodeInfo {
		owner: account,
		deposit: 10_000u32.into(),
		refcount: u64::MAX,
		determinism: Determinism::Enforced,
		code_len: len,
	};
	old::CodeInfoOf::<T, OldCurrency>::insert(hash, info);
}

#[cfg(feature = "try-runtime")]
#[derive(Encode, Decode)]
/// Accounts for the balance allocation of a code owner.
struct BalanceAllocation<T, OldCurrency>
where
	T: Config,
	OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId>,
{
	/// Total reserved balance as code upload deposit for the owner.
	reserved: old::BalanceOf<T, OldCurrency>,
	/// Total balance of the owner.
	total: old::BalanceOf<T, OldCurrency>,
}

#[derive(Encode, Decode, MaxEncodedLen, DefaultNoBound)]
pub struct Migration<T, OldCurrency>
where
	T: Config,
	OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId>,
{
	last_code_hash: Option<CodeHash<T>>,
	_phantom: PhantomData<(T, OldCurrency)>,
}

impl<T, OldCurrency> MigrationStep for Migration<T, OldCurrency>
where
	T: Config,
	OldCurrency: 'static + ReservableCurrency<<T as frame_system::Config>::AccountId>,
	BalanceOf<T>: From<OldCurrency::Balance>,
{
	const VERSION: u16 = 14;

	fn max_step_weight() -> Weight {
		T::WeightInfo::v14_migration_step()
	}

	fn step(&mut self) -> (IsFinished, Weight) {
		let mut iter = if let Some(last_hash) = self.last_code_hash.take() {
			old::CodeInfoOf::<T, OldCurrency>::iter_from(
				old::CodeInfoOf::<T, OldCurrency>::hashed_key_for(last_hash),
			)
		} else {
			old::CodeInfoOf::<T, OldCurrency>::iter()
		};

		if let Some((hash, code_info)) = iter.next() {
			log::debug!(target: LOG_TARGET, "Migrating code upload deposit for 0x{:?}", HexDisplay::from(&code_info.owner.encode()));

			let remaining = OldCurrency::unreserve(&code_info.owner, code_info.deposit);

			if remaining > Zero::zero() {
				log::warn!(
					target: LOG_TARGET,
					"Code owner's account 0x{:?} for code {:?} has some non-unreservable deposit {:?} from a total of {:?} that will remain in reserved.",
					HexDisplay::from(&code_info.owner.encode()),
					hash,
					remaining,
					code_info.deposit
				);
			}

			let unreserved = code_info.deposit.saturating_sub(remaining);
			let amount = BalanceOf::<T>::from(unreserved);

			log::debug!(
				target: LOG_TARGET,
				"Holding {:?} on the code owner's account 0x{:?} for code {:?}.",
				amount,
				HexDisplay::from(&code_info.owner.encode()),
				hash,
			);

			T::Currency::hold(
				&HoldReason::CodeUploadDepositReserve.into(),
				&code_info.owner,
				amount,
			)
			.unwrap_or_else(|err| {
				log::error!(
					target: LOG_TARGET,
					"Failed to hold {:?} from the code owner's account 0x{:?} for code {:?}, reason: {:?}.",
					amount,
					HexDisplay::from(&code_info.owner.encode()),
					hash,
					err
				);
			});

			self.last_code_hash = Some(hash);
			(IsFinished::No, T::WeightInfo::v14_migration_step())
		} else {
			log::debug!(target: LOG_TARGET, "No more code upload deposit to migrate");
			(IsFinished::Yes, T::WeightInfo::v14_migration_step())
		}
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade_step() -> Result<Vec<u8>, TryRuntimeError> {
		let info: Vec<_> = old::CodeInfoOf::<T, OldCurrency>::iter().collect();

		let mut owner_balance_allocation =
			BTreeMap::<AccountIdOf<T>, BalanceAllocation<T, OldCurrency>>::new();

		// Calculates the balance allocation by accumulating the code upload deposits of all codes
		// owned by an owner.
		for (_, code_info) in info {
			owner_balance_allocation
				.entry(code_info.owner.clone())
				.and_modify(|alloc| {
					alloc.reserved = alloc.reserved.saturating_add(code_info.deposit);
				})
				.or_insert(BalanceAllocation {
					reserved: code_info.deposit,
					total: OldCurrency::total_balance(&code_info.owner),
				});
		}

		Ok(owner_balance_allocation.encode())
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade_step(state: Vec<u8>) -> Result<(), TryRuntimeError> {
		let owner_balance_allocation =
			<BTreeMap<AccountIdOf<T>, BalanceAllocation<T, OldCurrency>> as Decode>::decode(
				&mut &state[..],
			)
			.expect("pre_upgrade_step provides a valid state; qed");

		let mut total_held: BalanceOf<T> = Zero::zero();
		let count = owner_balance_allocation.len();
		for (owner, old_balance_allocation) in owner_balance_allocation {
			let held =
				T::Currency::balance_on_hold(&HoldReason::CodeUploadDepositReserve.into(), &owner);
			log::debug!(
				target: LOG_TARGET,
				"Validating code upload deposit for owner 0x{:?}, reserved: {:?}, held: {:?}",
				HexDisplay::from(&owner.encode()),
				old_balance_allocation.reserved,
				held
			);
			ensure!(held == old_balance_allocation.reserved.into(), "Held amount mismatch");

			log::debug!(
				target: LOG_TARGET,
				"Validating total balance for owner 0x{:?}, new: {:?}, old: {:?}",
				HexDisplay::from(&owner.encode()),
				T::Currency::total_balance(&owner),
				old_balance_allocation.total
			);
			ensure!(
				T::Currency::total_balance(&owner) ==
					BalanceOf::<T>::decode(&mut &old_balance_allocation.total.encode()[..])
						.unwrap(),
				"Balance mismatch "
			);
			total_held += held;
		}

		log::info!(
			target: LOG_TARGET,
			"Code owners processed: {:?}.",
			count
		);

		log::info!(
			target: LOG_TARGET,
			"Total held amount for code upload deposit: {:?}",
			total_held
		);

		Ok(())
	}
}
