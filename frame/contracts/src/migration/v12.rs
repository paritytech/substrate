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

//! Move `OwnerInfo` to `CodeInfo`, add `determinism` field to the latter, clear `CodeStorage` and
//! repay deposits.

use crate::{
	migration::{IsFinished, MigrationStep},
	weights::WeightInfo,
	AccountIdOf, BalanceOf, CodeHash, Config, Determinism, Pallet, Weight, LOG_TARGET,
};
use codec::{Decode, Encode};
use frame_support::{
	pallet_prelude::*, storage_alias, traits::ReservableCurrency, DefaultNoBound, Identity,
};
use scale_info::prelude::format;
use sp_core::hexdisplay::HexDisplay;
#[cfg(feature = "try-runtime")]
use sp_runtime::TryRuntimeError;
use sp_runtime::{traits::Zero, FixedPointNumber, FixedU128, Saturating};
use sp_std::prelude::*;

mod old {
	use super::*;

	pub type BalanceOf<T, OldCurrency> = <OldCurrency as frame_support::traits::Currency<
		<T as frame_system::Config>::AccountId,
	>>::Balance;

	#[derive(Encode, Decode, scale_info::TypeInfo, MaxEncodedLen)]
	#[codec(mel_bound())]
	#[scale_info(skip_type_params(T, OldCurrency))]
	pub struct OwnerInfo<T: Config, OldCurrency>
	where
		OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId>,
	{
		pub owner: AccountIdOf<T>,
		#[codec(compact)]
		pub deposit: BalanceOf<T, OldCurrency>,
		#[codec(compact)]
		pub refcount: u64,
	}

	#[derive(Encode, Decode, scale_info::TypeInfo)]
	#[codec(mel_bound())]
	#[scale_info(skip_type_params(T))]
	pub struct PrefabWasmModule {
		#[codec(compact)]
		pub instruction_weights_version: u32,
		#[codec(compact)]
		pub initial: u32,
		#[codec(compact)]
		pub maximum: u32,
		pub code: Vec<u8>,
		pub determinism: Determinism,
	}

	#[storage_alias]
	pub type OwnerInfoOf<T: Config, OldCurrency> =
		StorageMap<Pallet<T>, Identity, CodeHash<T>, OwnerInfo<T, OldCurrency>>;

	#[storage_alias]
	pub type CodeStorage<T: Config> =
		StorageMap<Pallet<T>, Identity, CodeHash<T>, PrefabWasmModule>;
}

#[derive(Encode, Decode, scale_info::TypeInfo, MaxEncodedLen)]
#[codec(mel_bound())]
#[scale_info(skip_type_params(T, OldCurrency))]
pub struct CodeInfo<T: Config, OldCurrency>
where
	OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId>,
{
	owner: AccountIdOf<T>,
	#[codec(compact)]
	deposit: old::BalanceOf<T, OldCurrency>,
	#[codec(compact)]
	refcount: u64,
	determinism: Determinism,
	code_len: u32,
}

#[storage_alias]
pub type CodeInfoOf<T: Config, OldCurrency> =
	StorageMap<Pallet<T>, Twox64Concat, CodeHash<T>, CodeInfo<T, OldCurrency>>;

#[storage_alias]
pub type PristineCode<T: Config> = StorageMap<Pallet<T>, Identity, CodeHash<T>, Vec<u8>>;

#[cfg(feature = "runtime-benchmarks")]
pub fn store_old_dummy_code<T: Config, OldCurrency>(len: usize, account: T::AccountId)
where
	OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId> + 'static,
{
	use sp_runtime::traits::Hash;

	let code = vec![42u8; len];
	let hash = T::Hashing::hash(&code);
	PristineCode::<T>::insert(hash, code.clone());

	let module = old::PrefabWasmModule {
		instruction_weights_version: Default::default(),
		initial: Default::default(),
		maximum: Default::default(),
		code,
		determinism: Determinism::Enforced,
	};
	old::CodeStorage::<T>::insert(hash, module);

	let info = old::OwnerInfo { owner: account, deposit: u32::MAX.into(), refcount: u64::MAX };
	old::OwnerInfoOf::<T, OldCurrency>::insert(hash, info);
}

#[derive(Encode, Decode, MaxEncodedLen, DefaultNoBound)]
pub struct Migration<T: Config, OldCurrency>
where
	OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId>,
	OldCurrency::Balance: From<BalanceOf<T>>,
{
	last_code_hash: Option<CodeHash<T>>,
	_phantom: PhantomData<OldCurrency>,
}

impl<T: Config, OldCurrency> MigrationStep for Migration<T, OldCurrency>
where
	OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId> + 'static,
	OldCurrency::Balance: From<BalanceOf<T>>,
{
	const VERSION: u16 = 12;

	fn max_step_weight() -> Weight {
		T::WeightInfo::v12_migration_step(T::MaxCodeLen::get())
	}

	fn step(&mut self) -> (IsFinished, Weight) {
		let mut iter = if let Some(last_key) = self.last_code_hash.take() {
			old::OwnerInfoOf::<T, OldCurrency>::iter_from(
				old::OwnerInfoOf::<T, OldCurrency>::hashed_key_for(last_key),
			)
		} else {
			old::OwnerInfoOf::<T, OldCurrency>::iter()
		};
		if let Some((hash, old_info)) = iter.next() {
			log::debug!(target: LOG_TARGET, "Migrating OwnerInfo for code_hash {:?}", hash);

			let module = old::CodeStorage::<T>::take(hash)
				.expect(format!("No PrefabWasmModule found for code_hash: {:?}", hash).as_str());

			let code_len = module.code.len();
			// We print this to measure the impact of the migration.
			// Storage removed: deleted PrefabWasmModule's encoded len.
			// Storage added: determinism field encoded len (as all other CodeInfo fields are the
			// same as in the deleted OwnerInfo).
			log::debug!(target: LOG_TARGET, "Storage removed: 1 item, {} bytes", &code_len,);

			// Storage usage prices could change over time, and accounts who uploaded their
			// contracts code before the storage deposits where introduced, had not been ever
			// charged with any deposit for that (see migration v6).
			//
			// This is why deposit to be refunded here is calculated as follows:
			//
			// 1. Calculate the deposit amount for storage before the migration, given current
			// prices.
			// 2. Given current reserved deposit amount, calculate the correction factor.
			// 3. Calculate the deposit amount for storage after the migration, given current
			// prices.
			// 4. Calculate real deposit amount to be reserved after the migration.
			let price_per_byte = T::DepositPerByte::get();
			let price_per_item = T::DepositPerItem::get();
			let bytes_before = module
				.encoded_size()
				.saturating_add(code_len)
				.saturating_add(old::OwnerInfo::<T, OldCurrency>::max_encoded_len())
				as u32;
			let items_before = 3u32;
			let deposit_expected_before = price_per_byte
				.saturating_mul(bytes_before.into())
				.saturating_add(price_per_item.saturating_mul(items_before.into()));
			let ratio = FixedU128::checked_from_rational(old_info.deposit, deposit_expected_before)
				.unwrap_or_default()
				.min(FixedU128::from_u32(1));
			let bytes_after =
				code_len.saturating_add(CodeInfo::<T, OldCurrency>::max_encoded_len()) as u32;
			let items_after = 2u32;
			let deposit_expected_after = price_per_byte
				.saturating_mul(bytes_after.into())
				.saturating_add(price_per_item.saturating_mul(items_after.into()));
			let deposit = ratio.saturating_mul_int(deposit_expected_after);

			let info = CodeInfo::<T, OldCurrency> {
				determinism: module.determinism,
				owner: old_info.owner,
				deposit: deposit.into(),
				refcount: old_info.refcount,
				code_len: code_len as u32,
			};

			let amount = old_info.deposit.saturating_sub(info.deposit);
			if !amount.is_zero() {
				OldCurrency::unreserve(&info.owner, amount);
				log::debug!(
					target: LOG_TARGET,
					"Deposit refunded: {:?} Balance, to: {:?}",
					&amount,
					HexDisplay::from(&info.owner.encode())
				);
			} else {
				log::warn!(
					target: LOG_TARGET,
					"new deposit: {:?} >= old deposit: {:?}",
					&info.deposit,
					&old_info.deposit
				);
			}
			CodeInfoOf::<T, OldCurrency>::insert(hash, info);

			self.last_code_hash = Some(hash);

			(IsFinished::No, T::WeightInfo::v12_migration_step(code_len as u32))
		} else {
			log::debug!(target: LOG_TARGET, "No more OwnerInfo to migrate");
			(IsFinished::Yes, T::WeightInfo::v12_migration_step(0))
		}
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade_step() -> Result<Vec<u8>, TryRuntimeError> {
		let len = 100;
		log::debug!(target: LOG_TARGET, "Taking sample of {} OwnerInfo(s)", len);
		let sample: Vec<_> = old::OwnerInfoOf::<T, OldCurrency>::iter()
			.take(len)
			.map(|(k, v)| {
				let module = old::CodeStorage::<T>::get(k)
					.expect("No PrefabWasmModule found for code_hash: {:?}");
				let info: CodeInfo<T, OldCurrency> = CodeInfo {
					determinism: module.determinism,
					deposit: v.deposit,
					refcount: v.refcount,
					owner: v.owner,
					code_len: module.code.len() as u32,
				};
				(k, info)
			})
			.collect();

		let storage: u32 =
			old::CodeStorage::<T>::iter().map(|(_k, v)| v.encoded_size() as u32).sum();
		let mut deposit: old::BalanceOf<T, OldCurrency> = Default::default();
		old::OwnerInfoOf::<T, OldCurrency>::iter().for_each(|(_k, v)| deposit += v.deposit);

		Ok((sample, deposit, storage).encode())
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade_step(state: Vec<u8>) -> Result<(), TryRuntimeError> {
		let state = <(
			Vec<(CodeHash<T>, CodeInfo<T, OldCurrency>)>,
			old::BalanceOf<T, OldCurrency>,
			u32,
		) as Decode>::decode(&mut &state[..])
		.unwrap();

		log::debug!(target: LOG_TARGET, "Validating state of {} Codeinfo(s)", state.0.len());
		for (hash, old) in state.0 {
			let info = CodeInfoOf::<T, OldCurrency>::get(&hash)
				.expect(format!("CodeInfo for code_hash {:?} not found!", hash).as_str());
			ensure!(info.determinism == old.determinism, "invalid determinism");
			ensure!(info.owner == old.owner, "invalid owner");
			ensure!(info.refcount == old.refcount, "invalid refcount");
		}

		if let Some((k, _)) = old::CodeStorage::<T>::iter().next() {
			log::warn!(
				target: LOG_TARGET,
				"CodeStorage is still NOT empty, found code_hash: {:?}",
				k
			);
		} else {
			log::debug!(target: LOG_TARGET, "CodeStorage is empty.");
		}
		if let Some((k, _)) = old::OwnerInfoOf::<T, OldCurrency>::iter().next() {
			log::warn!(
				target: LOG_TARGET,
				"OwnerInfoOf is still NOT empty, found code_hash: {:?}",
				k
			);
		} else {
			log::debug!(target: LOG_TARGET, "OwnerInfoOf is empty.");
		}

		let mut deposit: old::BalanceOf<T, OldCurrency> = Default::default();
		let mut items = 0u32;
		let mut storage_info = 0u32;
		CodeInfoOf::<T, OldCurrency>::iter().for_each(|(_k, v)| {
			deposit += v.deposit;
			items += 1;
			storage_info += v.encoded_size() as u32;
		});
		let mut storage_code = 0u32;
		PristineCode::<T>::iter().for_each(|(_k, v)| {
			storage_code += v.len() as u32;
		});
		let (_, old_deposit, storage_module) = state;
		// CodeInfoOf::max_encoded_len == OwnerInfoOf::max_encoded_len + 1
		// I.e. code info adds up 1 byte per record.
		let info_bytes_added = items.clone();
		// We removed 1 PrefabWasmModule, and added 1 byte of determinism flag, per contract code.
		let storage_removed = storage_module.saturating_sub(info_bytes_added);
		// module+code+info - bytes
		let storage_was = storage_module
			.saturating_add(storage_code)
			.saturating_add(storage_info)
			.saturating_sub(info_bytes_added);
		// We removed 1 storage item (PrefabWasmMod) for every stored contract code (was stored 3
		// items per code).
		let items_removed = items;
		log::info!(
			target: LOG_TARGET,
			"Storage freed, bytes: {} (of {}), items: {} (of {})",
			storage_removed,
			storage_was,
			items_removed,
			items_removed * 3,
		);
		log::info!(
			target: LOG_TARGET,
			"Deposits returned, total: {:?} Balance (of {:?} Balance)",
			old_deposit.saturating_sub(deposit),
			old_deposit,
		);

		Ok(())
	}
}
