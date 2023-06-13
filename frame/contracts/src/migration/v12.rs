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
	migration::{IsFinished, Migrate},
	storage::meter::Diff,
	weights::WeightInfo,
	AccountIdOf, BalanceOf, CodeHash, Config, Determinism, Pallet, Weight, LOG_TARGET,
};
use codec::{Decode, Encode};
use frame_support::{
	codec, pallet_prelude::*, storage_alias, traits::ReservableCurrency, BoundedVec,
	DefaultNoBound, Identity,
};
use scale_info::prelude::format;
#[cfg(feature = "try-runtime")]
use sp_runtime::TryRuntimeError;
use sp_runtime::{traits::Zero, Saturating};
use sp_std::{marker::PhantomData, prelude::*};

mod old {
	use super::*;

	#[derive(Encode, Decode, scale_info::TypeInfo)]
	#[codec(mel_bound())]
	#[scale_info(skip_type_params(T))]
	pub struct OwnerInfo<T: Config> {
		pub owner: AccountIdOf<T>,
		#[codec(compact)]
		pub deposit: BalanceOf<T>,
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
	pub type OwnerInfoOf<T: Config> = StorageMap<Pallet<T>, Identity, CodeHash<T>, OwnerInfo<T>>;

	#[storage_alias]
	pub type CodeStorage<T: Config> =
		StorageMap<Pallet<T>, Identity, CodeHash<T>, PrefabWasmModule>;
}

#[derive(Encode, Decode)]
pub struct CodeInfo<T: Config> {
	owner: AccountIdOf<T>,
	#[codec(compact)]
	deposit: BalanceOf<T>,
	#[codec(compact)]
	refcount: u64,
	determinism: Determinism,
}

type CodeVec<T> = BoundedVec<u8, <T as Config>::MaxCodeLen>;

#[storage_alias]
pub type CodeInfoOf<T: Config> = StorageMap<Pallet<T>, Twox64Concat, CodeHash<T>, CodeInfo<T>>;

#[storage_alias]
pub type PristineCode<T: Config> = StorageMap<Pallet<T>, Identity, CodeHash<T>, CodeVec<T>>;

#[derive(Encode, Decode, MaxEncodedLen, DefaultNoBound)]
pub struct Migration<T: Config> {
	last_key: Option<BoundedVec<u8, ConstU32<256>>>,
	_phantom: PhantomData<T>,
}

impl<T: Config> Migrate for Migration<T> {
	const VERSION: u16 = 12;

	fn max_step_weight() -> Weight {
		T::WeightInfo::v12_migration_step(T::MaxCodeLen::get())
	}

	fn step(&mut self) -> (IsFinished, Weight) {
		let mut iter = if let Some(last_key) = self.last_key.take() {
			PristineCode::<T>::iter_from(last_key.to_vec())
		} else {
			PristineCode::<T>::iter()
		};
		if let Some((hash, code)) = iter.next() {
			let old = old::OwnerInfoOf::<T>::take(hash)
				.expect(format!("OwnerInfo for code_hash {:?} not found!", hash).as_str());

			log::debug!(target: LOG_TARGET, "Migrating OwnerInfo for code_hash {:?}", hash);

			let module = old::CodeStorage::<T>::take(hash)
				.expect(format!("No PrefabWasmModule found for code_hash: {:?}", hash).as_str());

			// We print this to measure the impact of the migration.
			// Storage removed: deleted PrefabWasmModule's encoded len.
			// Storage added: determinism field encoded len (as all other CodeInfo fields are the
			// same as in the deleted OwnerInfo)
			log::debug!(
				target: LOG_TARGET,
				"Storage removed: 1 item, {} bytes",
				module.encoded_size().saturating_sub(Determinism::max_encoded_len())
			);

			let deposit =
				Diff { bytes_added: code.len() as u32, items_added: 2, ..Default::default() }
					.update_contract::<T>(None)
					.charge_or_zero();

			let info = CodeInfo {
				determinism: module.determinism,
				owner: old.owner,
				deposit,
				refcount: old.refcount,
			};

			let amount = old.deposit.saturating_sub(info.deposit);
			if !amount.is_zero() {
				T::Currency::unreserve(&info.owner, amount);
				log::debug!(
					target: LOG_TARGET,
					"Storage deposit unlocked: {:?} Balance, to: {:?}",
					&amount,
					&info.owner
				);
			} else {
				log::warn!(
					target: LOG_TARGET,
					"new deposit: {:?}, old deposit: {:?}",
					&info.deposit,
					&old.deposit
				);
			}
			CodeInfoOf::<T>::insert(hash, info);

			self.last_key = Some(iter.last_raw_key().to_vec().try_into().unwrap());

			// TODO: write benchmark and pass corrent len instead of freed_bytes
			(IsFinished::No, T::WeightInfo::v12_migration_step(42))
		} else {
			log::debug!(target: LOG_TARGET, "No more OwnerInfo to migrate");
			(IsFinished::Yes, T::WeightInfo::v12_migration_step(0))
		}
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade_step() -> Result<Vec<u8>, TryRuntimeError> {
		let len = 5;
		log::debug!(target: LOG_TARGET, "Taking sample of {} OwnerInfo(s)", len);
		let sample: Vec<_> = old::OwnerInfoOf::<T>::iter()
			.take(len)
			.map(|(k, v)| {
				let module = old::CodeStorage::<T>::get(k)
					.expect("No PrefabWasmModule found for code_hash: {:?}");
				let info: CodeInfo<T> = CodeInfo {
					determinism: module.determinism,
					deposit: v.deposit,
					refcount: v.refcount,
					owner: v.owner,
				};
				(k, info)
			})
			.collect();

		let storage: u32 = old::CodeStorage::<T>::iter().map(|(_k, v)| v.encoded_size() as u32).sum();
		let mut deposit: BalanceOf<T> = Default::default();
		old::OwnerInfoOf::<T>::iter().for_each(|(_k, v)| deposit += v.deposit);

		Ok((sample, deposit, storage).encode())
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade_step(state: Vec<u8>) -> Result<(), TryRuntimeError> {
		let state = <(Vec<(CodeHash<T>, CodeInfo<T>)>, BalanceOf<T>, u32) as Decode>::decode(
			&mut &state[..],
		)
		.unwrap();

		log::debug!(target: LOG_TARGET, "Validating state of {} Codeinfo(s)", state.0.len());
		for (hash, old) in state.0 {
			let info = CodeInfoOf::<T>::get(&hash)
				.expect(format!("CodeInfo for code_hash {:?} not found!", hash).as_str());
			ensure!(info.determinism == old.determinism, "invalid determinism");
			ensure!(info.owner == old.owner, "invalid owner");
//			ensure!(info.deposit == old.deposit, "invalid deposit");
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
		if let Some((k, _)) = old::OwnerInfoOf::<T>::iter().next() {
			log::warn!(
				target: LOG_TARGET,
				"OwnerInfoOf is still NOT empty, found code_hash: {:?}",
				k
			);
		} else {
			log::debug!(target: LOG_TARGET, "OwnerInfoOf is empty.");
		}

		let mut deposit: BalanceOf<T> = Default::default();
		let mut bytes = 0u32;
		CodeInfoOf::<T>::iter().for_each(|(_k, v)| {
			deposit += v.deposit;
			bytes += 1;
		});
		let old_deposit = state.1;
		let storage = state.2;

		log::info!(target: LOG_TARGET, "Storage freed, bytes: {}", storage.saturating_sub(bytes));
		log::info!(
			target: LOG_TARGET,
			"Deposits returned, total: {:?} Balance",
			old_deposit.saturating_sub(deposit)
		);

		Ok(())
	}
}
