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

//! Move the `determinism` field to `CodeInfo` (ex. `OwnerInfo`), remove `CodeStorage` and repay
//! deposits.

use crate::{
	migration::{IsFinished, Migrate},
	weights::WeightInfo,
	AccountIdOf, BalanceOf, CodeHash, Config, Determinism, Pallet, Weight, LOG_TARGET,
};

use codec::{Decode, Encode};
use frame_support::{
	codec, pallet_prelude::*, storage_alias, BoundedVec, DefaultNoBound, Identity,
};
#[cfg(feature = "try-runtime")]
use sp_runtime::TryRuntimeError;
use sp_std::{marker::PhantomData, prelude::*};

mod old {
	use super::*;

	#[derive(Encode, Decode)]
	pub struct OwnerInfo<T: Config> {
		pub owner: AccountIdOf<T>,
		#[codec(compact)]
		pub deposit: BalanceOf<T>,
		#[codec(compact)]
		pub refcount: u64,
	}

	#[derive(Encode, Decode)]
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
	pub type OwnerInfoOf<T: Config> =
		StorageMap<Pallet<T>, Twox64Concat, CodeHash<T>, OwnerInfo<T>>;

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

#[storage_alias]
pub type CodeInfoOf<T: Config> = StorageMap<Pallet<T>, Twox64Concat, CodeHash<T>, CodeInfo<T>>;

#[cfg(feature = "runtime-benchmarks")]
pub fn store_old_owner_info<T: Config>(len: usize) {
	use sp_runtime::traits::Hash;
	let info = old::OnwerInfo {
		owner: Default::default(),
		deposit: BalanceOf::<T>::max(),
		refcount: u64::MAX,
	};
	let hash = T::Hashing::hash(&info.owner.into());
	old::OwnerInfoOf::<T>::insert(hash, info);
}

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
			old::OwnerInfoOf::<T>::iter_from(last_key.to_vec())
		} else {
			old::OwnerInfoOf::<T>::iter()
		};

		if let Some((key, old)) = iter.next() {
			log::debug!(target: LOG_TARGET, "Migrating OwnerInfo for code_hash {:?}", key);
			let module = old::CodeStorage::<T>::take(key).unwrap_or_else(|| {
				log::error!(
					target: LOG_TARGET,
					"No PrefabWasmModule found for code_hash: {:?}",
					key
				);
				panic!();
			});
			let freed_bytes = module.encode().len();
			log::debug!(
				target: LOG_TARGET,
				"Freed 1 storage item with size (in bytes): {:?}",
				freed_bytes
			);

			// TODO: remove this, as calculated determinism added bytes
			let freed_bytes = old.encode().len();

			let info = CodeInfo {
				determinism: module.determinism,
				owner: old.owner,
				deposit: old.deposit,
				refcount: old.refcount,
			};

			let occupied_bytes = info.encode().len() - freed_bytes;

			CodeInfoOf::<T>::insert(key, info);
			log::debug!(
				target: LOG_TARGET,
				"Occupied more (for storing determinism) bytes: {:?}",
				occupied_bytes
			);

			self.last_key = Some(iter.last_raw_key().to_vec().try_into().unwrap());

			// TODO: repay deposit
			// TODO: write benchmark and pass corrent len instead of freed_bytes
			(IsFinished::No, T::WeightInfo::v12_migration_step(freed_bytes as u32))
		} else {
			log::debug!(target: LOG_TARGET, "No more owner_info to migrate");
			(IsFinished::Yes, T::WeightInfo::v12_migration_step(0))
		}
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade_step() -> Result<Vec<u8>, TryRuntimeError> {
		let sample: Vec<_> = old::OwnerInfoOf::<T>::iter()
			.take(100)
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

		log::debug!(target: LOG_TARGET, "Taking sample of {} owner infos", sample.len());
		Ok(sample.encode())
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade_step(state: Vec<u8>) -> Result<(), TryRuntimeError> {
		let sample = <Vec<(CodeHash<T>, CodeInfo<T>)> as Decode>::decode(&mut &state[..]).unwrap();

		log::debug!(target: LOG_TARGET, "Validating sample of {} code infos", sample.len());
		for (code_hash, old) in sample {
			let info = CodeInfoOf::<T>::get(&code_hash).unwrap();

			ensure!(info.determinism == old.determinism, "invalid determinism");
			ensure!(info.owner == old.owner, "invalid owner");
			ensure!(info.deposit == old.deposit, "invalid deposit");
			ensure!(info.refcount == old.refcount, "invalid refcount");
		}

		Ok(())
	}
}
