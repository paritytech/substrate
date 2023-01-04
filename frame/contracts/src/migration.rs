// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

use crate::{BalanceOf, CodeHash, Config, Pallet, TrieId, Weight};
use codec::{Decode, Encode, FullCodec};
use frame_support::{
	codec,
	pallet_prelude::*,
	storage::{generator::StorageMap, migration, unhashed},
	storage_alias,
	traits::{Get, OnRuntimeUpgrade},
	Identity, Twox64Concat, WeakBoundedVec,
};
use sp_runtime::traits::Saturating;
use sp_std::{marker::PhantomData, prelude::*};

const LOG_TARGET: &str = "pallet-contracts::storage-migration";

/// Performs all necessary migrations based on `StorageVersion`.
pub struct Migration<T: Config>(PhantomData<T>);
impl<T: Config> OnRuntimeUpgrade for Migration<T> {
	fn on_runtime_upgrade() -> Weight {
		let version = <Pallet<T>>::on_chain_storage_version();
		let mut weight = Weight::zero();

		if version < 4 {
			v4::migrate::<T>(&mut weight);
		}

		if version < 5 {
			v5::migrate::<T>(&mut weight);
		}

		if version < 6 {
			v6::migrate::<T>(&mut weight);
		}

		if version < 7 {
			v7::migrate::<T>(&mut weight);
		}

		if version < 8 {
			v8::migrate::<T>(&mut weight);
		}

		if version < 9 {
			v9::migrate::<T>(&mut weight);
		}

		StorageVersion::new(9).put::<Pallet<T>>();
		weight.saturating_accrue(T::DbWeight::get().writes(1));

		weight
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, &'static str> {
		let version = <Pallet<T>>::on_chain_storage_version();

		if version == 7 {
			v8::pre_upgrade::<T>()?;
		}

		Ok(version.encode())
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade(state: Vec<u8>) -> Result<(), &'static str> {
		let version = Decode::decode(&mut state.as_ref()).map_err(|_| "Cannot decode version")?;
		post_checks::post_upgrade::<T>(version)
	}
}

impl<T: Config> Migration<T> {
	pub(crate) fn migration_step(weight_limit: Option<Weight>, version: u32) -> Weight {
		let max_allowed_call_weight = <MigrationHelper<T>>::max_call_weight();
		let weight_limit =
			weight_limit.unwrap_or(max_allowed_call_weight).min(max_allowed_call_weight);

		match version {
			9 => v9::migration_step::<T>(weight_limit),
			_ => Weight::zero(),
		}
	}
}

// Helper for common migration operations
pub struct MigrationHelper<T: Config>(PhantomData<T>);
impl<T: Config> MigrationHelper<T> {
	/// Max allowed weight that migration should be allowed to consume
	pub(crate) fn max_call_weight() -> Weight {
		// 50% of block should be fine
		T::BlockWeights::get().max_block / 2
	}

	/// Used to translate a single value in the DB
	/// Returns conservative weight estimate of the operation, even in case translation fails.
	///
	/// TODO: add such functions to StorageMap, DoubleStorageMap & StorageNMap
	fn translate<O: FullCodec + MaxEncodedLen, V: FullCodec, F: FnMut(O) -> Option<V>>(
		key: &[u8],
		mut f: F,
	) -> Weight {
		let value = match unhashed::get::<O>(key) {
			Some(value) => value,
			None =>
				return Weight::from_parts(
					T::DbWeight::get().reads(1).ref_time(),
					O::max_encoded_len() as u64,
				),
		};

		let mut proof_size = value.using_encoded(|o| o.len() as u64);

		match f(value) {
			Some(new) => {
				proof_size.saturating_accrue(new.using_encoded(|n| n.len() as u64));
				unhashed::put::<V>(key, &new);
			},
			None => unhashed::kill(key),
		}

		Weight::from_parts(T::DbWeight::get().reads_writes(1, 1).ref_time(), proof_size)
	}
}

/// V4: `Schedule` is changed to be a config item rather than an in-storage value.
mod v4 {
	use super::*;

	pub fn migrate<T: Config>(weight: &mut Weight) {
		#[allow(deprecated)]
		migration::remove_storage_prefix(<Pallet<T>>::name().as_bytes(), b"CurrentSchedule", b"");
		weight.saturating_accrue(T::DbWeight::get().writes(1));
	}
}

/// V5: State rent is removed which obsoletes some fields in `ContractInfo`.
mod v5 {
	use super::*;

	type AliveContractInfo<T> =
		RawAliveContractInfo<CodeHash<T>, BalanceOf<T>, <T as frame_system::Config>::BlockNumber>;
	type TombstoneContractInfo<T> = RawTombstoneContractInfo<
		<T as frame_system::Config>::Hash,
		<T as frame_system::Config>::Hashing,
	>;

	#[derive(Decode)]
	enum OldContractInfo<T: Config> {
		Alive(AliveContractInfo<T>),
		Tombstone(TombstoneContractInfo<T>),
	}

	#[derive(Decode)]
	struct RawAliveContractInfo<CodeHash, Balance, BlockNumber> {
		trie_id: TrieId,
		_storage_size: u32,
		_pair_count: u32,
		code_hash: CodeHash,
		_rent_allowance: Balance,
		_rent_paid: Balance,
		_deduct_block: BlockNumber,
		_last_write: Option<BlockNumber>,
		_reserved: Option<()>,
	}

	#[derive(Decode)]
	struct RawTombstoneContractInfo<H, Hasher>(H, PhantomData<Hasher>);

	#[derive(Decode)]
	struct OldDeletedContract {
		_pair_count: u32,
		trie_id: TrieId,
	}

	pub type ContractInfo<T> = RawContractInfo<CodeHash<T>>;

	#[derive(Encode, Decode)]
	pub struct RawContractInfo<CodeHash> {
		pub trie_id: TrieId,
		pub code_hash: CodeHash,
		pub _reserved: Option<()>,
	}

	#[derive(Encode, Decode)]
	struct DeletedContract {
		trie_id: TrieId,
	}

	#[storage_alias]
	type ContractInfoOf<T: Config> = StorageMap<
		Pallet<T>,
		Twox64Concat,
		<T as frame_system::Config>::AccountId,
		ContractInfo<T>,
	>;

	#[storage_alias]
	type DeletionQueue<T: Config> = StorageValue<Pallet<T>, Vec<DeletedContract>>;

	pub fn migrate<T: Config>(weight: &mut Weight) {
		<ContractInfoOf<T>>::translate(|_key, old: OldContractInfo<T>| {
			weight.saturating_accrue(T::DbWeight::get().reads_writes(1, 1));
			match old {
				OldContractInfo::Alive(old) => Some(ContractInfo::<T> {
					trie_id: old.trie_id,
					code_hash: old.code_hash,
					_reserved: old._reserved,
				}),
				OldContractInfo::Tombstone(_) => None,
			}
		});

		DeletionQueue::<T>::translate(|old: Option<Vec<OldDeletedContract>>| {
			weight.saturating_accrue(T::DbWeight::get().reads_writes(1, 1));
			old.map(|old| old.into_iter().map(|o| DeletedContract { trie_id: o.trie_id }).collect())
		})
		.ok();
	}
}

/// V6: Added storage deposits
mod v6 {
	use super::*;

	type RelaxedCodeVec<T> = WeakBoundedVec<u8, <T as Config>::MaxCodeLen>;

	#[derive(Encode, Decode)]
	struct OldPrefabWasmModule {
		#[codec(compact)]
		instruction_weights_version: u32,
		#[codec(compact)]
		initial: u32,
		#[codec(compact)]
		maximum: u32,
		#[codec(compact)]
		refcount: u64,
		_reserved: Option<()>,
		code: Vec<u8>,
		original_code_len: u32,
	}

	#[derive(Encode, Decode, MaxEncodedLen)]
	pub struct PrefabWasmModule<T: Config> {
		#[codec(compact)]
		pub instruction_weights_version: u32,
		#[codec(compact)]
		pub initial: u32,
		#[codec(compact)]
		pub maximum: u32,
		pub code: RelaxedCodeVec<T>,
	}

	use v5::ContractInfo as OldContractInfo;

	#[derive(Encode, Decode)]
	pub struct RawContractInfo<CodeHash, Balance> {
		pub trie_id: TrieId,
		pub code_hash: CodeHash,
		pub storage_deposit: Balance,
	}

	#[derive(Encode, Decode)]
	pub struct OwnerInfo<T: Config> {
		owner: T::AccountId,
		#[codec(compact)]
		deposit: BalanceOf<T>,
		#[codec(compact)]
		refcount: u64,
	}

	pub type ContractInfo<T> = RawContractInfo<CodeHash<T>, BalanceOf<T>>;

	#[storage_alias]
	type ContractInfoOf<T: Config> = StorageMap<
		Pallet<T>,
		Twox64Concat,
		<T as frame_system::Config>::AccountId,
		ContractInfo<T>,
	>;

	#[storage_alias]
	type CodeStorage<T: Config> = StorageMap<Pallet<T>, Identity, CodeHash<T>, PrefabWasmModule<T>>;

	#[storage_alias]
	type OwnerInfoOf<T: Config> = StorageMap<Pallet<T>, Identity, CodeHash<T>, OwnerInfo<T>>;

	pub fn migrate<T: Config>(weight: &mut Weight) {
		<ContractInfoOf<T>>::translate(|_key, old: OldContractInfo<T>| {
			weight.saturating_accrue(T::DbWeight::get().reads_writes(1, 1));
			Some(ContractInfo::<T> {
				trie_id: old.trie_id,
				code_hash: old.code_hash,
				storage_deposit: Default::default(),
			})
		});

		let nobody = T::AccountId::decode(&mut sp_runtime::traits::TrailingZeroInput::zeroes())
			.expect("Infinite input; no dead input space; qed");

		<CodeStorage<T>>::translate(|key, old: OldPrefabWasmModule| {
			weight.saturating_accrue(T::DbWeight::get().reads_writes(1, 2));
			<OwnerInfoOf<T>>::insert(
				key,
				OwnerInfo {
					refcount: old.refcount,
					owner: nobody.clone(),
					deposit: Default::default(),
				},
			);
			Some(PrefabWasmModule {
				instruction_weights_version: old.instruction_weights_version,
				initial: old.initial,
				maximum: old.maximum,
				code: WeakBoundedVec::force_from(old.code, None),
			})
		});
	}
}

/// Rename `AccountCounter` to `Nonce`.
mod v7 {
	use super::*;

	pub fn migrate<T: Config>(weight: &mut Weight) {
		#[storage_alias]
		type AccountCounter<T: Config> = StorageValue<Pallet<T>, u64, ValueQuery>;
		#[storage_alias]
		type Nonce<T: Config> = StorageValue<Pallet<T>, u64, ValueQuery>;

		Nonce::<T>::set(AccountCounter::<T>::take());
		weight.saturating_accrue(T::DbWeight::get().reads_writes(1, 2))
	}
}

/// Update `ContractInfo` with new fields that track storage deposits.
mod v8 {
	use super::*;
	use sp_io::default_child_storage as child;
	use v6::ContractInfo as OldContractInfo;

	#[derive(Encode, Decode)]
	pub struct ContractInfo<T: Config> {
		pub trie_id: TrieId,
		pub code_hash: CodeHash<T>,
		pub storage_bytes: u32,
		pub storage_items: u32,
		pub storage_byte_deposit: BalanceOf<T>,
		pub storage_item_deposit: BalanceOf<T>,
		pub storage_base_deposit: BalanceOf<T>,
	}

	#[storage_alias]
	type ContractInfoOf<T: Config, V> =
		StorageMap<Pallet<T>, Twox64Concat, <T as frame_system::Config>::AccountId, V>;

	pub fn migrate<T: Config>(weight: &mut Weight) {
		<ContractInfoOf<T, ContractInfo<T>>>::translate_values(|old: OldContractInfo<T>| {
			// Count storage items of this contract
			let mut storage_bytes = 0u32;
			let mut storage_items = 0u32;
			let mut key = Vec::new();
			while let Some(next) = child::next_key(&old.trie_id, &key) {
				key = next;
				let mut val_out = [];
				let len = child::read(&old.trie_id, &key, &mut val_out, 0)
					.expect("The loop conditions checks for existence of the key; qed");
				storage_bytes.saturating_accrue(len);
				storage_items.saturating_accrue(1);
			}

			let storage_byte_deposit =
				T::DepositPerByte::get().saturating_mul(storage_bytes.into());
			let storage_item_deposit =
				T::DepositPerItem::get().saturating_mul(storage_items.into());
			let storage_base_deposit = old
				.storage_deposit
				.saturating_sub(storage_byte_deposit)
				.saturating_sub(storage_item_deposit);

			// Reads: One read for each storage item plus the contract info itself.
			// Writes: Only the new contract info.
			weight.saturating_accrue(
				T::DbWeight::get().reads_writes(u64::from(storage_items) + 1, 1),
			);

			Some(ContractInfo {
				trie_id: old.trie_id,
				code_hash: old.code_hash,
				storage_bytes,
				storage_items,
				storage_byte_deposit,
				storage_item_deposit,
				storage_base_deposit,
			})
		});
	}

	#[cfg(feature = "try-runtime")]
	pub fn pre_upgrade<T: Config>() -> Result<(), &'static str> {
		use frame_support::traits::ReservableCurrency;
		for (key, value) in ContractInfoOf::<T, OldContractInfo<T>>::iter() {
			let reserved = T::Currency::reserved_balance(&key);
			ensure!(reserved >= value.storage_deposit, "Reserved balance out of sync.");
		}
		Ok(())
	}
}

/// Update `CodeStorage` with the new `determinism` field.
mod v9 {
	use super::*;
	use crate::Determinism;
	use v6::PrefabWasmModule as OldPrefabWasmModule;

	type RelaxedCodeVec<T> = WeakBoundedVec<u8, <T as Config>::MaxCodeLen>;

	#[derive(Encode, Decode)]
	pub struct PrefabWasmModule<T: Config> {
		#[codec(compact)]
		pub instruction_weights_version: u32,
		#[codec(compact)]
		pub initial: u32,
		#[codec(compact)]
		pub maximum: u32,
		pub code: RelaxedCodeVec<T>,
		pub determinism: Determinism,
	}

	#[storage_alias]
	type CodeStorage<T: Config> = StorageMap<Pallet<T>, Identity, CodeHash<T>, PrefabWasmModule<T>>;

	pub fn migrate<T: Config>(weight: &mut Weight) {
		<CodeStorage<T>>::translate_values(|old: OldPrefabWasmModule<T>| {
			weight.saturating_accrue(T::DbWeight::get().reads_writes(1, 1));
			Some(PrefabWasmModule::<T> {
				instruction_weights_version: old.instruction_weights_version,
				initial: old.initial,
				maximum: old.maximum,
				code: old.code,
				determinism: Determinism::Deterministic,
			})
		});
	}

	/// Used to keep track of migration state from `v8` to `v9`
	#[derive(PartialEq, Eq, Clone, Encode, Decode, TypeInfo, RuntimeDebug, MaxEncodedLen)]
	pub enum MigrationState {
		/// No migration in progress
		NotInProgress,
		/// In the middle of `CodeStorage` migration. The const for max size is an overestimate but
		/// that's fine.
		CodeStorage(Option<WeakBoundedVec<u8, ConstU32<1000>>>),
	}

	impl Default for MigrationState {
		fn default() -> Self {
			MigrationState::NotInProgress
		}
	}

	impl MigrationState {
		/// Convert `self` into value applicable for iteration
		fn for_iteration(self) -> Self {
			if self == Self::NotInProgress {
				Self::CodeStorage(None)
			} else {
				self
			}
		}
	}

	#[storage_alias]
	pub(super) type MigrationStateV9Storage<T: Config> =
		StorageValue<Pallet<T>, MigrationState, ValueQuery>;

	/// Executes storage migration from `v8` to `v9`, consuming limited amount of weight.
	///
	/// Migration will keep going until it consumes more weight than the specified limit.
	pub fn migration_step<T: Config>(weight_limit: Weight) -> Weight {
		let version = <Pallet<T>>::on_chain_storage_version();
		let mut consumed_weight = T::DbWeight::get().reads(1);

		if version != 8 {
			log::trace!(
				target: LOG_TARGET,
				"Current version is {:?} but expected is 8. Skipping migration procedures.",
				version,
			);
			// TODO: should we add function for depositing events without index?
			// <Pallet<T>>::deposit_event(crate::Event::<T>::ItemsMigrated{migrated_values: 0});
			return consumed_weight
		}

		log::trace!(target: LOG_TARGET, "v9 migration weight limit will be {:?}.", weight_limit,);

		let migration_state = <MigrationStateV9Storage<T>>::get().for_iteration();
		consumed_weight.saturating_accrue(T::DbWeight::get().reads(1));

		if let MigrationState::CodeStorage(last_processed_key) = migration_state {
			let key_iter = if let Some(previous_key) = last_processed_key {
				CodeStorage::<T>::iter_keys_from(previous_key.into_inner())
			} else {
				CodeStorage::<T>::iter_keys()
			};

			let mut counter = 0_u32;

			for key in key_iter {
				let key_as_vec = CodeStorage::<T>::storage_map_final_key(key);
				let used_weight =
					<MigrationHelper<T>>::translate(&key_as_vec, |old: OldPrefabWasmModule<T>| {
						Some(PrefabWasmModule::<T> {
							instruction_weights_version: old.instruction_weights_version,
							initial: old.initial,
							maximum: old.maximum,
							code: old.code,
							determinism: Determinism::Deterministic,
						})
					});

				// Increment total consumed weight.
				consumed_weight.saturating_accrue(used_weight);
				counter += 1;

				// Check if we've consumed enough weight already.
				if consumed_weight.any_gt(weight_limit) {
					log::trace!(
							target: LOG_TARGET,
							"v9 CodeStorage migration stopped after consuming {:?} weight and after processing {:?} DB entries.", consumed_weight, counter,
						);
					<MigrationStateV9Storage<T>>::put(MigrationState::CodeStorage(Some(
						WeakBoundedVec::force_from(key_as_vec, None),
					)));
					consumed_weight.saturating_accrue(T::DbWeight::get().writes(1));

					// Self::deposit_event(Event::<T>::ContractsMigrated(counter)); // TODO

					// we want `try-runtime` to execute the entire migration, hence the recursion
					if cfg!(feature = "try-runtime") {
						return migration_step::<T>(weight_limit).saturating_add(consumed_weight)
					} else {
						return consumed_weight
					}
				}
			}

			log::trace!(target: LOG_TARGET, "v9 CodeStorage migration finished.",);
			// Self::deposit_event(Event::<T>::ContractsMigrated(counter)); // TODO

			MigrationStateV9Storage::<T>::kill();
			StorageVersion::new(9).put::<Pallet<T>>();
			consumed_weight.saturating_accrue(T::DbWeight::get().writes(2));
		}

		consumed_weight
	}
}

// Post checks always need to be run against the latest storage version. This is why we
// do not scope them in the per version modules. They always need to be ported to the latest
// version.
#[cfg(feature = "try-runtime")]
mod post_checks {
	use super::*;
	use crate::Determinism;
	use sp_io::default_child_storage as child;
	use v8::ContractInfo;
	use v9::PrefabWasmModule;

	#[storage_alias]
	type CodeStorage<T: Config> = StorageMap<Pallet<T>, Identity, CodeHash<T>, PrefabWasmModule<T>>;

	#[storage_alias]
	type ContractInfoOf<T: Config, V> =
		StorageMap<Pallet<T>, Twox64Concat, <T as frame_system::Config>::AccountId, V>;

	pub fn post_upgrade<T: Config>(old_version: StorageVersion) -> Result<(), &'static str> {
		if old_version < 7 {
			return Ok(())
		}

		if old_version < 8 {
			v8::<T>()?;
		}

		if old_version < 9 {
			v9::<T>()?;
		}

		Ok(())
	}

	fn v8<T: Config>() -> Result<(), &'static str> {
		use frame_support::traits::ReservableCurrency;
		for (key, value) in ContractInfoOf::<T, ContractInfo<T>>::iter() {
			let reserved = T::Currency::reserved_balance(&key);
			let stored = value
				.storage_base_deposit
				.saturating_add(value.storage_byte_deposit)
				.saturating_add(value.storage_item_deposit);
			ensure!(reserved >= stored, "Reserved balance out of sync.");

			let mut storage_bytes = 0u32;
			let mut storage_items = 0u32;
			let mut key = Vec::new();
			while let Some(next) = child::next_key(&value.trie_id, &key) {
				key = next;
				let mut val_out = [];
				let len = child::read(&value.trie_id, &key, &mut val_out, 0)
					.expect("The loop conditions checks for existence of the key; qed");
				storage_bytes.saturating_accrue(len);
				storage_items.saturating_accrue(1);
			}
			ensure!(storage_bytes == value.storage_bytes, "Storage bytes do not match.",);
			ensure!(storage_items == value.storage_items, "Storage items do not match.",);
		}
		Ok(())
	}

	fn v9<T: Config>() -> Result<(), &'static str> {
		for value in CodeStorage::<T>::iter_values() {
			ensure!(
				value.determinism == Determinism::Deterministic,
				"All pre-existing codes need to be deterministic."
			);
		}

		ensure!(
			!v9::MigrationStateV9Storage::<T>::exists(),
			"MigrationStateStorage has to be killed at the end of migration."
		);

		ensure!(
			<Pallet<T>>::on_chain_storage_version() == 9,
			"pallet-contracts storage version must be 9 at the end of migration"
		);

		Ok(())
	}
}
