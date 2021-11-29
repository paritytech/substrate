// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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
use codec::{Decode, Encode};
use frame_support::{
	codec, generate_storage_alias,
	storage::migration,
	traits::{Get, PalletInfoAccess},
	Identity, Twox64Concat,
};
use sp_std::{marker::PhantomData, prelude::*};

pub fn migrate<T: Config>() -> Weight {
	use frame_support::traits::StorageVersion;

	let version = StorageVersion::get::<Pallet<T>>();
	let mut weight: Weight = 0;

	if version < 4 {
		weight = weight.saturating_add(v4::migrate::<T>());
		StorageVersion::new(4).put::<Pallet<T>>();
	}

	if version < 5 {
		weight = weight.saturating_add(v5::migrate::<T>());
		StorageVersion::new(5).put::<Pallet<T>>();
	}

	if version < 6 {
		weight = weight.saturating_add(v6::migrate::<T>());
		StorageVersion::new(6).put::<Pallet<T>>();
	}

	weight
}

/// V4: `Schedule` is changed to be a config item rather than an in-storage value.
mod v4 {
	use super::*;

	pub fn migrate<T: Config>() -> Weight {
		migration::remove_storage_prefix(<Pallet<T>>::name().as_bytes(), b"CurrentSchedule", b"");
		T::DbWeight::get().writes(1)
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

	generate_storage_alias!(
		Contracts,
		ContractInfoOf<T: Config> => Map<(Twox64Concat, T::AccountId), ContractInfo<T>>
	);

	generate_storage_alias!(
		Contracts,
		DeletionQueue => Value<Vec<DeletedContract>>
	);

	pub fn migrate<T: Config>() -> Weight {
		let mut weight: Weight = 0;

		<ContractInfoOf<T>>::translate(|_key, old: OldContractInfo<T>| {
			weight = weight.saturating_add(T::DbWeight::get().reads_writes(1, 1));
			match old {
				OldContractInfo::Alive(old) => Some(ContractInfo::<T> {
					trie_id: old.trie_id,
					code_hash: old.code_hash,
					_reserved: old._reserved,
				}),
				OldContractInfo::Tombstone(_) => None,
			}
		});

		DeletionQueue::translate(|old: Option<Vec<OldDeletedContract>>| {
			weight = weight.saturating_add(T::DbWeight::get().reads_writes(1, 1));
			old.map(|old| old.into_iter().map(|o| DeletedContract { trie_id: o.trie_id }).collect())
		})
		.ok();

		weight
	}
}

/// V6: Added storage deposits
mod v6 {
	use super::*;

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

	#[derive(Encode, Decode)]
	struct PrefabWasmModule {
		#[codec(compact)]
		instruction_weights_version: u32,
		#[codec(compact)]
		initial: u32,
		#[codec(compact)]
		maximum: u32,
		code: Vec<u8>,
	}

	use v5::ContractInfo as OldContractInfo;

	#[derive(Encode, Decode)]
	pub struct RawContractInfo<CodeHash, Balance> {
		trie_id: TrieId,
		code_hash: CodeHash,
		storage_deposit: Balance,
	}

	#[derive(Encode, Decode)]
	pub struct OwnerInfo<T: Config> {
		owner: T::AccountId,
		#[codec(compact)]
		deposit: BalanceOf<T>,
		#[codec(compact)]
		refcount: u64,
	}

	type ContractInfo<T> = RawContractInfo<CodeHash<T>, BalanceOf<T>>;

	generate_storage_alias!(
		Contracts,
		ContractInfoOf<T: Config> => Map<(Twox64Concat, T::AccountId), ContractInfo<T>>
	);

	generate_storage_alias!(
		Contracts,
		CodeStorage<T: Config> => Map<(Identity, CodeHash<T>), PrefabWasmModule>
	);

	generate_storage_alias!(
		Contracts,
		OwnerInfoOf<T: Config> => Map<(Identity, CodeHash<T>), OwnerInfo<T>>
	);

	pub fn migrate<T: Config>() -> Weight {
		let mut weight: Weight = 0;

		<ContractInfoOf<T>>::translate(|_key, old: OldContractInfo<T>| {
			weight = weight.saturating_add(T::DbWeight::get().reads_writes(1, 1));
			Some(ContractInfo::<T> {
				trie_id: old.trie_id,
				code_hash: old.code_hash,
				storage_deposit: Default::default(),
			})
		});

		<CodeStorage<T>>::translate(|key, old: OldPrefabWasmModule| {
			weight = weight.saturating_add(T::DbWeight::get().reads_writes(1, 2));
			<OwnerInfoOf<T>>::insert(
				key,
				OwnerInfo {
					refcount: old.refcount,
					owner: Default::default(),
					deposit: Default::default(),
				},
			);
			Some(PrefabWasmModule {
				instruction_weights_version: old.instruction_weights_version,
				initial: old.initial,
				maximum: old.maximum,
				code: old.code,
			})
		});

		weight
	}
}
