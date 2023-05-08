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

//! Update `CodeStorage` with the new `determinism` field.

use crate::{
	address::AddressGenerator,
	exec::AccountIdOf,
	migration::{IsFinished, Migrate},
	BalanceOf, CodeHash, Config, Pallet, TrieId, Weight,
};
use codec::{Decode, Encode};
use frame_support::{
	codec,
	pallet_prelude::*,
	storage_alias,
	traits::{Currency, ExistenceRequirement},
	DefaultNoBound,
};
use sp_std::{marker::PhantomData, ops::Deref};
mod old {
	use super::*;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	#[scale_info(skip_type_params(T))]
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
	pub type ContractInfoOf<T: Config> = StorageMap<
		Pallet<T>,
		Twox64Concat,
		<T as frame_system::Config>::AccountId,
		ContractInfo<T>,
	>;
}

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebugNoBound, TypeInfo, MaxEncodedLen)]
#[scale_info(skip_type_params(T))]
pub struct DepositAccount<T: Config>(AccountIdOf<T>);

impl<T: Config> Deref for DepositAccount<T> {
	type Target = AccountIdOf<T>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
#[scale_info(skip_type_params(T))]
pub struct ContractInfo<T: Config> {
	pub trie_id: TrieId,
	deposit_account: DepositAccount<T>,
	pub code_hash: CodeHash<T>,
	storage_bytes: u32,
	storage_items: u32,
	pub storage_byte_deposit: BalanceOf<T>,
	storage_item_deposit: BalanceOf<T>,
	storage_base_deposit: BalanceOf<T>,
}

#[derive(Encode, Decode, MaxEncodedLen, DefaultNoBound)]
pub struct Migration<T: Config> {
	_phantom: PhantomData<T>,
}

impl<T: Config> Migrate for Migration<T> {
	const VERSION: u16 = 10;

	fn max_step_weight() -> Weight {
		Weight::zero() // TODO fix
	}

	fn step(&mut self) -> (IsFinished, Weight) {
		// TODO

		let (account, contract) = old::ContractInfoOf::<T>::iter().next().unwrap();

		let deposit_account: DepositAccount<T> =
			DepositAccount(T::AddressGenerator::deposit_address(&account));

		T::Currency::transfer(
			&account,
			&deposit_account,
			contract.storage_byte_deposit,
			ExistenceRequirement::KeepAlive,
		)
		.unwrap();

		(IsFinished::Yes, Self::max_step_weight())
	}
}
