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

//! Move contracts' _reserved_ balance to be _held_ instead. Since
//! [`Currency`](frame_support::traits::Currency) has been deprecated [here](https://github.com/paritytech/substrate/pull/12951),
//! we need the storage deposit to be handled by the [fungible
//! traits](frame_support::traits::fungibles) instead.

mod old {
	use super::*;

	pub type BalanceOf<T, OldCurrency> = <OldCurrency as frame_support::traits::Currency<
		<T as frame_system::Config>::AccountId,
	>>::Balance;

	#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo, MaxEncodedLen)]
	#[scale_info(skip_type_params(T, OldCurrency))]
	pub struct ContractInfo<T: Config, OldCurrency>
	where
		OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId>
			+ Inspect<
				<T as frame_system::Config>::AccountId,
				Balance = old::BalanceOf<T, OldCurrency>,
			>,
	{
		pub trie_id: TrieId,
		pub deposit_account: DepositAccount<T>,
		pub code_hash: CodeHash<T>,
		pub storage_bytes: u32,
		pub storage_items: u32,
		pub storage_byte_deposit: BalanceOf<T, OldCurrency>,
		pub storage_item_deposit: BalanceOf<T, OldCurrency>,
		pub storage_base_deposit: BalanceOf<T, OldCurrency>,
	}
}
pub struct Migration<T: Config, OldCurrency>
where
	OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId>
		+ Inspect<<T as frame_system::Config>::AccountId, Balance = old::BalanceOf<T, OldCurrency>>,
{
	last_account: Option<T::AccountId>,
	_phantom: PhantomData<(T, OldCurrency)>,
}

impl<T: Config, OldCurrency: 'static> MigrationStep for Migration<T, OldCurrency>
where
	OldCurrency: ReservableCurrency<<T as frame_system::Config>::AccountId>
		+ Inspect<<T as frame_system::Config>::AccountId, Balance = old::BalanceOf<T, OldCurrency>>,
{
	const VERSION: u16 = 13;

	fn max_step_weight() -> Weight {
		T::WeightInfo::v10_migration_step()
	}

	fn step(&mut self) -> (IsFinished, Weight) {
		// Move balance reserved from the deposit account back to the contract account.
		// Let the deposit account be killed.

		// Hold the reserved balance.
	}
}
