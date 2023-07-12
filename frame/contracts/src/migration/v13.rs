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

use crate::{
	migration::{IsFinished, MigrationStep},
	weights::WeightInfo,
	Config, ContractInfo, ContractInfoOf, HoldReason, Weight, LOG_TARGET,
};
use frame_support::{
	pallet_prelude::*,
	traits::{
		fungible::{Mutate, MutateHold},
		tokens::{fungible::Inspect, Fortitude, Preservation},
	},
	DefaultNoBound,
};
#[cfg(feature = "try-runtime")]
use sp_runtime::TryRuntimeError;
use sp_runtime::{traits::Zero, Saturating};
use sp_std::ops::Deref;

#[derive(Encode, Decode, MaxEncodedLen, DefaultNoBound)]
pub struct Migration<T: Config> {
	last_account: Option<T::AccountId>,
}

impl<T: Config> MigrationStep for Migration<T> {
	const VERSION: u16 = 13;

	fn max_step_weight() -> Weight {
		// T::WeightInfo::v13_migration_step()
		todo!()
	}

	fn step(&mut self) -> (IsFinished, Weight) {
		let mut iter = if let Some(last_account) = self.last_account.take() {
			ContractInfoOf::<T>::iter_from(ContractInfoOf::<T>::hashed_key_for(last_account))
		} else {
			ContractInfoOf::<T>::iter()
		};

		if let Some((account, contract)) = iter.next() {
			do_step(contract, account);
			(IsFinished::No, T::WeightInfo::v10_migration_step()) // TODO
		} else {
			log::info!(target: LOG_TARGET, "Done Migrating Storage Deposits.");
			(IsFinished::Yes, T::WeightInfo::v10_migration_step()) // TODO
		}
	}

	#[cfg(feature = "try-runtime")]
	fn pre_upgrade_step() -> Result<Vec<u8>, TryRuntimeError> {
		todo!()
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade_step(state: Vec<u8>) -> Result<(), TryRuntimeError> {
		todo!()
	}
}

fn do_step<T: Config>(contract: ContractInfo<T>, account: <T as frame_system::Config>::AccountId) {
	// Get the deposit balance to transfer.
	let total_deposit_balance = T::Currency::total_balance(contract.deposit_account().deref());
	let reducible_deposit_balance = T::Currency::reducible_balance(
		&contract.deposit_account().deref(),
		Preservation::Expendable,
		Fortitude::Force,
	);

	if total_deposit_balance > reducible_deposit_balance {
		// This should never happen, as by design all balance in the deposit account should
		// be reducible.
		log::warn!(
			target: LOG_TARGET,
			"Deposit account {:?} for contract {:?} has some non-reducible balance {:?} that will remain in there.",
			contract.deposit_account(),
			account,
			total_deposit_balance.saturating_sub(reducible_deposit_balance)
		);
	}

	// Move balance reserved from the deposit account back to the contract account.
	// Let the deposit account die.
	let reducible_deposit_balance = T::Currency::transfer(
		&contract.deposit_account(),
		&account,
		reducible_deposit_balance,
		Preservation::Expendable,
	)
	.map(|_| {
		log::debug!(
			target: LOG_TARGET,
			"{:?} transferred from the deposit account {:?} to the contract {:?}.",
			reducible_deposit_balance,
			contract.deposit_account(),
			account
		);
		reducible_deposit_balance
	})
	.unwrap_or_else(|err| {
		log::error!(
			target: LOG_TARGET,
			"Failed to transfer {:?} from the deposit account {:?} to the contract {:?}, reason: {:?}.",
			reducible_deposit_balance,
			contract.deposit_account(),
			account,
			err
		);
		Zero::zero()
	});

	// Hold the reserved balance.
	if reducible_deposit_balance == Zero::zero() {
		log::warn!(
			target: LOG_TARGET,
			"No balance to hold as storage deposit on the contract {:?}.",
			account
		);
	} else {
		T::Currency::hold(
			&HoldReason::StorageDepositReserve.into(),
			&account,
			reducible_deposit_balance,
		)
		.map(|_| {
			log::debug!(
				target: LOG_TARGET,
				"Successfully held {:?} as storage deposit on the contract {:?}.",
				reducible_deposit_balance,
				account
			);
		})
		.unwrap_or_else(|err| {
			log::error!(
				target: LOG_TARGET,
				"Failed to hold {:?} as storage deposit on the contract {:?}, reason: {:?}.",
				reducible_deposit_balance,
				account,
				err
			);
		});
	}
}
