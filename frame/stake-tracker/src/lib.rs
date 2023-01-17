// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
pub(crate) mod mock;
#[cfg(test)]
mod tests;

use frame_election_provider_support::{SortedListProvider, VoteWeight};
use frame_support::traits::{Currency, CurrencyToVote};
pub use pallet::*;

use sp_staking::{OnStakingUpdate, Stake, StakingInterface};

use sp_std::vec::Vec;

/// The balance type of this pallet.
pub type BalanceOf<T> = <<T as Config>::Staking as StakingInterface>::Balance;

#[frame_support::pallet]
pub mod pallet {
	use crate::*;
	use frame_election_provider_support::{SortedListProvider, VoteWeight};
	use frame_support::pallet_prelude::*;

	use sp_staking::StakingInterface;

	/// The current storage version.
	const STORAGE_VERSION: StorageVersion = StorageVersion::new(0);

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// This has to come from Staking::Currency
		type Currency: Currency<Self::AccountId, Balance = BalanceOf<Self>>;

		type Staking: StakingInterface<AccountId = Self::AccountId>;

		type VoterList: SortedListProvider<Self::AccountId, Score = VoteWeight>;
	}
}

impl<T: Config> Pallet<T> {
	/// The total balance that can be slashed from a stash account as of right now.
	pub fn slashable_balance_of(who: &T::AccountId) -> BalanceOf<T> {
		// Weight note: consider making the stake accessible through stash.
		T::Staking::stake(&who).map(|l| l.active).unwrap_or_default()
	}

	pub(crate) fn to_vote(balance: BalanceOf<T>) -> VoteWeight {
		let total_issuance = T::Currency::total_issuance();
		<T::Staking as StakingInterface>::CurrencyToVote::to_vote(balance, total_issuance)
	}
}

impl<T: Config> OnStakingUpdate<T::AccountId, BalanceOf<T>> for Pallet<T> {
	fn on_stake_update(who: &T::AccountId, _: Option<Stake<T::AccountId, BalanceOf<T>>>) {
		let current_stake = T::Staking::stake(who).unwrap();
		let current_active = current_stake.active;

		// if this is a nominator
		if let Some(_) = T::Staking::nominations(&current_stake.stash) {
			let _ = T::VoterList::on_update(&current_stake.stash, Self::to_vote(current_active));
		}

		if T::Staking::is_validator(&current_stake.stash) {
			let _ = T::VoterList::on_update(&current_stake.stash, Self::to_vote(current_active));
		}
	}

	fn on_nominator_update(who: &T::AccountId, _prev_nominations: Vec<T::AccountId>) {
		// NOTE: We ignore the result here, because this method can be called when the nominator is
		// already in the list, just changing their nominations.
		let _ =
			T::VoterList::on_insert(who.clone(), Self::to_vote(Self::slashable_balance_of(who)));
	}

	/// This should only be called if that stash isn't already a validator. Note, that if we want to
	/// properly track ApprovalStake here - we need to make sure we subtract the validator stash
	/// balance when they chill?
	///	Why? Because we don't remove ApprovalStake when a validator chills and we need to make sure
	/// their self-stake is up-to-date and not applied twice.
	fn on_validator_add(who: &T::AccountId) {
		let self_stake = Self::slashable_balance_of(who);
		// maybe update sorted list.
		let _ = T::VoterList::on_insert(who.clone(), Self::to_vote(self_stake));
	}

	fn on_validator_remove(who: &T::AccountId) {
		let _ = T::VoterList::on_remove(who);
	}

	fn on_nominator_remove(who: &T::AccountId, _nominations: Vec<T::AccountId>) {
		let _ = T::VoterList::on_remove(who);
	}

	fn on_unstake(_who: &T::AccountId) {}
}
