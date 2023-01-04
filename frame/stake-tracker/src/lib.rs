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

use frame_election_provider_support::{
	ReadOnlySortedListProvider, ScoreProvider, SortedListProvider, VoteWeight,
};
use frame_support::traits::{Currency, CurrencyToVote, Defensive};
pub use pallet::*;
use sp_runtime::Saturating;
use sp_staking::{OnStakingUpdate, Stake, StakingInterface};

use sp_std::vec::Vec;

/// The balance type of this pallet.
pub type BalanceOf<T> = <<T as Config>::Staking as StakingInterface>::Balance;

#[frame_support::pallet]
pub mod pallet {
	use crate::*;
	use frame_election_provider_support::{SortedListProvider, VoteWeight};
	use frame_support::{pallet_prelude::*, Twox64Concat};

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

		type TargetList: SortedListProvider<Self::AccountId, Score = BalanceOf<Self>>;
	}

	#[pallet::error]
	pub enum Error<T> {
		/// ApprovalStake entry does not exist.
		DoesNotExist,
	}

	/// The map from validator stash key to their total approval stake. Not that this map is kept up
	/// to date even if a validator chilled or turned into nominator. Entries from this map are only
	/// ever removed if the stash is reaped.
	///
	/// NOTE: This is currently a [`CountedStorageMap`] for debugging purposes. We might actually
	/// want to revisit this once this pallet starts populating the actual [`Config::TargetList`]
	/// used by [`Config::Staking`].
	#[pallet::storage]
	#[pallet::getter(fn approval_stake)]
	pub type ApprovalStake<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, BalanceOf<T>, OptionQuery>;
}

impl<T: Config> Pallet<T> {
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
	fn on_update_ledger(who: &T::AccountId, prev_stake: Option<Stake<T::AccountId, BalanceOf<T>>>) {
		let current_stake = T::Staking::stake(who).unwrap();
		let prev_active = prev_stake.map(|s| s.active).unwrap_or_default();
		let current_active = current_stake.active;

		let update_approval_stake = |who: &T::AccountId| {
			let mut approval_stake = Self::approval_stake(who).unwrap_or_default();

			use sp_std::cmp::Ordering;
			match current_active.cmp(&prev_active) {
				Ordering::Greater => {
					approval_stake = approval_stake.saturating_add(current_active - prev_active);
				},
				Ordering::Less => {
					approval_stake = approval_stake.saturating_sub(prev_active - current_active);
				},
				Ordering::Equal => return,
			};
			let _ = T::TargetList::on_update(who, approval_stake).defensive();
			ApprovalStake::<T>::set(who, Some(approval_stake));
		};

		// if this is a nominator
		if let Some(targets) = T::Staking::nominations(&current_stake.stash) {
			// update the target list.
			for target in targets {
				update_approval_stake(&target);
			}

			// update the voter list.
			let _ = T::VoterList::on_update(&current_stake.stash, Self::to_vote(current_active))
				.defensive_proof("any nominator should have an entry in the voter list.");
		}

		if T::Staking::is_validator(&current_stake.stash) {
			update_approval_stake(&current_stake.stash);

			let _ = T::VoterList::on_update(&current_stake.stash, Self::to_vote(current_active))
				.defensive_proof("any validator should have an entry in the voter list.");
		}
	}

	fn on_nominator_add(who: &T::AccountId, prev_nominations: Vec<T::AccountId>) {
		let nominations = T::Staking::nominations(who).unwrap_or_default();
		let new = nominations.iter().filter(|n| !prev_nominations.contains(&n));
		let obsolete = prev_nominations.iter().filter(|n| !nominations.contains(&n));

		let update_approval_stake = |nomination: &T::AccountId, new_stake: BalanceOf<T>| {
			ApprovalStake::<T>::set(&nomination, Some(new_stake));

			if T::TargetList::contains(&nomination) {
				let _ = T::TargetList::on_update(&nomination, new_stake).defensive();
			}
		};

		for nomination in new {
			// Create a new entry if it does not exist
			let new_stake = Self::approval_stake(&nomination)
				.unwrap_or_default()
				.saturating_add(Self::slashable_balance_of(who));

			update_approval_stake(&nomination, new_stake);
		}

		for nomination in obsolete {
			// we should actually fail if an old nomination was not in the map, which should never
			// happen.
			let new_stake = Self::approval_stake(&nomination)
				.unwrap()
				.saturating_sub(Self::slashable_balance_of(who));

			update_approval_stake(&nomination, new_stake);
		}
		let _ =
			T::VoterList::on_insert(who, Self::to_vote(Self::slashable_balance_of(who)))
				.defensive();
	}

	/// This should only be called if that stash isn't already a validator. Note, that if we want to
	/// properly track ApprovalStake here - we need to make sure we subtract the validator stash
	/// balance when they chill?
	///	Why? Because we don't remove ApprovalStake when a validator chills and we need to make sure
	/// their self-stake is up-to-date and not applied twice.
	fn on_validator_add(who: &T::AccountId) {
		let self_stake = Self::slashable_balance_of(who);
		let new_stake = Self::approval_stake(who).unwrap_or_default().saturating_add(self_stake);

		// maybe update sorted list.
		let _ = T::VoterList::on_insert(who.clone(), Self::to_vote(self_stake)).defensive();

		// TODO: Make sure this always works. Among other things we need to make sure that when the
		// migration is run we only have active validators in TargetList and not the chilled ones.
		let _ = T::TargetList::on_insert(who.clone(), new_stake).defensive();
		ApprovalStake::<T>::set(who, Some(new_stake));
	}

	fn on_validator_remove(who: &T::AccountId) {
		let _ = T::TargetList::on_remove(who).defensive();
		let _ = T::VoterList::on_remove(who).defensive();

		// This will panic if the validator is not in the map, but this should never happen!
		ApprovalStake::<T>::mutate(who, |x: &mut Option<BalanceOf<T>>| {
			x.map(|b| b.saturating_sub(Self::slashable_balance_of(who)))
		})
		.unwrap();
	}

	fn on_nominator_remove(who: &T::AccountId, nominations: Vec<T::AccountId>) {
		let score = Self::slashable_balance_of(who);
		let _ = T::VoterList::on_remove(who).defensive();
		for validator in nominations {
			ApprovalStake::<T>::mutate(&validator, |x: &mut Option<BalanceOf<T>>| {
				x.map(|b| b.saturating_sub(score))
			})
			.unwrap();
		}
	}

	fn on_reaped(who: &T::AccountId) {
		ApprovalStake::<T>::remove(who)
	}
}

impl<T: Config> ScoreProvider<T::AccountId> for Pallet<T> {
	type Score = BalanceOf<T>;

	fn score(who: &T::AccountId) -> Self::Score {
		Self::approval_stake(who).unwrap_or_default()
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn set_score_of(_: &T::AccountId, _: Self::Score) {
		todo!()
	}
}
