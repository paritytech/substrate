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

use frame_election_provider_support::{
	ReadOnlySortedListProvider, ScoreProvider, SortedListProvider, VoteWeight,
};
use frame_support::{
	sp_runtime::Saturating,
	traits::{Currency, CurrencyToVote},
};
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
	use frame_system::pallet_prelude::BlockNumberFor;

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

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		#[cfg(feature = "try-runtime")]
		fn try_state(n: BlockNumberFor<T>) -> Result<(), &'static str> {
			ensure!(
				ApprovalStake::<T>::count() >= T::TargetList::count(),
				"ApprovalStake map missing entries"
			);
			T::TargetList::try_state();
			T::VoterList::try_state();
		}
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
	fn on_stake_update(who: &T::AccountId, prev_stake: Option<Stake<T::AccountId, BalanceOf<T>>>) {
		// This should never fail.
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
			let _ = T::TargetList::on_update(who, approval_stake);
			ApprovalStake::<T>::set(who, Some(approval_stake));
		};

		// if this is a nominator
		if let Some(targets) = T::Staking::nominations(&current_stake.stash) {
			// update the target list.
			for target in targets {
				update_approval_stake(&target);
			}

			let _ = T::VoterList::on_update(&current_stake.stash, Self::to_vote(current_active));
		}

		if T::Staking::is_validator(&current_stake.stash) {
			update_approval_stake(&current_stake.stash);
			let _ = T::VoterList::on_update(&current_stake.stash, Self::to_vote(current_active));
		}
	}

	fn on_nominator_update(who: &T::AccountId, prev_nominations: Vec<T::AccountId>) {
		if let Some(nominations) = T::Staking::nominations(who) {
			let new = nominations.iter().filter(|n| !prev_nominations.contains(&n));
			let obsolete = prev_nominations.iter().filter(|n| !nominations.contains(&n));

			let update_approval_stake = |nomination: &T::AccountId, new_stake: BalanceOf<T>| {
				ApprovalStake::<T>::set(&nomination, Some(new_stake));

				if T::TargetList::contains(&nomination) {
					let _ = T::TargetList::on_update(&nomination, new_stake);
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
				if let Some(new_stake) = Self::approval_stake(&nomination) {
					let new_stake = new_stake.saturating_sub(Self::slashable_balance_of(who));
					update_approval_stake(&nomination, new_stake);
				}
			}

			// NOTE: We ignore the result here, because this method can be called when the nominator
			// is already in the list, just changing their nominations.
			let _ = T::VoterList::on_insert(
				who.clone(),
				Self::to_vote(Self::slashable_balance_of(who)),
			);
		}
	}

	// NOTE: This should only be called if that stash isn't already a validator. Because we don't
	// remove ApprovalStake when a validator chills and we need to make sure their self-stake is
	// up-to-date and not applied twice.
	fn on_validator_add(who: &T::AccountId) {
		let self_stake = Self::slashable_balance_of(who);
		let new_stake = Self::approval_stake(who).unwrap_or_default().saturating_add(self_stake);

		// maybe update sorted list.
		let _ = T::VoterList::on_insert(who.clone(), Self::to_vote(self_stake));

		// TODO: Make sure this always works. Among other things we need to make sure that when the
		// migration is run we only have active validators in TargetList and not the chilled ones.
		let _ = T::TargetList::on_insert(who.clone(), new_stake);
		ApprovalStake::<T>::set(who, Some(new_stake));
	}

	fn on_validator_remove(who: &T::AccountId) {
		let _ = T::TargetList::on_remove(who);
		let _ = T::VoterList::on_remove(who);

		let _ = ApprovalStake::<T>::mutate(who, |x: &mut Option<BalanceOf<T>>| {
			*x = x.map(|b| b.saturating_sub(Self::slashable_balance_of(who)))
		});
	}

	fn on_nominator_remove(who: &T::AccountId, nominations: Vec<T::AccountId>) {
		let score = Self::slashable_balance_of(who);
		let _ = T::VoterList::on_remove(who);
		for validator in nominations {
			let _ = ApprovalStake::<T>::mutate(&validator, |x: &mut Option<BalanceOf<T>>| {
				*x = x.map(|b| b.saturating_sub(score))
			});
			let _ = T::TargetList::on_update(
				&validator,
				Self::approval_stake(&validator).unwrap_or_default(),
			);
		}
	}

	fn on_unstake(who: &T::AccountId) {
		ApprovalStake::<T>::remove(who);
	}
}

impl<T: Config> ScoreProvider<T::AccountId> for Pallet<T> {
	type Score = BalanceOf<T>;

	fn score(who: &T::AccountId) -> Self::Score {
		Self::approval_stake(who).unwrap_or_default()
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn set_score_of(who: &T::AccountId, score: Self::Score) {
		ApprovalStake::<T>::set(who, score);
	}
}
