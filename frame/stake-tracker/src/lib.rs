// This file is part of Substrate.

// Copyright (C) 2023 Parity Technologies (UK) Ltd.
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

//! # Stake Tracker Pallet
//!
//! The Stake Tracker pallet is used to maintain sorted lists of [`frame_system::Config::AccountId`]
//! by listening to the events that Staking emits.
//!
//! - [`Config`]
//! - [`Pallet`]
//!
//! ## Overview
//!
//! The goal of Stake Tracker is to maintain [`SortedListProvider`] sorted list implementations
//! based on [`SortedListProvider::Score`]. This pallet implements [`OnStakingUpdate`] interface in
//! order to be able to listen to the events that Staking emits and propagate the changes to said
//! lists accordingly. It also exposes [`TrackedList`] that adds defensive checks to a subset of
//! [`SortedListProvider`] methods in order to spot unexpected list updates on the consumer side.
//! This wrapper should be used to pass the tracked entity to the consumer.
//!
//! ## Terminology
//!
//! - Approval Stake: a sum total of self-stake and all of the backing nominator stakes.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
pub(crate) mod mock;
#[cfg(test)]
mod tests;

use frame_election_provider_support::{ScoreProvider, SortedListProvider, VoteWeight};
use frame_support::{
	defensive,
	traits::{Currency, CurrencyToVote, Defensive},
};
pub use pallet::*;
use sp_runtime::Saturating;
use sp_staking::{OnStakingUpdate, Stake, StakingInterface};

use sp_std::{boxed::Box, vec::Vec};

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
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// The same currency type that's used by Staking.
		type Currency: Currency<Self::AccountId, Balance = BalanceOf<Self>>;

		/// An interface to Staking.
		type Staking: StakingInterface<AccountId = Self::AccountId>;

		/// A sorted list of nominators and validators, by their stake and self-stake respectively.
		type VoterList: SortedListProvider<Self::AccountId, Score = VoteWeight>;

		/// A sorted list of validators, by their approval stake.
		type TargetList: SortedListProvider<Self::AccountId, Score = BalanceOf<Self>>;
	}

	/// The map from validator stash key to their approval stake. Note that this map is kept up to
	/// date even if a validator chilled or turned into nominator. Entries from this map are only
	/// ever removed if the stash is reaped.
	///
	/// NOTE: This is currently a [`CountedStorageMap`] for debugging purposes. We might actually
	/// want to revisit this once this pallet starts populating the actual [`Config::TargetList`]
	/// used by [`Config::Staking`].
	#[pallet::storage]
	pub type ApprovalStake<T: Config> =
		CountedStorageMap<_, Twox64Concat, T::AccountId, BalanceOf<T>, OptionQuery>;

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		#[cfg(feature = "try-runtime")]
		fn try_state(_n: BlockNumberFor<T>) -> Result<(), &'static str> {
			ensure!(
				ApprovalStake::<T>::count() >= T::TargetList::count(),
				"ApprovalStake map missing entries"
			);
			T::TargetList::try_state()?;
			T::VoterList::try_state()
		}
	}
}

impl<T: Config> Pallet<T> {
	pub(crate) fn active_stake_of(who: &T::AccountId) -> BalanceOf<T> {
		T::Staking::stake(&who).map(|s| s.active).unwrap_or_default()
	}

	pub(crate) fn to_vote(balance: BalanceOf<T>) -> VoteWeight {
		let total_issuance = T::Currency::total_issuance();
		<T::Staking as StakingInterface>::CurrencyToVote::to_vote(balance, total_issuance)
	}

	pub(crate) fn approval_stake(who: &T::AccountId) -> Option<BalanceOf<T>> {
		ApprovalStake::<T>::get(who)
	}
}

impl<T: Config> OnStakingUpdate<T::AccountId, BalanceOf<T>> for Pallet<T> {
	fn on_stake_update(who: &T::AccountId, prev_stake: Option<Stake<T::AccountId, BalanceOf<T>>>) {
		if let Ok(current_stake) = T::Staking::stake(who) {
			let current_active = current_stake.active;
			let prev_active = prev_stake.map(|s| s.active).unwrap_or_default();

			let update_approval_stake = |who: &T::AccountId| {
				let mut approval_stake = Self::approval_stake(who).unwrap_or_default();

				use sp_std::cmp::Ordering;
				match current_active.cmp(&prev_active) {
					Ordering::Greater => {
						approval_stake =
							approval_stake.saturating_add(current_active - prev_active);
					},
					Ordering::Less => {
						approval_stake =
							approval_stake.saturating_sub(prev_active - current_active);
					},
					Ordering::Equal => return,
				};

				if T::TargetList::contains(who) {
					let _ = T::TargetList::on_update(who, approval_stake)
						.defensive_proof("Unable to update a TargetList entry.");
				}

				ApprovalStake::<T>::set(who, Some(approval_stake));
			};

			// If this is a nominator, update their position in the `VoterList`.
			if let Some(targets) = T::Staking::nominations(&current_stake.stash) {
				// update the target list.
				for target in targets {
					update_approval_stake(&target);
				}

				let _ =
					T::VoterList::on_update(&current_stake.stash, Self::to_vote(current_active))
						.defensive_proof("Nominator's position in VoterList updated; qed");
			}

			// If this is a validator, update their position in the `VoterList`.
			if T::Staking::is_validator(&current_stake.stash) {
				if !T::TargetList::contains(&current_stake.stash) {
					defensive!("Validator exists in TargetList; qed.");
				}

				update_approval_stake(&current_stake.stash);
				let _ =
					T::VoterList::on_update(&current_stake.stash, Self::to_vote(current_active))
						.defensive_proof("Validator's position in VoterList updated; qed");
			}
		} else {
			defensive!("on_stake_update is called on a bonded account; qed");
		}
	}
	fn on_nominator_add(who: &T::AccountId) {
		let score = Self::active_stake_of(who);
		if let Some(nominations) = T::Staking::nominations(who) {
			for nomination in nominations {
				// Create a new entry if it does not exist
				let new_stake =
					Self::approval_stake(&nomination).unwrap_or_default().saturating_add(score);

				ApprovalStake::<T>::set(&nomination, Some(new_stake));

				if T::TargetList::contains(&nomination) {
					let _ = T::TargetList::on_update(&nomination, new_stake)
						.defensive_proof("Unable to update a TargetList entry.");
				}
			}
			let _ = T::VoterList::on_insert(who.clone(), Self::to_vote(score))
				.defensive_proof("Nominator inserted into VoterList; qed");
		} else {
			defensive!("on_nominator_add is called for a nominator; qed");
		}
	}

	fn on_nominator_update(who: &T::AccountId, prev_nominations: Vec<T::AccountId>) {
		if let Some(nominations) = T::Staking::nominations(who) {
			if !T::VoterList::contains(who) {
				defensive!("Active nominator is in the VoterList; qed");
			}
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
					.saturating_add(Self::active_stake_of(who));

				update_approval_stake(&nomination, new_stake);
			}

			for nomination in obsolete {
				if let Some(new_stake) = Self::approval_stake(&nomination) {
					let new_stake = new_stake.saturating_sub(Self::active_stake_of(who));
					update_approval_stake(&nomination, new_stake);
				}
			}
		}
	}

	fn on_validator_add(who: &T::AccountId) {
		let self_stake = Self::active_stake_of(who);
		let new_stake = Self::approval_stake(who).unwrap_or_default().saturating_add(self_stake);
		let _ = T::TargetList::on_insert(who.clone(), new_stake)
			.defensive_proof("Validator inserted into TargetList; qed");
		let _ = T::VoterList::on_insert(who.clone(), Self::to_vote(self_stake))
			.defensive_proof("Validator inserted into VoterList; qed");
		ApprovalStake::<T>::set(who, Some(new_stake));
	}

	fn on_validator_update(who: &T::AccountId) {
		if !T::VoterList::contains(who) {
			defensive!("Active validator is in the VoterList; qed");
		}
		if !T::TargetList::contains(who) {
			defensive!("Active validator is in the TargetList; qed");
		}
	}

	fn on_validator_remove(who: &T::AccountId) {
		if T::Staking::is_validator(who) {
			let _ = T::TargetList::on_remove(who)
				.defensive_proof("Validator removed from TargetList; qed");
			let _ = T::VoterList::on_remove(who)
				.defensive_proof("Validator removed from VoterList; qed");

			let self_stake = Self::active_stake_of(who);
			let new_stake =
				Self::approval_stake(who).unwrap_or_default().saturating_sub(self_stake);
			ApprovalStake::<T>::set(who, Some(new_stake));
		} else {
			defensive!("on_validator_remove is called for a validator; qed");
		}
	}

	fn on_nominator_remove(who: &T::AccountId, nominations: Vec<T::AccountId>) {
		let _ =
			T::VoterList::on_remove(who).defensive_proof("Nominator removed from VoterList; qed");
		let score = Self::active_stake_of(who);

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
		if T::VoterList::contains(who) {
			defensive!("The staker has already been removed from VoterList; qed");
		}
		if T::TargetList::contains(who) {
			defensive!("The validator has already been removed from TargetList; qed");
		}
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
		ApprovalStake::<T>::set(who, Some(score));
	}
}

/// A wrapper for a given `SortedListProvider` that introduces defensive checks  for insert, update
/// and remove operations, suggesting that it's read-only, except for unsafe operations.
pub struct TrackedList<AccountId, Inner>(sp_std::marker::PhantomData<(AccountId, Inner)>);

impl<AccountId, Inner: SortedListProvider<AccountId>> SortedListProvider<AccountId>
	for TrackedList<AccountId, Inner>
{
	type Error = Inner::Error;
	type Score = Inner::Score;
	fn iter() -> Box<dyn Iterator<Item = AccountId>> {
		Inner::iter()
	}

	fn iter_from(start: &AccountId) -> Result<Box<dyn Iterator<Item = AccountId>>, Self::Error> {
		Inner::iter_from(start)
	}

	fn count() -> u32 {
		Inner::count()
	}

	fn contains(id: &AccountId) -> bool {
		Inner::contains(id)
	}

	fn get_score(id: &AccountId) -> Result<Self::Score, Self::Error> {
		Inner::get_score(id)
	}

	#[cfg(feature = "try-runtime")]
	fn try_state() -> Result<(), &'static str> {
		Inner::try_state()
	}

	fn on_insert(id: AccountId, score: Self::Score) -> Result<(), Self::Error> {
		defensive!("TrackedList on_insert should never be called");
		Inner::on_insert(id, score)
	}

	fn on_update(id: &AccountId, score: Self::Score) -> Result<(), Self::Error> {
		defensive!("TrackedList on_update should never be called");
		Inner::on_update(id, score)
	}

	fn on_increase(id: &AccountId, additional: Self::Score) -> Result<(), Self::Error> {
		defensive!("TrackedList on_increase should never be called");
		Inner::on_increase(id, additional)
	}

	fn on_decrease(id: &AccountId, decreased: Self::Score) -> Result<(), Self::Error> {
		defensive!("TrackedList on_decrease should never be called");
		Inner::on_decrease(id, decreased)
	}

	fn on_remove(id: &AccountId) -> Result<(), Self::Error> {
		defensive!("TrackedList on_remove should never be called");
		Inner::on_remove(id)
	}

	fn unsafe_regenerate(
		all: impl IntoIterator<Item = AccountId>,
		score_of: Box<dyn Fn(&AccountId) -> Self::Score>,
	) -> u32 {
		Inner::unsafe_regenerate(all, score_of)
	}

	frame_election_provider_support::runtime_benchmarks_or_test_enabled! {
		fn unsafe_clear() {
			Inner::unsafe_clear()
		}

		fn score_update_worst_case(who: &AccountId, is_increase: bool) -> Self::Score {
			Inner::score_update_worst_case(who, is_increase)
		}
	}
}
