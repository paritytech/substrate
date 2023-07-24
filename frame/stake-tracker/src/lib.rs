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

//! # StakeTracker
//!
//! FRAME stake tracker pallet
//!
//! ## Overview
//!
//! The stake-tracker pallet is listens to staking events through implemeting the
//! [`OnStakingUpdate`] trait and forwards those events to one or multiple types (e.g. pallets). It
//! works as a multiplexer of staking events and it is used to update semi-sorted target and voter
//! lists implemented with bags lists.
#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

use frame_election_provider_support::SortedListProvider;
use frame_support::traits::{Currency, Defensive};
use sp_runtime::Saturating;
use sp_staking::{
	currency_to_vote::CurrencyToVote, OnStakingUpdate, StakerStatus, StakingInterface,
};
use sp_std::collections::btree_map::BTreeMap;

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

/// The balance type of this pallet.
pub type BalanceOf<T> = <<T as Config>::Staking as StakingInterface>::Balance;

#[frame_support::pallet]
pub mod pallet {
	use crate::*;
	use frame_election_provider_support::VoteWeight;
	use frame_support::pallet_prelude::*;

	/// The current storage version.
	const STORAGE_VERSION: StorageVersion = StorageVersion::new(0);

	#[pallet::pallet]
	#[pallet::storage_version(STORAGE_VERSION)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		type Currency: Currency<Self::AccountId, Balance = BalanceOf<Self>>;

		/// The staking interface.
		type Staking: StakingInterface<AccountId = Self::AccountId>;

		/// Something that provides a best-effort sorted list of voters.
		///
		/// To keep the load off the chain as much as possible, changes made to the staked amount
		/// via rewards and slashes are dropped and thus need to be manually fixed by the
		/// staker. In case of `bags-list`, this always means using `rebag` and `putInFrontOf`.
		type VoterList: SortedListProvider<Self::AccountId, Score = VoteWeight>;

		/// Something that provides a best-effort sorted list of targets.
		///
		/// Unlike `VoterList`, the values in this list are always kept up to date with reward and
		/// slash as well, and thus represent the accurate approval stake of all account being
		/// nominated by nominators.
		///
		/// Note that while at the time of nomination, all targets are checked to be real
		/// validators, they can chill at any point, and their approval stakes will still be
		/// recorded. This implies that what comes out of iterating this list MIGHT NOT BE AN ACTIVE
		/// VALIDATOR.
		type TargetList: SortedListProvider<Self::AccountId, Score = VoteWeight>;
	}

	impl<T: Config> Pallet<T> {
		/// Returns the vote weight of a staker.
		pub(crate) fn active_vote_of(who: &T::AccountId) -> VoteWeight {
			T::Staking::stake(who)
				.map(|s| Self::to_vote(s.active))
				.defensive_unwrap_or_default()
		}

		/// Converts a staker's balance to its vote weight.
		pub(crate) fn to_vote(balance: BalanceOf<T>) -> VoteWeight {
			<T::Staking as StakingInterface>::CurrencyToVote::to_vote(
				balance,
				T::Currency::total_issuance(),
			)
		}

		// Decreases the approval voting of a target by `amount`.
		pub(crate) fn decrease_target_score(stash: &T::AccountId, amount: BalanceOf<T>) {
			let _ = T::TargetList::on_decrease(
				stash,
				Self::active_vote_of(stash).saturating_sub(Self::to_vote(amount)),
			)
			.defensive_proof(
				"the validator exists in the list as per the contract with staking; qed.",
			);
		}
	}
}

impl<T: Config> OnStakingUpdate<T::AccountId, BalanceOf<T>> for Pallet<T> {
	fn on_stake_update(who: &T::AccountId, _prev_stake: Option<sp_staking::Stake<BalanceOf<T>>>) {
		// note: it's safe to assume that who's stake is up to date because the ledger is updated
		// *before* calling the staking update. This is part of the contract between the staking
		// interface and its listeners.
		if let Ok(stake) = T::Staking::stake(who) {
			let voter_weight = Self::to_vote(stake.active);

			match T::Staking::status(who).defensive_unwrap_or(StakerStatus::Idle) {
				StakerStatus::Nominator(_) => {
					let _ = T::VoterList::on_update(who, voter_weight)
						.defensive_proof("Nominator's position in voter list updated; qed.");
				},
				StakerStatus::Validator => {
					let _ = T::TargetList::on_update(who, voter_weight)
						.defensive_proof("Validator's position in voter list updated; qed.");
				},
				StakerStatus::Idle => {},
			}
		}
	}

	fn on_nominator_add(who: &T::AccountId) {
		let _ = T::VoterList::on_insert(who.clone(), Self::active_vote_of(who)).defensive_proof(
			"the nominator is not part of the VoterList, as per the contract with \
                staking; qed.",
		);
	}

	fn on_validator_add(who: &T::AccountId) {
		let _ = T::TargetList::on_insert(who.clone(), Self::active_vote_of(who)).defensive_proof(
			"the validator is not part of the TargetList, as per the contract \
                with staking; qed.",
		);
	}

	fn on_nominator_remove(who: &T::AccountId, _nominations: Vec<T::AccountId>) {
		let _ = T::VoterList::on_remove(&who).defensive_proof(
			"the nominator exists in the list as per the contract with staking; qed.",
		);
	}

	fn on_validator_remove(who: &T::AccountId) {
		let _ = T::TargetList::on_remove(&who).defensive_proof(
			"the validator exists in the list as per the contract with staking; qed.",
		);
	}

	fn on_slash(
		stash: &T::AccountId,
		slashed_active: BalanceOf<T>,
		slashed_unlocking: &BTreeMap<sp_staking::EraIndex, BalanceOf<T>>,
	) {
		let slashed_amount: BalanceOf<T> = slashed_unlocking
			.values()
			.fold(Default::default(), |acc: BalanceOf<T>, u| acc.saturating_add(*u))
			.saturating_add(slashed_active);

		match T::Staking::status(stash).defensive_unwrap_or(StakerStatus::Idle) {
			StakerStatus::Validator => {
				// the slashed target's approval voting must be updated upon slashing.
				Self::decrease_target_score(stash, slashed_amount);
			},
			// the nominators stake is not updated automatically when slashed. However, the
			// nominators to be always up to date as well (re. slashes and rewards).
			// TODO(gpestana): consider a multi-block approach to spread the computational burden
			// of this loop in multiple blocks.
			StakerStatus::Nominator(_) => {
				let _: Vec<_> = <T::Staking as StakingInterface>::nominations(stash)
					.unwrap_or_default()
					.into_iter()
					.map(|t| Self::decrease_target_score(&t, slashed_amount))
					.collect();
			},
			StakerStatus::Idle => {},
		}
	}
}
