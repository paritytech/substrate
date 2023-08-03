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
//! The stake-tracker pallet listens to staking events through implementing the
//! [`OnStakingUpdate`] trait and forwards those events to one or multiple types (e.g. pallets) that
//! must be kept up to date with certain updates in staking. The pallet does not expose any
//! callables and acts as a multiplexer of staking events.
//!
//! Currently, the stake tracker pallet is used to update the semi-sorted target and voter lists
//! implemented through the bags lists pallet.
//!
//! ## Goals
//!
//! The [`OnStakingUpdate`] implementation aims at achieving the following goals:
//!
//! * The [`Config::TargetList`] keeps a semi-sorted list of validators, sorted by approvals
//! (including self-vote and nominations).
//! * The [`Config::VoterList`] keeps a semi-sorted list of voters, sorted by bonded stake.
//! * The [`Config::TargetList`] sorting must be *always* kept up to date, even in the event of new
//! nomination updates, nominator/validator slashes and rewards.
//! * The [`Config::VoterList`] does not need to necessarily be kept up to date at all times (e.g.
//! slashes). Those updates may be done externally if possible (e.g. if the voter sorted list
//! provider is implemented using a bags-list pallet, the updates can be accomplished through
//! callables).
//!
//! ## Event emitter ordering and staking ledger state updates
//!
//! It is important to ensure that the events are emitted from staking (i.e. the calls into
//! [`OnStakingUpdate`]) *after* the caller ensures that the state of the staking ledger is up to
//! date, since the new state will be fetched and used to update the sorted lists accordingly.

#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

use frame_election_provider_support::SortedListProvider;
use frame_support::traits::{Currency, Defensive};
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
/// The account ID of this pallet.
pub type AccountIdOf<T> = <T as frame_system::Config>::AccountId;

/// Represents a stake imbalance to be applied to a staker's score.
#[derive(Copy, Clone, Debug)]
pub enum StakeImbalance<Balance> {
	// Represents the reduction of stake by `Balance`.
	Negative(Balance),
	// Represents the increase of stake by `Balance`.
	Positive(Balance),
}

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
		/// Returns the vote weight of a staker based on its current stake.
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

		/// Updates a staker's score by increasing/decreasing an imbalance of the current score in
		/// the list.
		pub(crate) fn update_score<L>(who: &T::AccountId, imbalance: StakeImbalance<VoteWeight>)
		where
			L: SortedListProvider<AccountIdOf<T>, Score = VoteWeight>,
		{
			match imbalance {
				StakeImbalance::Positive(imbalance) => {
					let _ = L::on_increase(who, imbalance).defensive_proof(
						"the staker exists in the list as per the contract with staking; qed.",
					);
				},
				StakeImbalance::Negative(imbalance) => {
					let _ = L::on_decrease(who, imbalance).defensive_proof(
						"the staker exists in the list as per the contract with staking; qed.",
					);
				},
			}
		}
	}
}

impl<T: Config> OnStakingUpdate<T::AccountId, BalanceOf<T>> for Pallet<T> {
	// Fired when the stake amount of someone updates.
	//
	// When a nominator's stake is updated, all the nominated targets must be updated accordingly.
	//
	// Note: it is assumed that who's staking state is updated *before* the caller calling into
	// this method.
	fn on_stake_update(who: &T::AccountId, prev_stake: Option<sp_staking::Stake<BalanceOf<T>>>) {
		if let Ok(stake) = T::Staking::stake(who) {
			let voter_weight = Self::to_vote(stake.active);

			match T::Staking::status(who).defensive_unwrap_or(StakerStatus::Idle) {
				StakerStatus::Nominator(_) => {
					let _ = T::VoterList::on_update(who, voter_weight)
						.defensive_proof("Nominator's position in voter list updated; qed."); // TODO(gpestana): check this defensive out

					// calculate imbalace to update the score of nominated targets.
					let stake_imbalance = if let Some(prev_stake) = prev_stake {
						let prev_voter_weight = Self::to_vote(prev_stake.active);
						if prev_voter_weight > voter_weight {
							StakeImbalance::Negative(prev_voter_weight - voter_weight)
						} else {
							StakeImbalance::Positive(voter_weight - prev_voter_weight)
						}
					} else {
						// if nominator had no stake before update, then add all the voter weight
						// to the target's score.
						StakeImbalance::Positive(voter_weight)
					};

					// updates vote weight of nominated targets accordingly.
					for target in <T::Staking as StakingInterface>::nominations(who)
						.unwrap_or_default()
						.into_iter()
					{
						// target may be chilling due to a recent slash, verify if it is active
						// before updating the score.
						if <T::Staking as StakingInterface>::is_validator(&target) {
							Self::update_score::<T::TargetList>(&target, stake_imbalance);
						}
					}
				},
				StakerStatus::Validator => {
					let _ = T::TargetList::on_update(who, voter_weight)
						.defensive_proof("Validator's position in voter list updated; qed.");
				},
				StakerStatus::Idle => (), // nothing to see here.
			}
		}
	}

	// Fired when someone sets their intention to nominate.
	//
	// Note: it is assumed that who's staking state is updated *before* the caller calling into
	// this method.
	fn on_nominator_add(who: &T::AccountId) {
		let nominator_vote = Self::active_vote_of(who);

		let _ = T::VoterList::on_insert(who.clone(), nominator_vote).defensive_proof(
			"the nominator is not part of the VoterList, as per the contract with \
                staking; qed.",
		);

		// on_nominator_add could be called on a validator. If who is a nominator, update the vote
		// weight of the nominations if they exist.
		match T::Staking::status(who) {
			Ok(StakerStatus::Nominator(nominations)) =>
				for t in nominations {
					Self::update_score::<T::TargetList>(
						&t,
						StakeImbalance::Positive(nominator_vote),
					)
				},
			Ok(StakerStatus::Idle) | Ok(StakerStatus::Validator) | Err(_) => (), // nada.
		};
	}

	// Fired when someone sets their intention to validate.
	//
	// A validator is also considered a voter with self-vote and should be added to
	// [`Config::VoterList`].
	//
	// Note: it is assumed that who's staking state is updated *before* the caller calling into
	// this method.
	fn on_validator_add(who: &T::AccountId) {
		let _ = T::TargetList::on_insert(who.clone(), Self::active_vote_of(who)).defensive_proof(
			"the validator is not part of the TargetList, as per the contract \
                with staking; qed.",
		);

		// a validator is also a nominator.
		Self::on_nominator_add(who)
	}

	// Fired when someone removes their intention to nominate, either due to chill or validating.
	//
	// Note: it is assumed that who's staking state is updated *before* the caller calling into
	// this method. Thus, the nominations before the nominator has been removed from staking are
	// passed in, so that the target list can be updated accordingly.
	fn on_nominator_remove(who: &T::AccountId, nominations: Vec<T::AccountId>) {
		let nominator_vote = Self::active_vote_of(who);

		// updates the nominated target's score.
		for t in nominations.iter() {
			Self::update_score::<T::TargetList>(&t, StakeImbalance::Negative(nominator_vote))
		}

		let _ = T::VoterList::on_remove(&who).defensive_proof(
			"the nominator exists in the list as per the contract with staking; qed.",
		);
	}

	// Fired when someone removes their intention to validate, either due to chill or nominating.
	fn on_validator_remove(who: &T::AccountId) {
		let _ = T::TargetList::on_remove(&who).defensive_proof(
			"the validator exists in the list as per the contract with staking; qed.",
		);

		// validator is also a nominator.
		Self::on_nominator_remove(who, vec![]);
	}

	// Fired when an existing nominator updates their nominations.
	//
	// This is called when a nominator updates their nominations. The nominator's stake remains the
	// same (updates to the nominator's stake should emit [`Self::on_stake_update`] instead).
	// However, the score of the nominated targets must be updated accordingly.
	//
	// Note: it is assumed that who's staking state is updated *before* the caller calling into
	// this method.
	fn on_nominator_update(who: &T::AccountId, prev_nominations: Vec<T::AccountId>) {
		let nominator_vote = Self::active_vote_of(who);
		let curr_nominations =
			<T::Staking as StakingInterface>::nominations(&who).unwrap_or_default();

		// new nominations
		for target in curr_nominations.iter() {
			if !prev_nominations.contains(target) {
				Self::update_score::<T::TargetList>(
					&target,
					StakeImbalance::Positive(nominator_vote),
				);
			}
		}
		// removed nominations
		for target in prev_nominations.iter() {
			if !curr_nominations.contains(target) {
				Self::update_score::<T::TargetList>(
					&target,
					StakeImbalance::Negative(nominator_vote),
				);
			}
		}
	}

	// noop: the updates to target and voter lists when applying a slash are performed
	// through [`Self::on_nominator_remove`] and [`Self::on_validator_remove`] when the stakers are
	// chilled.
	fn on_slash(
		_stash: &T::AccountId,
		_slashed_active: BalanceOf<T>,
		_slashed_unlocking: &BTreeMap<sp_staking::EraIndex, BalanceOf<T>>,
	) {
	}
}
