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
//! The Stake Tracker pallet is used to maintain a sorted list of voters by listening to the events
//! that Staking emits.
//!
//! - [`Config`]
//! - [`Pallet`]
//!
//! ## Overview
//!
//! The goal of Stake Tracker is to reduce the burden of Staking pallet by taking care of the
//! [`Config::VoterList`] maintenance. This pallet implements [`OnStakingUpdate`] interface in order
//! to be able to listen to the events that Staking emits and propagate the changes to the list
//! accordingly. It also exposes [`TrackedList`] that stubs a subset of [`SortedListProvider`]
//! methods out effectively disabling the user's ability to update the list. This wrapper should be
//! used to pass the tracked entity to the consumer.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
pub(crate) mod mock;
#[cfg(test)]
mod tests;

use frame_election_provider_support::{SortedListProvider, VoteWeight};
use frame_support::traits::{Currency, CurrencyToVote};
pub use pallet::*;
use sp_runtime::{
	traits::{Bounded, Zero},
	Saturating,
};
use sp_staking::{OnStakingUpdate, Stake, StakingInterface};

use sp_std::{boxed::Box, vec::Vec};

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

		/// A sorted list of nominators and validators, by their stake and self-stake respectively.
		type VoterList: SortedListProvider<Self::AccountId, Score = VoteWeight>;
	}
}

impl<T: Config> Pallet<T> {
	pub fn active_stake_of(who: &T::AccountId) -> BalanceOf<T> {
		T::Staking::stake(&who).map(|s| s.active).unwrap_or_default()
	}

	pub(crate) fn to_vote(balance: BalanceOf<T>) -> VoteWeight {
		let total_issuance = T::Currency::total_issuance();
		<T::Staking as StakingInterface>::CurrencyToVote::to_vote(balance, total_issuance)
	}
}

impl<T: Config> OnStakingUpdate<T::AccountId, BalanceOf<T>> for Pallet<T> {
	fn on_stake_update(who: &T::AccountId, _: Option<Stake<T::AccountId, BalanceOf<T>>>) {
		if let Ok(current_stake) = T::Staking::stake(who) {
			let current_active = current_stake.active;

			// if this is a nominator
			if let Some(_) = T::Staking::nominations(&current_stake.stash) {
				let _ =
					T::VoterList::on_update(&current_stake.stash, Self::to_vote(current_active));
			}

			if T::Staking::is_validator(&current_stake.stash) {
				let _ =
					T::VoterList::on_update(&current_stake.stash, Self::to_vote(current_active));
			}
		}
	}

	fn on_nominator_update(who: &T::AccountId, _prev_nominations: Vec<T::AccountId>) {
		// NOTE: We ignore the result here, because this method can be called when the nominator
		// is already in the list, just changing their nominations.
		let _ = T::VoterList::on_insert(who.clone(), Self::to_vote(Self::active_stake_of(who)));
	}

	fn on_validator_update(who: &T::AccountId) {
		let self_stake = Self::active_stake_of(who);
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

/// A wrapper for a given `SortedListProvider` that disables insert/update/remove operations,
/// effectively rendering it read-only, except for unsafe operations.
pub struct TrackedList<T, S, P>(sp_std::marker::PhantomData<(T, S, P)>);

impl<T: Config, S: Bounded + Saturating + Zero, P: SortedListProvider<T::AccountId, Score = S>>
	SortedListProvider<T::AccountId> for TrackedList<T, S, P>
{
	type Error = P::Error;
	type Score = P::Score;
	fn iter() -> Box<dyn Iterator<Item = T::AccountId>> {
		P::iter()
	}

	fn iter_from(
		start: &T::AccountId,
	) -> Result<Box<dyn Iterator<Item = T::AccountId>>, Self::Error> {
		P::iter_from(start)
	}

	fn count() -> u32 {
		P::count()
	}

	fn contains(id: &T::AccountId) -> bool {
		P::contains(id)
	}

	fn get_score(id: &T::AccountId) -> Result<Self::Score, Self::Error> {
		P::get_score(id)
	}

	#[cfg(feature = "try-runtime")]
	fn try_state() -> Result<(), &'static str> {
		P::try_state()
	}

	fn on_insert(_id: T::AccountId, _score: Self::Score) -> Result<(), Self::Error> {
		unreachable!()
	}

	fn on_update(_id: &T::AccountId, _score: Self::Score) -> Result<(), Self::Error> {
		unreachable!()
	}

	fn on_increase(_id: &T::AccountId, _additional: Self::Score) -> Result<(), Self::Error> {
		unreachable!()
	}

	fn on_decrease(_id: &T::AccountId, _decreased: Self::Score) -> Result<(), Self::Error> {
		unreachable!()
	}

	fn on_remove(_id: &T::AccountId) -> Result<(), Self::Error> {
		unreachable!()
	}

	fn unsafe_regenerate(
		all: impl IntoIterator<Item = T::AccountId>,
		score_of: Box<dyn Fn(&T::AccountId) -> Self::Score>,
	) -> u32 {
		P::unsafe_regenerate(all, score_of)
	}

	frame_election_provider_support::runtime_benchmarks_or_test_enabled! {
		fn unsafe_clear() {
			P::unsafe_clear()
		}

		fn score_update_worst_case(who: &T::AccountId, is_increase: bool) -> Self::Score {
			P::score_update_worst_case(who, is_increase)
		}
	}
}
