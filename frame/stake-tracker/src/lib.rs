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

use crate::pallet::Pallet;
use pallet::Config;
use sp_staking::{OnStakingUpdate, Stake};

#[frame_support::pallet]
pub mod pallet {
	use frame_election_provider_support::{SortedListProvider, VoteWeight};
	use sp_staking::StakingInterface;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// We only need this to be able to pass to `Stake` as the type from StakingInterface is
		/// ambiguous.
		type Balance: PartialEq;
		type Staking: StakingInterface;

		type VoterList: SortedListProvider<Self::AccountId, Score = VoteWeight>;

		type TargetList: SortedListProvider<Self::AccountId, Score = VoteWeight>;
	}
}

impl<T: Config> OnStakingUpdate<T::AccountId, T::Balance> for Pallet<T> {
	fn on_update_ledger(who: &T::AccountId, old_ledger: Stake<T::AccountId, T::Balance>) {
		todo!()
	}

	fn on_nominator_add(who: &T::AccountId, old_nominations: Vec<T::AccountId>) {
		todo!()
	}

	fn on_validator_add(who: &T::AccountId) {
		todo!()
	}

	fn on_validator_remove(who: &T::AccountId) {
		todo!()
	}

	fn on_nominator_remove(who: &T::AccountId, nominations: Vec<T::AccountId>) {
		todo!()
	}

	fn on_reaped(who: &T::AccountId) {
		todo!()
	}
}
