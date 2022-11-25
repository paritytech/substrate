// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

use crate::{BalanceOf, Config, Pallet, MAXIMUM_VOTE};
use codec::{Decode, Encode};
use frame_support::{traits::ConstU32, BoundedVec, RuntimeDebug, Twox64Concat};
use sp_std::prelude::*;

#[derive(Encode, Decode, Clone, Default, RuntimeDebug, PartialEq)]
struct DeprecatedVoter<AccountId, Balance> {
	votes: Vec<AccountId>,
	stake: Balance,
	deposit: Balance,
}

#[frame_support::storage_alias]
type Voting<T: Config> = StorageMap<
	Pallet<T>,
	Twox64Concat,
	<T as frame_system::Config>::AccountId,
	crate::Voter<<T as frame_system::Config>::AccountId, BalanceOf<T>>,
>;

pub fn migrate_voting<T: Config>() {
	Voting::<T>::translate::<DeprecatedVoter<T::AccountId, BalanceOf<T>>, _>(|_, voter| {
		let bounded_votes: BoundedVec<T::AccountId, ConstU32<{ MAXIMUM_VOTE as u32 }>> =
			voter.votes.try_into().unwrap();
		Some(crate::Voter { votes: bounded_votes, stake: voter.stake, deposit: voter.deposit })
	});
}
