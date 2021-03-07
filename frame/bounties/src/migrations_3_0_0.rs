// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

//! Migrations to version [`3.0.0`], as denoted by the changelog.

use codec::{Encode, Decode, FullCodec};
use sp_std::prelude::*;
use frame_support::{
	RuntimeDebug, weights::Weight, Twox64Concat,
	storage::types::{StorageMap, StorageValue},
	traits::{GetPalletVersion, PalletVersion},
};

/// An index of a bounty. Just a `u32`.
pub type BountyIndex = u32;

#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct Bounty<AccountId, Balance, BlockNumber> {
	/// The account proposing it.
	proposer: AccountId,
	/// The (total) amount that should be paid if the bounty is rewarded.
	value: Balance,
	/// The curator fee. Included in value.
	fee: Balance,
	/// The deposit of curator.
	curator_deposit: Balance,
	/// The amount held on deposit (reserved) for making this proposal.
	bond: Balance,
	/// The status of this bounty.
	status: BountyStatus<AccountId, BlockNumber>,
	/// active Subbounty count
	active_subbounty_count: BountyIndex,
}


/// Trait to implement to give information about types used for migration
pub trait V2ToV3 {

	type Module: GetPalletVersion;

	type AccountId: 'static + FullCodec;

	type Balance: 'static + FullCodec + Copy;

	type BlockNumber: 'static + FullCodec + Copy;
}

struct __Bounties;
impl frame_support::traits::StorageInstance for __Bounties {
	fn pallet_prefix() -> &'static str { "Treasury" }
	const STORAGE_PREFIX: &'static str = "Bounties";
}
#[allow(type_alias_bounds)]
type Bounties<T: V2ToV3> = StorageMap<__Bounties, Twox64Concat, T::AccountId, T::Balance, T::BlockNumber>>;



/// Migrate to support subbounty extn
pub fn migrate_bounty_to_support_subbounty<T: V2ToV3>(old_deposit: T::Balance) {
	<Voting<T>>::translate::<(T::Balance, Vec<T::AccountId>), _>(
		|_index, (stake, votes)| {
			Some(Bounty {
				votes,
				stake,
				deposit: old_deposit,
			})
		},
	);

	log::info!(
		target: "runtime::elections-phragmen",
		"migrated {} voter accounts.",
		<Voting<T>>::iter().count(),
	);
}


#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct Bounty<AccountId, Balance, BlockNumber> {
	/// The account proposing it.
	proposer: AccountId,
	/// The (total) amount that should be paid if the bounty is rewarded.
	value: Balance,
	/// The curator fee. Included in value.
	fee: Balance,
	/// The deposit of curator.
	curator_deposit: Balance,
	/// The amount held on deposit (reserved) for making this proposal.
	bond: Balance,
	/// The status of this bounty.
	status: BountyStatus<AccountId, BlockNumber>,
	/// active Subbounty count
	active_subbounty_count: BountyIndex,
}

/// Bounties that have been made.
pub Bounties get(fn bounties):
	map hasher(twox_64_concat) BountyIndex
	=> Option<Bounty<T::AccountId, BalanceOf<T>, T::BlockNumber>>;
