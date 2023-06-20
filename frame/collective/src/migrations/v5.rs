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

use crate::{Config, Pallet};
use codec::{Decode, Encode};
use frame_support::{
	pallet_prelude::{OptionQuery, StorageVersion, TypeInfo, ValueQuery},
	sp_runtime::Saturating,
	traits::{Get, StorePreimage},
	weights::Weight,
	BoundedVec, Identity, RuntimeDebug,
};
use frame_system::pallet_prelude::BlockNumberFor;
use sp_std::prelude::*;

#[frame_support::storage_alias]
pub type Proposals<T: Config<I>, I: 'static> = StorageValue<
	Pallet<T, I>,
	BoundedVec<<T as frame_system::Config>::Hash, <T as Config<I>>::MaxProposals>,
	ValueQuery,
>;

#[frame_support::storage_alias]
pub type ProposalOf<T: Config<I>, I: 'static> = StorageMap<
	Pallet<T, I>,
	Identity,
	<T as frame_system::Config>::Hash,
	<T as Config<I>>::Proposal,
	OptionQuery,
>;

#[frame_support::storage_alias]
pub type Voting<T: Config<I>, I: 'static> = StorageMap<
	Pallet<T, I>,
	Identity,
	<T as frame_system::Config>::Hash,
	OldVotes<<T as frame_system::Config>::AccountId, BlockNumberFor<T>>,
	OptionQuery,
>;

#[frame_support::storage_alias]
pub type Members<T: Config<I>, I: 'static> =
	StorageValue<Pallet<T, I>, Vec<<T as frame_system::Config>::AccountId>, ValueQuery>;

/// Info for keeping track of a motion being voted on.
#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct OldVotes<AccountId, BlockNumber> {
	/// The proposal's unique index.
	pub index: crate::ProposalIndex,
	/// The number of approval votes that are needed to pass the motion.
	pub threshold: crate::MemberCount,
	/// The current set of voters that approved it.
	pub ayes: Vec<AccountId>,
	/// The current set of voters that rejected it.
	pub nays: Vec<AccountId>,
	/// The hard end time of this vote.
	pub end: BlockNumber,
}

pub fn migrate<T: Config<I>, I: 'static>() -> Weight {
	let storage_version = StorageVersion::get::<Pallet<T, I>>();
	log::info!(
		target: "runtime::collective",
		"Running migration for collective with storage version {:?}",
		storage_version,
	);

	if storage_version <= 4 {
		let mut count = 0u64;

		Proposals::<T, I>::kill();

		Voting::<T, I>::drain().for_each(|(hash, vote)| {
			count.saturating_inc();

			let proposal = ProposalOf::<T, I>::take(hash).expect("proposal should exist");
			let proposal_bounded = <T as Config<I>>::Preimages::bound(proposal)
				.expect("preimage bound failed, the call is too big");
			let vote =
				crate::Votes::<T::AccountId, BlockNumberFor<T>, <T as Config<I>>::MaxMembers> {
					index: vote.index,
					threshold: vote.threshold,
					ayes: vote
						.ayes
						.try_into()
						.expect("runtime::collective migration failed, ayes overflow"),
					nays: vote
						.nays
						.try_into()
						.expect("runtime::collective migration failed, nays overflow"),
					end: vote.end,
				};

			crate::Voting::<T, I>::insert(proposal_bounded, vote);
		});

		StorageVersion::new(5).put::<Pallet<T, I>>();

		T::DbWeight::get().reads_writes(count, count)
	} else {
		log::warn!(
			target: "runtime::collective",
			"Attempted to apply migration to V5 but failed because storage version is {:?}",
			storage_version,
		);
		Weight::zero()
	}
}
