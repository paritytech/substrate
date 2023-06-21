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

//! # Migrations for Society Pallet

use super::*;
use codec::{Decode, Encode};
use frame_support::traits::{Instance, OnRuntimeUpgrade};

#[cfg(feature = "try-runtime")]
use sp_runtime::TryRuntimeError;

/// The log target.
const TARGET: &'static str = "runtime::society::migration";

/// This migration moves all the state to v2 of Society.
pub struct MigrateToV2<T: Config<I>, I: 'static, PastPayouts>(
	sp_std::marker::PhantomData<(T, I, PastPayouts)>,
);

impl<
		T: Config<I>,
		I: Instance + 'static,
		PastPayouts: Get<Vec<(<T as frame_system::Config>::AccountId, BalanceOf<T, I>)>>,
	> OnRuntimeUpgrade for MigrateToV2<T, I, PastPayouts>
{
	#[cfg(feature = "try-runtime")]
	fn pre_upgrade() -> Result<Vec<u8>, TryRuntimeError> {
		ensure!(can_migrate::<T, I>(), "pallet_society: already upgraded");

		let current = Pallet::<T, I>::current_storage_version();
		let onchain = Pallet::<T, I>::on_chain_storage_version();
		ensure!(onchain == 0 && current == 2, "pallet_society: invalid version");

		Ok((old::Candidates::<T, I>::get(), old::Members::<T, I>::get()).encode())
	}

	fn on_runtime_upgrade() -> Weight {
		let current = Pallet::<T, I>::current_storage_version();
		let onchain = Pallet::<T, I>::on_chain_storage_version();
		if current == 2 && onchain == 0 {
			from_original::<T, I>(&mut PastPayouts::get())
		} else {
			log::info!(
				"Running migration with current storage version {:?} / onchain {:?}",
				current,
				onchain
			);
			T::DbWeight::get().reads(1)
		}
	}

	#[cfg(feature = "try-runtime")]
	fn post_upgrade(data: Vec<u8>) -> Result<(), TryRuntimeError> {
		let old: (
			Vec<Bid<<T as frame_system::Config>::AccountId, BalanceOf<T, I>>>,
			Vec<<T as frame_system::Config>::AccountId>,
		) = Decode::decode(&mut &data[..]).expect("Bad data");
		let mut old_candidates =
			old.0.into_iter().map(|x| (x.who, x.kind, x.value)).collect::<Vec<_>>();
		let mut old_members = old.1;
		let mut candidates =
			Candidates::<T, I>::iter().map(|(k, v)| (k, v.kind, v.bid)).collect::<Vec<_>>();
		let mut members = Members::<T, I>::iter_keys().collect::<Vec<_>>();

		old_candidates.sort_by_key(|x| x.0.clone());
		candidates.sort_by_key(|x| x.0.clone());
		assert_eq!(candidates, old_candidates);

		members.sort();
		old_members.sort();
		assert_eq!(members, old_members);

		ensure!(
			Pallet::<T, I>::on_chain_storage_version() == 2,
			"The onchain version must be updated after the migration."
		);

		assert_internal_consistency::<T, I>();
		Ok(())
	}
}

pub(crate) mod old {
	use super::*;
	use frame_support::storage_alias;

	/// A vote by a member on a candidate application.
	#[derive(Encode, Decode, Copy, Clone, PartialEq, Eq, RuntimeDebug, TypeInfo)]
	pub enum Vote {
		/// The member has been chosen to be skeptic and has not yet taken any action.
		Skeptic,
		/// The member has rejected the candidate's application.
		Reject,
		/// The member approves of the candidate's application.
		Approve,
	}

	#[storage_alias]
	pub type Bids<T: Config<I>, I: 'static> = StorageValue<
		Pallet<T, I>,
		Vec<Bid<<T as frame_system::Config>::AccountId, BalanceOf<T, I>>>,
		ValueQuery,
	>;
	#[storage_alias]
	pub type Candidates<T: Config<I>, I: 'static> = StorageValue<
		Pallet<T, I>,
		Vec<Bid<<T as frame_system::Config>::AccountId, BalanceOf<T, I>>>,
		ValueQuery,
	>;
	#[storage_alias]
	pub type Votes<T: Config<I>, I: 'static> = StorageDoubleMap<
		Pallet<T, I>,
		Twox64Concat,
		<T as frame_system::Config>::AccountId,
		Twox64Concat,
		<T as frame_system::Config>::AccountId,
		Vote,
	>;
	#[storage_alias]
	pub type SuspendedCandidates<T: Config<I>, I: 'static> = StorageMap<
		Pallet<T, I>,
		Twox64Concat,
		<T as frame_system::Config>::AccountId,
		(BalanceOf<T, I>, BidKind<<T as frame_system::Config>::AccountId, BalanceOf<T, I>>),
	>;
	#[storage_alias]
	pub type Members<T: Config<I>, I: 'static> =
		StorageValue<Pallet<T, I>, Vec<<T as frame_system::Config>::AccountId>, ValueQuery>;
	#[storage_alias]
	pub type Vouching<T: Config<I>, I: 'static> = StorageMap<
		Pallet<T, I>,
		Twox64Concat,
		<T as frame_system::Config>::AccountId,
		VouchingStatus,
	>;
	#[storage_alias]
	pub type Strikes<T: Config<I>, I: 'static> = StorageMap<
		Pallet<T, I>,
		Twox64Concat,
		<T as frame_system::Config>::AccountId,
		StrikeCount,
		ValueQuery,
	>;
	#[storage_alias]
	pub type Payouts<T: Config<I>, I: 'static> = StorageMap<
		Pallet<T, I>,
		Twox64Concat,
		<T as frame_system::Config>::AccountId,
		Vec<(<T as frame_system::Config>::BlockNumber, BalanceOf<T, I>)>,
		ValueQuery,
	>;
	#[storage_alias]
	pub type SuspendedMembers<T: Config<I>, I: 'static> = StorageMap<
		Pallet<T, I>,
		Twox64Concat,
		<T as frame_system::Config>::AccountId,
		bool,
		ValueQuery,
	>;
	#[storage_alias]
	pub type Defender<T: Config<I>, I: 'static> =
		StorageValue<Pallet<T, I>, <T as frame_system::Config>::AccountId>;
	#[storage_alias]
	pub type DefenderVotes<T: Config<I>, I: 'static> =
		StorageMap<Pallet<T, I>, Twox64Concat, <T as frame_system::Config>::AccountId, Vote>;
}

pub fn can_migrate<T: Config<I>, I: Instance + 'static>() -> bool {
	old::Members::<T, I>::exists()
}

/// Will panic if there are any inconsistencies in the pallet's state or old keys remaining.
pub fn assert_internal_consistency<T: Config<I>, I: Instance + 'static>() {
	// Check all members are valid data.
	let mut members = vec![];
	for m in Members::<T, I>::iter_keys() {
		let r = Members::<T, I>::get(&m).expect("Member data must be valid");
		members.push((m, r));
	}
	assert_eq!(MemberCount::<T, I>::get(), members.len() as u32);
	for (who, record) in members.iter() {
		assert_eq!(MemberByIndex::<T, I>::get(record.index).as_ref(), Some(who));
	}
	if let Some(founder) = Founder::<T, I>::get() {
		assert_eq!(Members::<T, I>::get(founder).expect("founder is member").index, 0);
	}
	if let Some(head) = Head::<T, I>::get() {
		assert!(Members::<T, I>::contains_key(head));
	}
	// Check all votes are valid data.
	for (k1, k2) in Votes::<T, I>::iter_keys() {
		assert!(Votes::<T, I>::get(k1, k2).is_some());
	}
	// Check all defender votes are valid data.
	for (k1, k2) in DefenderVotes::<T, I>::iter_keys() {
		assert!(DefenderVotes::<T, I>::get(k1, k2).is_some());
	}
	// Check all candidates are valid data.
	for k in Candidates::<T, I>::iter_keys() {
		assert!(Candidates::<T, I>::get(k).is_some());
	}
	// Check all suspended members are valid data.
	for m in SuspendedMembers::<T, I>::iter_keys() {
		assert!(SuspendedMembers::<T, I>::get(m).is_some());
	}
	// Check all payouts are valid data.
	for p in Payouts::<T, I>::iter_keys() {
		let k = Payouts::<T, I>::hashed_key_for(&p);
		let v = frame_support::storage::unhashed::get_raw(&k[..]).expect("value is in map");
		assert!(PayoutRecordFor::<T, I>::decode(&mut &v[..]).is_ok());
	}

	// We don't use these - make sure they don't exist.
	assert_eq!(old::SuspendedCandidates::<T, I>::iter().count(), 0);
	assert_eq!(old::Strikes::<T, I>::iter().count(), 0);
	assert_eq!(old::Vouching::<T, I>::iter().count(), 0);
	assert!(!old::Defender::<T, I>::exists());
	assert!(!old::Members::<T, I>::exists());
}

pub fn from_original<T: Config<I>, I: Instance + 'static>(
	past_payouts: &mut [(<T as frame_system::Config>::AccountId, BalanceOf<T, I>)],
) -> Weight {
	// First check that this is the original state layout. This is easy since the original layout
	// contained the Members value, and this value no longer exists in the new layout.
	if !old::Members::<T, I>::exists() {
		log::warn!(target: TARGET, "Skipping MigrateToV2 migration since it appears unapplicable");
		// Already migrated or no data to migrate: Bail.
		return T::DbWeight::get().reads(1)
	}

	// Migrate Bids from old::Bids (just a trunctation).
	Bids::<T, I>::put(BoundedVec::<_, T::MaxBids>::truncate_from(old::Bids::<T, I>::take()));

	// Initialise round counter.
	RoundCount::<T, I>::put(0);

	// Migrate Candidates from old::Candidates
	for Bid { who: candidate, kind, value } in old::Candidates::<T, I>::take().into_iter() {
		let mut tally = Tally::default();
		// Migrate Votes from old::Votes
		// No need to drain, since we're overwriting values.
		for (voter, vote) in old::Votes::<T, I>::iter_prefix(&candidate) {
			Votes::<T, I>::insert(
				&candidate,
				&voter,
				Vote { approve: vote == old::Vote::Approve, weight: 1 },
			);
			match vote {
				old::Vote::Approve => tally.approvals.saturating_inc(),
				old::Vote::Reject => tally.rejections.saturating_inc(),
				old::Vote::Skeptic => Skeptic::<T, I>::put(&voter),
			}
		}
		Candidates::<T, I>::insert(
			&candidate,
			Candidacy { round: 0, kind, tally, skeptic_struck: false, bid: value },
		);
	}

	// Migrate Members from old::Members old::Strikes old::Vouching
	let mut member_count = 0;
	for member in old::Members::<T, I>::take() {
		let strikes = old::Strikes::<T, I>::take(&member);
		let vouching = old::Vouching::<T, I>::take(&member);
		let record = MemberRecord { index: member_count, rank: 0, strikes, vouching };
		Members::<T, I>::insert(&member, record);
		MemberByIndex::<T, I>::insert(member_count, &member);
		member_count.saturating_inc();
	}
	MemberCount::<T, I>::put(member_count);

	// Migrate Payouts from: old::Payouts and raw info (needed since we can't query old chain
	// state).
	past_payouts.sort();
	for (who, mut payouts) in old::Payouts::<T, I>::iter() {
		payouts.truncate(T::MaxPayouts::get() as usize);
		// ^^ Safe since we already truncated.
		let paid = past_payouts
			.binary_search_by_key(&&who, |x| &x.0)
			.ok()
			.map(|p| past_payouts[p].1)
			.unwrap_or(Zero::zero());
		match BoundedVec::try_from(payouts) {
			Ok(payouts) => Payouts::<T, I>::insert(who, PayoutRecord { paid, payouts }),
			Err(_) => debug_assert!(false, "Truncation of Payouts ineffective??"),
		}
	}

	// Migrate SuspendedMembers from old::SuspendedMembers old::Strikes old::Vouching.
	for who in old::SuspendedMembers::<T, I>::iter_keys() {
		let strikes = old::Strikes::<T, I>::take(&who);
		let vouching = old::Vouching::<T, I>::take(&who);
		let record = MemberRecord { index: 0, rank: 0, strikes, vouching };
		SuspendedMembers::<T, I>::insert(&who, record);
	}

	// Any suspended candidates remaining are rejected.
	let _ = old::SuspendedCandidates::<T, I>::clear(u32::MAX, None);

	// We give the current defender the benefit of the doubt.
	old::Defender::<T, I>::kill();
	let _ = old::DefenderVotes::<T, I>::clear(u32::MAX, None);

	T::BlockWeights::get().max_block
}

pub fn from_raw_past_payouts<T: Config<I>, I: Instance + 'static>(
	past_payouts_raw: impl Iterator<Item = ([u8; 32], u128)>,
) -> Vec<(<T as frame_system::Config>::AccountId, BalanceOf<T, I>)> {
	past_payouts_raw
		.filter_map(|(x, y)| Some((Decode::decode(&mut &x[..]).ok()?, y.try_into().ok()?)))
		.collect()
}
