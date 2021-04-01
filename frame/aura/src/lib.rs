// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! # Aura Module
//!
//! - [`aura::Config`](./trait.Config.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Overview
//!
//! The Aura module extends Aura consensus by managing offline reporting.
//!
//! ## Interface
//!
//! ### Public Functions
//!
//! - `slot_duration` - Determine the Aura slot-duration based on the Timestamp module configuration.
//!
//! ## Related Modules
//!
//! - [Timestamp](../pallet_timestamp/index.html): The Timestamp module is used in Aura to track
//! consensus rounds (via `slots`).

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use codec::{Encode, Decode};
use frame_support::{
	Parameter, traits::{Get, FindAuthor, OneSessionHandler, OnTimestampSet}, ConsensusEngineId,
};
use sp_runtime::{
	RuntimeAppPublic,
	traits::{SaturatedConversion, Saturating, Zero, Member, IsMember}, generic::DigestItem,
};
use sp_consensus_aura::{AURA_ENGINE_ID, ConsensusLog, AuthorityIndex, Slot};

mod mock;
mod tests;
pub mod migrations;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: pallet_timestamp::Config + frame_system::Config {
		/// The identifier type for an authority.
		type AuthorityId: Member + Parameter + RuntimeAppPublic + Default + MaybeSerializeDeserialize;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(sp_std::marker::PhantomData<T>);

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(_: T::BlockNumber) -> Weight {
			if let Some(new_slot) = Self::current_slot_from_digests() {
				let current_slot = CurrentSlot::<T>::get();

				assert!(current_slot < new_slot, "Slot must increase");
				CurrentSlot::<T>::put(new_slot);

				// TODO [#3398] Generate offence report for all authorities that skipped their slots.

				T::DbWeight::get().reads_writes(2, 1)
			} else {
				T::DbWeight::get().reads(1)
			}
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {}

	/// The current authority set.
	#[pallet::storage]
	#[pallet::getter(fn authorities)]
	pub(super) type Authorities<T: Config> = StorageValue<_, Vec<T::AuthorityId>, ValueQuery>;

	/// The current slot of this block.
	///
	/// This will be set in `on_initialize`.
	#[pallet::storage]
	#[pallet::getter(fn current_slot)]
	pub(super) type CurrentSlot<T: Config> = StorageValue<_, Slot, ValueQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub authorities: Vec<T::AuthorityId>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			Self { authorities: Vec::new() }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			Pallet::<T>::initialize_authorities(&self.authorities);
		}
	}
}

impl<T: Config> Pallet<T> {
	fn change_authorities(new: Vec<T::AuthorityId>) {
		<Authorities<T>>::put(&new);

		let log: DigestItem<T::Hash> = DigestItem::Consensus(
			AURA_ENGINE_ID,
			ConsensusLog::AuthoritiesChange(new).encode()
		);
		<frame_system::Module<T>>::deposit_log(log.into());
	}

	fn initialize_authorities(authorities: &[T::AuthorityId]) {
		if !authorities.is_empty() {
			assert!(<Authorities<T>>::get().is_empty(), "Authorities are already initialized!");
			<Authorities<T>>::put(authorities);
		}
	}

	/// Get the current slot from the pre-runtime digests.
	fn current_slot_from_digests() -> Option<Slot> {
		let digest = frame_system::Pallet::<T>::digest();
		let pre_runtime_digests = digest.logs.iter().filter_map(|d| d.as_pre_runtime());
		for (id, mut data) in pre_runtime_digests {
			if id == AURA_ENGINE_ID {
				return Slot::decode(&mut data).ok();
			}
		}

		None
	}

	/// Determine the Aura slot-duration based on the Timestamp module configuration.
	pub fn slot_duration() -> T::Moment {
		// we double the minimum block-period so each author can always propose within
		// the majority of its slot.
		<T as pallet_timestamp::Config>::MinimumPeriod::get().saturating_mul(2u32.into())
	}
}

impl<T: Config> sp_runtime::BoundToRuntimeAppPublic for Pallet<T> {
	type Public = T::AuthorityId;
}

impl<T: Config> OneSessionHandler<T::AccountId> for Pallet<T> {
	type Key = T::AuthorityId;

	fn on_genesis_session<'a, I: 'a>(validators: I)
		where I: Iterator<Item=(&'a T::AccountId, T::AuthorityId)>
	{
		let authorities = validators.map(|(_, k)| k).collect::<Vec<_>>();
		Self::initialize_authorities(&authorities);
	}

	fn on_new_session<'a, I: 'a>(changed: bool, validators: I, _queued_validators: I)
		where I: Iterator<Item=(&'a T::AccountId, T::AuthorityId)>
	{
		// instant changes
		if changed {
			let next_authorities = validators.map(|(_, k)| k).collect::<Vec<_>>();
			let last_authorities = Self::authorities();
			if next_authorities != last_authorities {
				Self::change_authorities(next_authorities);
			}
		}
	}

	fn on_disabled(i: usize) {
		let log: DigestItem<T::Hash> = DigestItem::Consensus(
			AURA_ENGINE_ID,
			ConsensusLog::<T::AuthorityId>::OnDisabled(i as AuthorityIndex).encode(),
		);

		<frame_system::Module<T>>::deposit_log(log.into());
	}
}

impl<T: Config> FindAuthor<u32> for Pallet<T> {
	fn find_author<'a, I>(digests: I) -> Option<u32> where
		I: 'a + IntoIterator<Item=(ConsensusEngineId, &'a [u8])>
	{
		for (id, mut data) in digests.into_iter() {
			if id == AURA_ENGINE_ID {
				let slot = Slot::decode(&mut data).ok()?;
				let author_index = *slot % Self::authorities().len() as u64;
				return Some(author_index as u32)
			}
		}

		None
	}
}

/// We can not implement `FindAuthor` twice, because the compiler does not know if
/// `u32 == T::AuthorityId` and thus, prevents us to implement the trait twice.
#[doc(hidden)]
pub struct FindAccountFromAuthorIndex<T, Inner>(sp_std::marker::PhantomData<(T, Inner)>);

impl<T: Config, Inner: FindAuthor<u32>> FindAuthor<T::AuthorityId>
	for FindAccountFromAuthorIndex<T, Inner>
{
	fn find_author<'a, I>(digests: I) -> Option<T::AuthorityId>
		where I: 'a + IntoIterator<Item=(ConsensusEngineId, &'a [u8])>
	{
		let i = Inner::find_author(digests)?;

		let validators = <Pallet<T>>::authorities();
		validators.get(i as usize).map(|k| k.clone())
	}
}

/// Find the authority ID of the Aura authority who authored the current block.
pub type AuraAuthorId<T> = FindAccountFromAuthorIndex<T, Pallet<T>>;

impl<T: Config> IsMember<T::AuthorityId> for Pallet<T> {
	fn is_member(authority_id: &T::AuthorityId) -> bool {
		Self::authorities()
			.iter()
			.any(|id| id == authority_id)
	}
}

impl<T: Config> OnTimestampSet<T::Moment> for Pallet<T> {
	fn on_timestamp_set(moment: T::Moment) {
		let slot_duration = Self::slot_duration();
		assert!(!slot_duration.is_zero(), "Aura slot duration cannot be zero.");

		let timestamp_slot = moment / slot_duration;
		let timestamp_slot = Slot::from(timestamp_slot.saturated_into::<u64>());

		assert!(CurrentSlot::<T>::get() == timestamp_slot, "Timestamp slot must match `CurrentSlot`");
	}
}
