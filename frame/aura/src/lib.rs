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

//! # Aura Module
//!
//! - [`Config`]
//! - [`Pallet`]
//!
//! ## Overview
//!
//! The Aura module extends Aura consensus by managing offline reporting.
//!
//! ## Interface
//!
//! ### Public Functions
//!
//! - `slot_duration` - Determine the Aura slot-duration based on the Timestamp module
//!   configuration.
//!
//! ## Related Modules
//!
//! - [Timestamp](../pallet_timestamp/index.html): The Timestamp module is used in Aura to track
//! consensus rounds (via `slots`).

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	log,
	traits::{DisabledValidators, FindAuthor, Get, OnTimestampSet, OneSessionHandler},
	BoundedSlice, BoundedVec, ConsensusEngineId, Parameter,
};
use sp_consensus_aura::{AuthorityIndex, ConsensusLog, Slot, AURA_ENGINE_ID};
use sp_runtime::{
	generic::DigestItem,
	traits::{IsMember, Member, SaturatedConversion, Saturating, Zero},
	RuntimeAppPublic,
};
use sp_std::prelude::*;

pub mod migrations;
mod mock;
mod tests;

pub use pallet::*;

const LOG_TARGET: &str = "runtime::aura";

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: pallet_timestamp::Config + frame_system::Config {
		/// The identifier type for an authority.
		type AuthorityId: Member
			+ Parameter
			+ RuntimeAppPublic
			+ MaybeSerializeDeserialize
			+ MaxEncodedLen;
		/// The maximum number of authorities that the pallet can hold.
		type MaxAuthorities: Get<u32>;

		/// A way to check whether a given validator is disabled and should not be authoring blocks.
		/// Blocks authored by a disabled validator will lead to a panic as part of this module's
		/// initialization.
		type DisabledValidators: DisabledValidators;
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

				if let Some(n_authorities) = <Authorities<T>>::decode_len() {
					let authority_index = *new_slot % n_authorities as u64;
					if T::DisabledValidators::is_disabled(authority_index as u32) {
						panic!(
							"Validator with index {:?} is disabled and should not be attempting to author blocks.",
							authority_index,
						);
					}
				}

				// TODO [#3398] Generate offence report for all authorities that skipped their
				// slots.

				T::DbWeight::get().reads_writes(2, 1)
			} else {
				T::DbWeight::get().reads(1)
			}
		}
	}

	/// The current authority set.
	#[pallet::storage]
	#[pallet::getter(fn authorities)]
	pub(super) type Authorities<T: Config> =
		StorageValue<_, BoundedVec<T::AuthorityId, T::MaxAuthorities>, ValueQuery>;

	/// The current slot of this block.
	///
	/// This will be set in `on_initialize`.
	#[pallet::storage]
	#[pallet::getter(fn current_slot)]
	pub(super) type CurrentSlot<T: Config> = StorageValue<_, Slot, ValueQuery>;

	#[pallet::genesis_config]
	#[derive(frame_support::DefaultNoBound)]
	pub struct GenesisConfig<T: Config> {
		pub authorities: Vec<T::AuthorityId>,
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			Pallet::<T>::initialize_authorities(&self.authorities);
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Change authorities.
	///
	/// The storage will be applied immediately.
	/// And aura consensus log will be appended to block's log.
	///
	/// This is a no-op if `new` is empty.
	pub fn change_authorities(new: BoundedVec<T::AuthorityId, T::MaxAuthorities>) {
		if new.is_empty() {
			log::warn!(target: LOG_TARGET, "Ignoring empty authority change.");

			return
		}

		<Authorities<T>>::put(&new);

		let log = DigestItem::Consensus(
			AURA_ENGINE_ID,
			ConsensusLog::AuthoritiesChange(new.into_inner()).encode(),
		);
		<frame_system::Pallet<T>>::deposit_log(log);
	}

	/// Initial authorities.
	///
	/// The storage will be applied immediately.
	///
	/// The authorities length must be equal or less than T::MaxAuthorities.
	pub fn initialize_authorities(authorities: &[T::AuthorityId]) {
		if !authorities.is_empty() {
			assert!(<Authorities<T>>::get().is_empty(), "Authorities are already initialized!");
			let bounded = <BoundedSlice<'_, _, T::MaxAuthorities>>::try_from(authorities)
				.expect("Initial authority set must be less than T::MaxAuthorities");
			<Authorities<T>>::put(bounded);
		}
	}

	/// Get the current slot from the pre-runtime digests.
	fn current_slot_from_digests() -> Option<Slot> {
		let digest = frame_system::Pallet::<T>::digest();
		let pre_runtime_digests = digest.logs.iter().filter_map(|d| d.as_pre_runtime());
		for (id, mut data) in pre_runtime_digests {
			if id == AURA_ENGINE_ID {
				return Slot::decode(&mut data).ok()
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
	where
		I: Iterator<Item = (&'a T::AccountId, T::AuthorityId)>,
	{
		let authorities = validators.map(|(_, k)| k).collect::<Vec<_>>();
		Self::initialize_authorities(&authorities);
	}

	fn on_new_session<'a, I: 'a>(changed: bool, validators: I, _queued_validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, T::AuthorityId)>,
	{
		// instant changes
		if changed {
			let next_authorities = validators.map(|(_, k)| k).collect::<Vec<_>>();
			let last_authorities = Self::authorities();
			if last_authorities != next_authorities {
				if next_authorities.len() as u32 > T::MaxAuthorities::get() {
					log::warn!(
						target: LOG_TARGET,
						"next authorities list larger than {}, truncating",
						T::MaxAuthorities::get(),
					);
				}
				let bounded = <BoundedVec<_, T::MaxAuthorities>>::truncate_from(next_authorities);
				Self::change_authorities(bounded);
			}
		}
	}

	fn on_disabled(i: u32) {
		let log = DigestItem::Consensus(
			AURA_ENGINE_ID,
			ConsensusLog::<T::AuthorityId>::OnDisabled(i as AuthorityIndex).encode(),
		);

		<frame_system::Pallet<T>>::deposit_log(log);
	}
}

impl<T: Config> FindAuthor<u32> for Pallet<T> {
	fn find_author<'a, I>(digests: I) -> Option<u32>
	where
		I: 'a + IntoIterator<Item = (ConsensusEngineId, &'a [u8])>,
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
	where
		I: 'a + IntoIterator<Item = (ConsensusEngineId, &'a [u8])>,
	{
		let i = Inner::find_author(digests)?;

		let validators = <Pallet<T>>::authorities();
		validators.get(i as usize).cloned()
	}
}

/// Find the authority ID of the Aura authority who authored the current block.
pub type AuraAuthorId<T> = FindAccountFromAuthorIndex<T, Pallet<T>>;

impl<T: Config> IsMember<T::AuthorityId> for Pallet<T> {
	fn is_member(authority_id: &T::AuthorityId) -> bool {
		Self::authorities().iter().any(|id| id == authority_id)
	}
}

impl<T: Config> OnTimestampSet<T::Moment> for Pallet<T> {
	fn on_timestamp_set(moment: T::Moment) {
		let slot_duration = Self::slot_duration();
		assert!(!slot_duration.is_zero(), "Aura slot duration cannot be zero.");

		let timestamp_slot = moment / slot_duration;
		let timestamp_slot = Slot::from(timestamp_slot.saturated_into::<u64>());

		assert!(
			CurrentSlot::<T>::get() == timestamp_slot,
			"Timestamp slot must match `CurrentSlot`"
		);
	}
}
