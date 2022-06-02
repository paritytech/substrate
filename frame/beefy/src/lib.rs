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

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Encode, MaxEncodedLen};

use frame_support::{traits::OneSessionHandler, BoundedSlice, Parameter, WeakBoundedVec};

use sp_runtime::{
	generic::DigestItem,
	traits::{IsMember, Member},
	RuntimeAppPublic,
};
use sp_std::prelude::*;

use beefy_primitives::{AuthorityIndex, ConsensusLog, ValidatorSet, BEEFY_ENGINE_ID};

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Authority identifier type
		type BeefyId: Member
			+ Parameter
			+ RuntimeAppPublic
			+ MaybeSerializeDeserialize
			+ MaxEncodedLen;

		/// The maximum number of authorities that can be added.
		type MaxAuthorities: Get<u32>;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);

	/// The current authorities set
	#[pallet::storage]
	#[pallet::getter(fn authorities)]
	pub(super) type Authorities<T: Config> =
		StorageValue<_, WeakBoundedVec<T::BeefyId, T::MaxAuthorities>, ValueQuery>;

	/// The current validator set id
	#[pallet::storage]
	#[pallet::getter(fn validator_set_id)]
	pub(super) type ValidatorSetId<T: Config> =
		StorageValue<_, beefy_primitives::ValidatorSetId, ValueQuery>;

	/// Authorities set scheduled to be used with the next session
	#[pallet::storage]
	#[pallet::getter(fn next_authorities)]
	pub(super) type NextAuthorities<T: Config> =
		StorageValue<_, WeakBoundedVec<T::BeefyId, T::MaxAuthorities>, ValueQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		pub authorities: Vec<T::BeefyId>,
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
	/// Return the current active BEEFY validator set.
	pub fn validator_set() -> Option<ValidatorSet<T::BeefyId>> {
		let validators: WeakBoundedVec<T::BeefyId, T::MaxAuthorities> = Self::authorities();
		let id: beefy_primitives::ValidatorSetId = Self::validator_set_id();
		ValidatorSet::<T::BeefyId>::new(validators, id)
	}

	fn change_authorities(
		new: WeakBoundedVec<T::BeefyId, T::MaxAuthorities>,
		queued: WeakBoundedVec<T::BeefyId, T::MaxAuthorities>,
	) {
		<Authorities<T>>::put(&new);

		let next_id = Self::validator_set_id() + 1u64;
		<ValidatorSetId<T>>::put(next_id);
		if let Some(validator_set) = ValidatorSet::<T::BeefyId>::new(new, next_id) {
			let log = DigestItem::Consensus(
				BEEFY_ENGINE_ID,
				ConsensusLog::AuthoritiesChange(validator_set).encode(),
			);
			<frame_system::Pallet<T>>::deposit_log(log);
		}

		<NextAuthorities<T>>::put(&queued);
	}

	fn initialize_authorities(authorities: &[T::BeefyId]) {
		if authorities.is_empty() {
			return
		}

		assert!(<Authorities<T>>::get().is_empty(), "Authorities are already initialized!");

		let bounded_authorities =
			BoundedSlice::<T::BeefyId, T::MaxAuthorities>::try_from(authorities)
				.expect("Authorities vec too big");

		<Authorities<T>>::put(bounded_authorities);
		<ValidatorSetId<T>>::put(0);
		// Like `pallet_session`, initialize the next validator set as well.
		<NextAuthorities<T>>::put(bounded_authorities);
	}
}

impl<T: Config> sp_runtime::BoundToRuntimeAppPublic for Pallet<T> {
	type Public = T::BeefyId;
}

impl<T: Config> OneSessionHandler<T::AccountId> for Pallet<T> {
	type Key = T::BeefyId;

	fn on_genesis_session<'a, I: 'a>(validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, T::BeefyId)>,
	{
		let authorities = validators.map(|(_, k)| k).collect::<Vec<_>>();
		Self::initialize_authorities(&authorities);
	}

	fn on_new_session<'a, I: 'a>(_changed: bool, validators: I, queued_validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, T::BeefyId)>,
	{
		let next_authorities = validators.map(|(_, k)| k).collect::<Vec<_>>();
		let bounded_next_authorities = WeakBoundedVec::<_, T::MaxAuthorities>::force_from(
			next_authorities,
			Some(
				"Warning: The session has more validators than expected. \
				A runtime configuration adjustment may be needed.",
			),
		);
		let next_queued_authorities = queued_validators.map(|(_, k)| k).collect::<Vec<_>>();
		let bounded_next_queued_authorities = WeakBoundedVec::<_, T::MaxAuthorities>::force_from(
			next_queued_authorities,
			Some(
				"Warning: The session has more queued validators than expected. \
				A runtime configuration adjustment may be needed.",
			),
		);

		// Always issue a change on each `session`, even if validator set hasn't changed.
		// We want to have at least one BEEFY mandatory block per session.
		Self::change_authorities(bounded_next_authorities, bounded_next_queued_authorities);
	}

	fn on_disabled(i: u32) {
		let log = DigestItem::Consensus(
			BEEFY_ENGINE_ID,
			ConsensusLog::<T::BeefyId>::OnDisabled(i as AuthorityIndex).encode(),
		);

		<frame_system::Pallet<T>>::deposit_log(log);
	}
}

impl<T: Config> IsMember<T::BeefyId> for Pallet<T> {
	fn is_member(authority_id: &T::BeefyId) -> bool {
		Self::authorities().iter().any(|id| id == authority_id)
	}
}
