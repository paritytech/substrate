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

use frame_support::{
	log,
	traits::{Get, OneSessionHandler},
	BoundedSlice, BoundedVec, Parameter,
};

use sp_runtime::{
	generic::DigestItem,
	traits::{IsMember, Member},
	RuntimeAppPublic,
};
use sp_std::prelude::*;

use beefy_primitives::{
	AuthorityIndex, ConsensusLog, OnNewValidatorSet, ValidatorSet, BEEFY_ENGINE_ID,
	GENESIS_AUTHORITY_SET_ID,
};

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::BlockNumberFor;

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

		/// A hook to act on the new BEEFY validator set.
		///
		/// For some applications it might be beneficial to make the BEEFY validator set available
		/// externally apart from having it in the storage. For instance you might cache a light
		/// weight MMR root over validators and make it available for Light Clients.
		type OnNewValidatorSet: OnNewValidatorSet<<Self as Config>::BeefyId>;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);

	/// The current authorities set
	#[pallet::storage]
	#[pallet::getter(fn authorities)]
	pub(super) type Authorities<T: Config> =
		StorageValue<_, BoundedVec<T::BeefyId, T::MaxAuthorities>, ValueQuery>;

	/// The current validator set id
	#[pallet::storage]
	#[pallet::getter(fn validator_set_id)]
	pub(super) type ValidatorSetId<T: Config> =
		StorageValue<_, beefy_primitives::ValidatorSetId, ValueQuery>;

	/// Authorities set scheduled to be used with the next session
	#[pallet::storage]
	#[pallet::getter(fn next_authorities)]
	pub(super) type NextAuthorities<T: Config> =
		StorageValue<_, BoundedVec<T::BeefyId, T::MaxAuthorities>, ValueQuery>;

	/// Block number where BEEFY consensus is enabled/started.
	/// If changing this, make sure `Self::ValidatorSetId` is also reset to
	/// `GENESIS_AUTHORITY_SET_ID` in the state of the new block number configured here.
	#[pallet::storage]
	#[pallet::getter(fn genesis_block)]
	pub(super) type GenesisBlock<T: Config> =
		StorageValue<_, Option<BlockNumberFor<T>>, ValueQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		/// Initial set of BEEFY authorities.
		pub authorities: Vec<T::BeefyId>,
		/// Block number where BEEFY consensus should start.
		/// Should match the session where initial authorities are active.
		/// *Note:* Ideally use block number where GRANDPA authorities are changed,
		/// to guarantee the client gets a finality notification for exactly this block.
		pub genesis_block: Option<BlockNumberFor<T>>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			// BEEFY genesis will be first BEEFY-MANDATORY block,
			// use block number one instead of chain-genesis.
			let genesis_block = Some(sp_runtime::traits::One::one());
			Self { authorities: Vec::new(), genesis_block }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			Pallet::<T>::initialize_authorities(&self.authorities)
				// we panic here as runtime maintainers can simply reconfigure genesis and restart
				// the chain easily
				.expect("Authorities vec too big");
			<GenesisBlock<T>>::put(&self.genesis_block);
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Return the current active BEEFY validator set.
	pub fn validator_set() -> Option<ValidatorSet<T::BeefyId>> {
		let validators: BoundedVec<T::BeefyId, T::MaxAuthorities> = Self::authorities();
		let id: beefy_primitives::ValidatorSetId = Self::validator_set_id();
		ValidatorSet::<T::BeefyId>::new(validators, id)
	}

	fn change_authorities(
		new: BoundedVec<T::BeefyId, T::MaxAuthorities>,
		queued: BoundedVec<T::BeefyId, T::MaxAuthorities>,
	) {
		<Authorities<T>>::put(&new);

		let new_id = Self::validator_set_id() + 1u64;
		<ValidatorSetId<T>>::put(new_id);

		<NextAuthorities<T>>::put(&queued);

		if let Some(validator_set) = ValidatorSet::<T::BeefyId>::new(new, new_id) {
			let log = DigestItem::Consensus(
				BEEFY_ENGINE_ID,
				ConsensusLog::AuthoritiesChange(validator_set.clone()).encode(),
			);
			<frame_system::Pallet<T>>::deposit_log(log);

			let next_id = new_id + 1;
			if let Some(next_validator_set) = ValidatorSet::<T::BeefyId>::new(queued, next_id) {
				<T::OnNewValidatorSet as OnNewValidatorSet<_>>::on_new_validator_set(
					&validator_set,
					&next_validator_set,
				);
			}
		}
	}

	fn initialize_authorities(authorities: &Vec<T::BeefyId>) -> Result<(), ()> {
		if authorities.is_empty() {
			return Ok(())
		}

		if !<Authorities<T>>::get().is_empty() {
			return Err(())
		}

		let bounded_authorities =
			BoundedSlice::<T::BeefyId, T::MaxAuthorities>::try_from(authorities.as_slice())
				.map_err(|_| ())?;

		let id = GENESIS_AUTHORITY_SET_ID;
		<Authorities<T>>::put(bounded_authorities);
		<ValidatorSetId<T>>::put(id);
		// Like `pallet_session`, initialize the next validator set as well.
		<NextAuthorities<T>>::put(bounded_authorities);

		if let Some(validator_set) = ValidatorSet::<T::BeefyId>::new(authorities.clone(), id) {
			let next_id = id + 1;
			if let Some(next_validator_set) =
				ValidatorSet::<T::BeefyId>::new(authorities.clone(), next_id)
			{
				<T::OnNewValidatorSet as OnNewValidatorSet<_>>::on_new_validator_set(
					&validator_set,
					&next_validator_set,
				);
			}
		}
		Ok(())
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
		// we panic here as runtime maintainers can simply reconfigure genesis and restart the
		// chain easily
		Self::initialize_authorities(&authorities).expect("Authorities vec too big");
	}

	fn on_new_session<'a, I: 'a>(_changed: bool, validators: I, queued_validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, T::BeefyId)>,
	{
		let next_authorities = validators.map(|(_, k)| k).collect::<Vec<_>>();
		if next_authorities.len() as u32 > T::MaxAuthorities::get() {
			log::error!(
				target: "runtime::beefy",
				"authorities list {:?} truncated to length {}",
				next_authorities, T::MaxAuthorities::get(),
			);
		}
		let bounded_next_authorities =
			BoundedVec::<_, T::MaxAuthorities>::truncate_from(next_authorities);

		let next_queued_authorities = queued_validators.map(|(_, k)| k).collect::<Vec<_>>();
		if next_queued_authorities.len() as u32 > T::MaxAuthorities::get() {
			log::error!(
				target: "runtime::beefy",
				"queued authorities list {:?} truncated to length {}",
				next_queued_authorities, T::MaxAuthorities::get(),
			);
		}
		let bounded_next_queued_authorities =
			BoundedVec::<_, T::MaxAuthorities>::truncate_from(next_queued_authorities);

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
