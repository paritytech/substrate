// Sassafras This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Consensus extension module for Sassafras consensus.
//!
//! Sassafras is a constant-time block production protocol that aims to ensure that
//! there is exactly one block produced with constant time intervals rather multiple
//! or none.
//!
//! We run a lottery to distribute block production slots in an epoch and to fix the
//! order validators produce blocks by the beginning of an epoch.
//!
//! Each validator signs the same VRF input and publish the output onchain. This
//! value is their lottery ticket that can be validated against their public key.
//!
//! We want to keep lottery winners secret, i.e. do not publish their public keys.
//! At the begin of the epoch all the validators tickets are published but not their
//! public keys.
//!
//! A valid tickets are validated when an honest validator reclaims it on block
//! production.
//!
//! To prevent submission of fake tickets, resulting in empty slots, the validator
//! when submitting the ticket accompanies it with a SNARK of the statement: "Here's
//! my VRF output that has been generated using the given VRF input and my secret
//! key. I'm not telling you my keys, but my public key is among those of the
//! nominated validators", that is validated before the lottery.
//!
//! To anonymously publish the ticket to the chain a validator sends their tickets
//! to a random validator who later puts it on-chain as a transaction.

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(unused_must_use, unsafe_code, unused_variables, unused_must_use)]

use frame_support::{
	traits::{FindAuthor, Get, OneSessionHandler},
	weights::Weight,
	WeakBoundedVec,
};
use sp_runtime::{
	traits::{SaturatedConversion, Saturating},
	ConsensusEngineId, Permill,
};
use sp_std::prelude::Vec;

pub use sp_consensus_sassafras::{
	AuthorityId, SassafrasAuthorityWeight, SassafrasEpochConfiguration, Slot, PUBLIC_KEY_LENGTH,
	RANDOMNESS_LENGTH, SASSAFRAS_ENGINE_ID, VRF_OUTPUT_LENGTH,
};

//#[cfg(test)]
//mod mock;
//
//#[cfg(test)]
//mod tests;
//
//#[cfg(feature = "runtime-benchmarks")]
//mod benchmarking;

pub use pallet::*;

/// Trigger an epoch change, if any should take place.
pub trait EpochChangeTrigger {
	/// Trigger an epoch change, if any should take place. This should be called
	/// during every block, after initialization is done.
	fn trigger<T: Config>(now: T::BlockNumber);
}

/// A type signifying to Sassafras that an external trigger
/// for epoch changes (e.g. pallet-session) is used.
pub struct ExternalTrigger;

impl EpochChangeTrigger for ExternalTrigger {
	fn trigger<T: Config>(_: T::BlockNumber) {} // nothing to do - trigger is external.
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	/// The Sassafras pallet.
	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	/// Configuration parameters.
	// TODO-SASS: this is incomplete
	#[pallet::config]
	#[pallet::disable_frame_system_supertrait_check]
	pub trait Config: pallet_timestamp::Config {
		/// The amount of time, in slots, that each epoch should last.
		/// NOTE: Currently it is not possible to change the epoch duration after the chain has
		/// started. Attempting to do so will brick block production.
		#[pallet::constant]
		type EpochDuration: Get<u64>;

		/// The expected average block time at which BABE should be creating
		/// blocks. Since Sassafras is probabilistic it is not trivial to figure out
		/// what the expected average block time should be based on the slot
		/// duration and the security parameter `c` (where `1 - c` represents
		/// the probability of a slot being empty).
		#[pallet::constant]
		type ExpectedBlockTime: Get<Self::Moment>;

		/// Sassafras requires some logic to be triggered on every block to query for whether an
		/// epoch has ended and to perform the transition to the next epoch.
		///
		/// Typically, the `ExternalTrigger` type should be used. An internal trigger should only
		/// be used when no other module is responsible for changing authority set.
		type EpochChangeTrigger: EpochChangeTrigger;

		/// Max number of authorities allowed
		#[pallet::constant]
		type MaxAuthorities: Get<u32>;
	}

	// TODO-SASS
	// Errors inform users that something went wrong.
	#[pallet::error]
	pub enum Error<T> {
		/// Errors should have helpful documentation associated with them.
		StorageOverflow,
	}

	/// Current epoch authorities.
	#[pallet::storage]
	#[pallet::getter(fn authorities)]
	pub type Authorities<T: Config> = StorageValue<
		_,
		WeakBoundedVec<(AuthorityId, SassafrasAuthorityWeight), T::MaxAuthorities>,
		ValueQuery,
	>;

	/// Current slot number.
	#[pallet::storage]
	#[pallet::getter(fn current_slot)]
	pub type CurrentSlot<T> = StorageValue<_, Slot, ValueQuery>;

	/// Next epoch authorities.
	#[pallet::storage]
	pub(super) type NextAuthorities<T: Config> = StorageValue<
		_,
		WeakBoundedVec<(AuthorityId, SassafrasAuthorityWeight), T::MaxAuthorities>,
		ValueQuery,
	>;

	/// The configuration for the current epoch. Should never be `None` as it is initialized in
	/// genesis.
	#[pallet::storage]
	pub(super) type EpochConfig<T> = StorageValue<_, SassafrasEpochConfiguration>;

	#[cfg_attr(feature = "std", derive(Default))]
	#[pallet::genesis_config]
	pub struct GenesisConfig {
		pub authorities: Vec<(AuthorityId, SassafrasAuthorityWeight)>,
		pub epoch_config: Option<SassafrasEpochConfiguration>,
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig {
		fn build(&self) {
			//SegmentIndex::<T>::put(0); // TODO-SASS Used by Babe to collect randomness under
			// construction
			Pallet::<T>::initialize_genesis_authorities(&self.authorities);
			EpochConfig::<T>::put(
				self.epoch_config.clone().expect("epoch_config must not be None"),
			);
		}
	}

	// TODO-SASS
	// #[pallet::hooks]

	// TODO-SASS
	// Dispatchable functions allows users to interact with the pallet and invoke state changes.
	// These functions materialize as "extrinsics", which are often compared to transactions.
	// Dispatchable functions must be annotated with a weight and must return a DispatchResult.
	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// An example dispatchable that takes a singles value as a parameter, writes the value to
		/// storage and emits an event. This function must be dispatched by a signed extrinsic.
		#[pallet::weight(10_000 + T::DbWeight::get().writes(1))]
		pub fn do_something(origin: OriginFor<T>, something: u32) -> DispatchResult {
			// Check that the extrinsic was signed and get the signer.
			// This function will return an error if the extrinsic is not signed.
			// https://docs.substrate.io/v3/runtime/origins
			let _who = ensure_signed(origin)?;
			let _ = something;

			Ok(())
		}
	}
}

impl<T: Config> FindAuthor<u32> for Pallet<T> {
	fn find_author<'a, I>(digests: I) -> Option<u32>
	where
		I: 'a + IntoIterator<Item = (ConsensusEngineId, &'a [u8])>,
	{
		for (id, mut data) in digests.into_iter() {
			if id == SASSAFRAS_ENGINE_ID {
				return None
				// TODO-SASS
				//let pre_digest: PreDigest = PreDigest::decode(&mut data).ok()?;
				//return Some(pre_digest.authority_index())
			}
		}

		None
	}
}

impl<T: Config> pallet_session::ShouldEndSession<T::BlockNumber> for Pallet<T> {
	fn should_end_session(now: T::BlockNumber) -> bool {
		// it might be (and it is in current implementation) that session module is calling
		// `should_end_session` from it's own `on_initialize` handler, in which case it's
		// possible that babe's own `on_initialize` has not run yet, so let's ensure that we
		// have initialized the pallet and updated the current slot.

		// TODO-SASS
		//Self::initialize(now);
		//Self::should_epoch_change(now)
		false
	}
}

// TODO-SASS
// Inherent methods
impl<T: Config> Pallet<T> {
	/// Determine the BABE slot duration based on the Timestamp module configuration.
	pub fn slot_duration() -> T::Moment {
		// TODO-SASS: clarify why this is doubled
		// we double the minimum block-period so each author can always propose within
		// the majority of their slot.
		<T as pallet_timestamp::Config>::MinimumPeriod::get().saturating_mul(2u32.into())
	}

	/// DANGEROUS: Enact an epoch change. Should be done on every block where `should_epoch_change`
	/// has returned `true`, and the caller is the only caller of this function.
	///
	/// Typically, this is not handled directly by the user, but by higher-level validator-set
	/// manager logic like `pallet-session`.
	pub fn enact_epoch_change(
		authorities: WeakBoundedVec<(AuthorityId, SassafrasAuthorityWeight), T::MaxAuthorities>,
		next_authorities: WeakBoundedVec<
			(AuthorityId, SassafrasAuthorityWeight),
			T::MaxAuthorities,
		>,
	) {
		let _ = authorities;
		let _ = next_authorities;

		//TODO-SASS
		// // PRECONDITION: caller has done initialization and is guaranteed
		// // by the session module to be called before this.
		// debug_assert!(Self::initialized().is_some());

		// // Update epoch index
		// let epoch_index = EpochIndex::<T>::get()
		// 	.checked_add(1)
		// 	.expect("epoch indices will never reach 2^64 before the death of the universe; qed");

		// EpochIndex::<T>::put(epoch_index);
		// Authorities::<T>::put(authorities);

		// // Update epoch randomness.
		// let next_epoch_index = epoch_index
		// 	.checked_add(1)
		// 	.expect("epoch indices will never reach 2^64 before the death of the universe; qed");

		// // Returns randomness for the current epoch and computes the *next*
		// // epoch randomness.
		// let randomness = Self::randomness_change_epoch(next_epoch_index);
		// Randomness::<T>::put(randomness);

		// // Update the next epoch authorities.
		// NextAuthorities::<T>::put(&next_authorities);

		// // Update the start blocks of the previous and new current epoch.
		// <EpochStart<T>>::mutate(|(previous_epoch_start_block, current_epoch_start_block)| {
		// 	*previous_epoch_start_block = sp_std::mem::take(current_epoch_start_block);
		// 	*current_epoch_start_block = <frame_system::Pallet<T>>::block_number();
		// });

		// // After we update the current epoch, we signal the *next* epoch change
		// // so that nodes can track changes.
		// let next_randomness = NextRandomness::<T>::get();

		// let next_epoch = NextEpochDescriptor {
		// 	authorities: next_authorities.to_vec(),
		// 	randomness: next_randomness,
		// };
		// Self::deposit_consensus(ConsensusLog::NextEpochData(next_epoch));

		// if let Some(next_config) = NextEpochConfig::<T>::get() {
		// 	EpochConfig::<T>::put(next_config);
		// }

		// if let Some(pending_epoch_config_change) = PendingEpochConfigChange::<T>::take() {
		// 	let next_epoch_config: BabeEpochConfiguration =
		// 		pending_epoch_config_change.clone().into();
		// 	NextEpochConfig::<T>::put(next_epoch_config);

		// 	Self::deposit_consensus(ConsensusLog::NextConfigData(pending_epoch_config_change));
		// }
	}

	// Initialize authorities on genesis phase.
	fn initialize_genesis_authorities(authorities: &[(AuthorityId, SassafrasAuthorityWeight)]) {
		if !authorities.is_empty() {
			assert!(Authorities::<T>::get().is_empty(), "Authorities are already initialized!");
			let bounded_authorities =
				WeakBoundedVec::<_, T::MaxAuthorities>::try_from(authorities.to_vec())
					.expect("Initial number of authorities should be lower than T::MaxAuthorities");
			Authorities::<T>::put(&bounded_authorities);
			NextAuthorities::<T>::put(&bounded_authorities);
		}
	}
}

impl<T: Config> frame_support::traits::EstimateNextSessionRotation<T::BlockNumber> for Pallet<T> {
	fn average_session_length() -> T::BlockNumber {
		T::EpochDuration::get().saturated_into()
	}

	fn estimate_current_session_progress(_now: T::BlockNumber) -> (Option<Permill>, Weight) {
		// let elapsed = CurrentSlot::<T>::get().saturating_sub(Self::current_epoch_start()) + 1;

		// (
		// 	Some(Permill::from_rational(*elapsed, T::EpochDuration::get())),
		// 	// Read: Current Slot, Epoch Index, Genesis Slot
		// 	T::DbWeight::get().reads(3),
		// )
		(None, Weight::default())
	}

	fn estimate_next_session_rotation(now: T::BlockNumber) -> (Option<T::BlockNumber>, Weight) {
		// (
		// 	Self::next_expected_epoch_change(now),
		// 	// Read: Current Slot, Epoch Index, Genesis Slot
		// 	T::DbWeight::get().reads(3),
		// )
		(None, Weight::default())
	}
}

impl<T: Config> sp_runtime::BoundToRuntimeAppPublic for Pallet<T> {
	type Public = AuthorityId;
}

// TODO-SASS
impl<T: Config> OneSessionHandler<T::AccountId> for Pallet<T> {
	type Key = AuthorityId;

	fn on_genesis_session<'a, I: 'a>(validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, AuthorityId)>,
	{
		let authorities = validators.map(|(_, k)| (k, 1)).collect::<Vec<_>>();
		Self::initialize_genesis_authorities(&authorities);
	}

	fn on_new_session<'a, I: 'a>(_changed: bool, validators: I, queued_validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, AuthorityId)>,
	{
		let authorities = validators.map(|(_account, k)| (k, 1)).collect::<Vec<_>>();
		let bounded_authorities = WeakBoundedVec::<_, T::MaxAuthorities>::force_from(
			authorities,
			Some(
				"Warning: The session has more validators than expected. \
				A runtime configuration adjustment may be needed.",
			),
		);

		let next_authorities = queued_validators.map(|(_account, k)| (k, 1)).collect::<Vec<_>>();
		let next_bounded_authorities = WeakBoundedVec::<_, T::MaxAuthorities>::force_from(
			next_authorities,
			Some(
				"Warning: The session has more queued validators than expected. \
				A runtime configuration adjustment may be needed.",
			),
		);

		Self::enact_epoch_change(bounded_authorities, next_bounded_authorities)
	}

	fn on_disabled(i: u32) {
		let _ = i;
		// TODO-SASS
		//Self::deposit_consensus(ConsensusLog::OnDisabled(i))
	}
}
