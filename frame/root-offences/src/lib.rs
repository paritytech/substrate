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

//! # Sudo Offences Pallet
//! Pallet that allows the root to create an offence.
//!
//! NOTE: This pallet should be used for testing purposes.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

use pallet_session::historical::IdentificationTuple;
use pallet_staking::{BalanceOf, Exposure, ExposureOf, Pallet as Staking};
use sp_runtime::{traits::Convert, Perbill};
use sp_staking::offence::{DisableStrategy, OnOffenceHandler};

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config + pallet_staking::Config {
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		CreatedOffence { offenders: Vec<(T::AccountId, Perbill)>, unapplied_slash: Weight },
	}

	#[pallet::error]
	pub enum Error<T> {
		FailedToGetActiveEra,
	}

	#[allow(type_alias_bounds)]
	type OffenceDetails<T: Config> =
		sp_staking::offence::OffenceDetails<T::AccountId, IdentificationTuple<T>>;

	#[pallet::call]
	impl<T: Config> Pallet<T>
	where
		T: pallet_session::Config<ValidatorId = <T as frame_system::Config>::AccountId>,
		T: pallet_session::historical::Config<
			FullIdentification = Exposure<<T as frame_system::Config>::AccountId, BalanceOf<T>>,
			FullIdentificationOf = ExposureOf<T>,
		>,
		T::ValidatorIdOf: Convert<
			<T as frame_system::Config>::AccountId,
			Option<<T as frame_system::Config>::AccountId>,
		>,
	{
		/// Allows the `root`, for example sudo to create an offence.
		#[pallet::weight(10_000)]
		pub fn create_offence(
			origin: OriginFor<T>,
			offenders: Vec<(T::AccountId, Perbill)>,
		) -> DispatchResult {
			ensure_root(origin)?;

			let slash_fraction = offenders
				.clone()
				.into_iter()
				.map(|(_, fraction)| fraction)
				.collect::<Vec<Perbill>>();

			let offence_details = Self::get_offence_details(offenders.clone())?;

			let unapplied_slash = Self::submit_offence(&offence_details, &slash_fraction)?;

			Self::deposit_event(Event::CreatedOffence { offenders, unapplied_slash });
			Ok(())
		}
	}

	impl<T: Config> Pallet<T>
	where
		T: pallet_session::Config<ValidatorId = <T as frame_system::Config>::AccountId>,
		T: pallet_session::historical::Config<
			FullIdentification = Exposure<<T as frame_system::Config>::AccountId, BalanceOf<T>>,
			FullIdentificationOf = ExposureOf<T>,
		>,
	{
		/// Submits the offence by calling the `on_offence` function.
		fn submit_offence(
			offenders: &[OffenceDetails<T>],
			slash_fraction: &[Perbill],
		) -> Result<Weight, DispatchError> {
			let session_index = <pallet_session::Pallet<T> as frame_support::traits::ValidatorSet<T::AccountId>>::session_index();

			Ok(<pallet_staking::Pallet<T> as OnOffenceHandler<
				T::AccountId,
				IdentificationTuple<T>,
				Weight,
			>>::on_offence(
				&offenders, &slash_fraction, session_index, DisableStrategy::WhenSlashed
			))
		}

		/// Returns a vector of offenders that are going to be slashed.
		fn get_offence_details(
			offenders: Vec<(T::AccountId, Perbill)>,
		) -> Result<Vec<OffenceDetails<T>>, DispatchError> {
			let active_era = Staking::<T>::active_era().ok_or(Error::<T>::FailedToGetActiveEra)?;
			let now = active_era.index;

			Ok(offenders
				.clone()
				.into_iter()
				.map(|(o, _)| OffenceDetails::<T> {
					offender: (o.clone(), Staking::<T>::eras_stakers(now, o)),
					reporters: vec![],
				})
				.collect())
		}
	}
}
