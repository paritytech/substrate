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

//! # Root Offences Pallet
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
use sp_runtime::Perbill;
use sp_staking::offence::{DisableStrategy, OnOffenceHandler};

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config:
		frame_system::Config
		+ pallet_staking::Config
		+ pallet_session::Config<ValidatorId = <Self as frame_system::Config>::AccountId>
		+ pallet_session::historical::Config<
			FullIdentification = Exposure<
				<Self as frame_system::Config>::AccountId,
				BalanceOf<Self>,
			>,
			FullIdentificationOf = ExposureOf<Self>,
		>
	{
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// An offence was created by root.
		OffenceCreated { offenders: Vec<(T::AccountId, Perbill)> },
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Failed to get the active era from the staking pallet.
		FailedToGetActiveEra,
	}

	type OffenceDetails<T> = sp_staking::offence::OffenceDetails<
		<T as frame_system::Config>::AccountId,
		IdentificationTuple<T>,
	>;

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Allows the `root`, for example sudo to create an offence.
		#[pallet::weight(T::DbWeight::get().reads(2))]
		pub fn create_offence(
			origin: OriginFor<T>,
			offenders: Vec<(T::AccountId, Perbill)>,
		) -> DispatchResult {
			ensure_root(origin)?;

			let slash_fraction =
				offenders.clone().into_iter().map(|(_, fraction)| fraction).collect::<Vec<_>>();
			let offence_details = Self::get_offence_details(offenders.clone())?;

			Self::submit_offence(&offence_details, &slash_fraction);
			Self::deposit_event(Event::OffenceCreated { offenders });
			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {
		/// Returns a vector of offenders that are going to be slashed.
		fn get_offence_details(
			offenders: Vec<(T::AccountId, Perbill)>,
		) -> Result<Vec<OffenceDetails<T>>, DispatchError> {
			let now = Staking::<T>::active_era()
				.map(|e| e.index)
				.ok_or(Error::<T>::FailedToGetActiveEra)?;

			Ok(offenders
				.clone()
				.into_iter()
				.map(|(o, _)| OffenceDetails::<T> {
					offender: (o.clone(), Staking::<T>::eras_stakers(now, o)),
					reporters: vec![],
				})
				.collect())
		}

		/// Submits the offence by calling the `on_offence` function.
		fn submit_offence(offenders: &[OffenceDetails<T>], slash_fraction: &[Perbill]) {
			let session_index = <pallet_session::Pallet<T> as frame_support::traits::ValidatorSet<T::AccountId>>::session_index();

			<pallet_staking::Pallet<T> as OnOffenceHandler<
				T::AccountId,
				IdentificationTuple<T>,
				Weight,
			>>::on_offence(&offenders, &slash_fraction, session_index, DisableStrategy::WhenSlashed);
		}
	}
}
