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

#![cfg_attr(not(feature = "std"), no_std)]

use pallet_staking::Pallet as Staking;
use sp_runtime::Perbill;
use sp_staking::offence::{DisableStrategy, OffenceDetails, OnOffenceHandler};
use pallet_staking::{Exposure, ExposureOf, BalanceOf};
use sp_runtime::traits::Convert;

pub use pallet::*;

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::config]
	pub trait Config:
		frame_system::Config
		+ pallet_session::Config
		+ pallet_staking::Config
		+ pallet_offences::Config
		+ pallet_session::historical::Config
	{
		type Event: From<Event<Self>> + IsType<<Self as frame_system::Config>::Event>;
		type IdentificationTuple: Parameter;
		type OnOffenceHandler: OnOffenceHandler<
			Self::AccountId,
			<Self as pallet::Config>::IdentificationTuple,
			Weight,
		>;
	}

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	pub type IdentificationTuple<T> = (
		<T as frame_system::Config>::AccountId,
		pallet_staking::Exposure<
			<T as frame_system::Config>::AccountId,
			<T as pallet_staking::Config>::CurrencyBalance,
		>,
	);

	#[pallet::call]
	impl<T: Config> Pallet<T> where
		T: pallet_session::Config<ValidatorId = <T as frame_system::Config>::AccountId>,
		T: pallet_session::historical::Config<
			FullIdentification = Exposure<<T as frame_system::Config>::AccountId, BalanceOf<T>>,
			FullIdentificationOf = ExposureOf<T>,
		>,
		T::SessionHandler: pallet_session::SessionHandler<<T as frame_system::Config>::AccountId>,
		T::SessionManager: pallet_session::SessionManager<<T as frame_system::Config>::AccountId>,
		T::ValidatorIdOf: Convert<
			<T as frame_system::Config>::AccountId,
			Option<<T as frame_system::Config>::AccountId>,
		>,
	{
		/// Allows the `root` to create an offence.
		#[pallet::weight(10_000)]
		pub fn create_offence(
			origin: OriginFor<T>,
			offenders: Vec<(T::AccountId, Perbill)>,
		) -> DispatchResult {
			ensure_root(origin)?;

			let slash_fractions: &[Perbill] = &(offenders
				.clone()
				.into_iter()
				.map(|(_, fraction)| fraction)
				.collect::<Vec<Perbill>>());

			let active_era = Staking::<T>::active_era().ok_or(Error::<T>::FailedToGetActiveEra)?;
			let now = active_era.index;

			let offender_details: &[OffenceDetails<
				T::AccountId,
				pallet_session::historical::IdentificationTuple<T>
			>] = &(
				offenders.into_iter().map(|(o, _)| {
					let offender: pallet_session::historical::IdentificationTuple<T> = (o.clone(), Staking::<T>::eras_stakers(now, o));
					OffenceDetails::<T::AccountId, pallet_session::historical::IdentificationTuple<T>> {
						offender,
						reporters: vec![],
					}
				}).collect::<Vec<OffenceDetails<
					T::AccountId,
					pallet_session::historical::IdentificationTuple<T>
				>>>()
			);

			<pallet_staking::Pallet<T> as OnOffenceHandler<T::AccountId, pallet_session::historical::IdentificationTuple<T>, Weight>>::on_offence(
				offender_details,
				slash_fractions,
				now,
				DisableStrategy::WhenSlashed,
			);

			Ok(())
		}
	}

	#[pallet::event]
	pub enum Event<T: Config> {}

	#[pallet::error]
	pub enum Error<T> {
		FailedToGetActiveEra,
	}
}
