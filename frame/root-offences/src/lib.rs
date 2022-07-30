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

use pallet_session::Pallet as Session;
use pallet_staking::Pallet as Staking;
use sp_runtime::Perbill;
use sp_staking::offence::{DisableStrategy, OffenceDetails, OnOffenceHandler};

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

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(10_000)]
		pub fn slash(
			origin: OriginFor<T>,
			offenders: Vec<(T::AccountId, Perbill)>,
		) -> DispatchResult {
			ensure_root(origin)?;

			let slash_fractions: &[Perbill] = &(offenders
				.clone()
				.into_iter()
				.map(|(_, fraction)| fraction)
				.collect::<Vec<Perbill>>());

			// FIX don't use unwrap!!
			let now = Staking::<T>::active_era().unwrap().index;

			let offs: Vec<
				OffenceDetails<T::AccountId, pallet_session::historical::IdentificationTuple<T>>,
			> = offenders
				.into_iter()
				.map(|(o, _)| {
					let validator_id = match <T as pallet_session::Config>::ValidatorId::try_from(o)
					{
						Ok(id) => id,
						Err(_) => panic!("FIX need to add actual error here!"),
					};
					OffenceDetails::<
						T::AccountId,
						pallet_session::historical::IdentificationTuple<T>,
					> {
						offender: (validator_id, (1, 2)),
						reporters: vec![],
					}
				})
				.collect();

			<T as pallet::Config>::OnOffenceHandler::on_offence(
				&[],
				slash_fractions,
				now,
				DisableStrategy::WhenSlashed,
			);

			Ok(())
		}
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {}

	#[pallet::error]
	pub enum Error<T> {
		CantGetValidatorId
	}
}
