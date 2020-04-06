// Copyright 2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Offences pallet benchmarking.

#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use sp_std::vec;

use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account};
use frame_support::traits::{Currency, OnInitialize};

use sp_runtime::{Perbill, traits::{Convert, StaticLookup}};
use sp_staking::offence::ReportOffence;

use pallet_im_online::{Trait as ImOnlineTrait, Module as ImOnline, UnresponsivenessOffence};
use pallet_offences::{Trait as OffencesTrait, Module as Offences};
use pallet_staking::{
	Module as Staking, Trait as StakingTrait, RewardDestination, ValidatorPrefs,
	Exposure, IndividualExposure, ElectionStatus
};
use pallet_session::Trait as SessionTrait;
use pallet_session::historical::{Trait as HistoricalTrait, IdentificationTuple};

const SEED: u32 = 0;

const MAX_USERS: u32 = 1000;
const MAX_REPORTERS: u32 = 100;
const MAX_OFFENDERS: u32 = 100;
const MAX_NOMINATORS: u32 = 100;
const MAX_DEFERRED_OFFENCES: u32 = 100;

pub struct Module<T: Trait>(Offences<T>);

pub trait Trait: SessionTrait + StakingTrait + OffencesTrait + ImOnlineTrait + HistoricalTrait {}

fn create_offender<T: Trait>(n: u32, nominators: u32) -> Result<T::AccountId, &'static str> {
	let stash: T::AccountId = account("stash", n, SEED);
	let controller: T::AccountId = account("controller", n, SEED);
	let controller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(controller.clone());
	let reward_destination = RewardDestination::Staked;
	let amount = T::Currency::minimum_balance();

	Staking::<T>::bond(
		RawOrigin::Signed(stash.clone()).into(),
		controller_lookup.clone(),
		amount.clone(),
		reward_destination.clone(),
	)?;

	let validator_prefs = ValidatorPrefs {
		commission: Perbill::from_percent(50),
	};
	Staking::<T>::validate(RawOrigin::Signed(controller.clone()).into(), validator_prefs)?;

	let mut individual_exposures = vec![];

	// Create n nominators
	for i in 0 .. nominators {
		let nominator_stash: T::AccountId = account("nominator stash", n * MAX_NOMINATORS + i, SEED);
		let nominator_controller: T::AccountId = account("nominator controller", n * MAX_NOMINATORS + i, SEED);
		let nominator_controller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(nominator_controller.clone());

		Staking::<T>::bond(
			RawOrigin::Signed(nominator_stash.clone()).into(),
			nominator_controller_lookup.clone(),
			amount,
			reward_destination,
		)?;

		let selected_validators: Vec<<T::Lookup as StaticLookup>::Source> = vec![controller_lookup.clone()];
		Staking::<T>::nominate(RawOrigin::Signed(nominator_controller.clone()).into(), selected_validators)?;

		individual_exposures.push(IndividualExposure {
			who: nominator_controller.clone(),
			value: amount.clone(),
		});
	}

	let exposure = Exposure {
		total: amount.clone() * n.into(),
		own: amount,
		others: individual_exposures,
	};
	let current_era = 0u32;
	Staking::<T>::add_era_stakers(current_era.into(), stash.clone().into(), exposure);

	Ok(controller)
}

fn make_offenders<T: Trait>(num_offenders: u32, num_nominators: u32) -> Result<Vec<IdentificationTuple<T>>, &'static str> {
	let mut offenders: Vec<T::AccountId> = vec![];

	for i in 0 .. num_offenders {
		let offender = create_offender::<T>(i, num_nominators)?;
		offenders.push(offender);
	}

	Ok(offenders.iter()
		.map(|id|
			<T as SessionTrait>::ValidatorIdOf::convert(id.clone())
				.expect("failed to get validator id from account id"))
		.map(|validator_id|
			<T as HistoricalTrait>::FullIdentificationOf::convert(validator_id.clone())
			.map(|full_id| (validator_id, full_id))
			.expect("failed to convert validator id to full identification"))
		.collect::<Vec<IdentificationTuple<T>>>())
}

benchmarks! {
	_ {
		let u in 1 .. MAX_USERS => ();
		let r in 1 .. MAX_REPORTERS => ();
		let o in 1 .. MAX_OFFENDERS => ();
		let n in 1 .. MAX_NOMINATORS => ();
		let d in 1 .. MAX_DEFERRED_OFFENCES => ();
	}

	report_offence {
		let r in ...;
		let o in ...;
		let n in ...;

		let mut reporters = vec![];

		for i in 0 .. r {
			let reporter = account("reporter", i, SEED);
			reporters.push(reporter);
		}
	
		let offenders = make_offenders::<T>(o, n).expect("failed to create offenders");
		let keys =  ImOnline::<T>::keys();

		let offence = UnresponsivenessOffence {
			session_index: 0,
			validator_set_count: keys.len() as u32,
			offenders,
		};

	}: {
		let _ = <T as ImOnlineTrait>::ReportUnresponsiveness::report_offence(reporters, offence);
	}

	on_initialize {
		let d in ...;

		Staking::<T>::put_election_status(ElectionStatus::Closed);

		let mut deferred_offences = vec![];

		for i in 0 .. d {
			deferred_offences.push((vec![], vec![], 0u32));
		}

		Offences::<T>::set_deferred_offences(deferred_offences);

	}: {
		Offences::<T>::on_initialize(u.into());
	}
}
