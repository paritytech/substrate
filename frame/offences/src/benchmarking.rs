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

use super::*;

use sp_std::prelude::*;
use frame_benchmarking::{benchmarks, account};
use frame_support::traits::Currency;
use frame_system::RawOrigin;
use sp_runtime::{Perbill, traits::{Convert, StaticLookup}};
use pallet_im_online::UnresponsivenessOffence;
use pallet_staking::{Module as Staking, RewardDestination, ValidatorPrefs};

const SEED: u32 = 0;
const MAX_REPORTERS: u32 = 1000;
const MAX_OFFENDERS: u32 = 1000;

pub trait Trait: pallet_staking::Trait + crate::Trait + pallet_im_online::Trait {}

pub fn create_offender<T: frame_system::Trait + pallet_staking::Trait>(n: u32) -> Result<T::AccountId, &'static str> {
	let stash: T::AccountId = account("stash", n, 0);
	let controller: T::AccountId = account("controller", n, 0);
	let controller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(controller.clone());
	let reward_destination = RewardDestination::Staked;
	let amount = T::Currency::minimum_balance() * 10.into();
	Staking::<T>::bond(RawOrigin::Signed(stash.clone()).into(), controller_lookup, amount, reward_destination)?;
	let validator_prefs = ValidatorPrefs {
		commission: Perbill::from_percent(50),
	};
	Staking::<T>::validate(RawOrigin::Signed(controller.clone()).into(), validator_prefs)?;

	return Ok(controller)
}

benchmarks! {
	_ {
		let r in 1 .. MAX_REPORTERS => ();
		let o in 1 .. MAX_OFFENDERS => ();
	}

	report_offence {
		let r in ...;
		let o in ...;

		let mut offenders: Vec<T::AccountId> = vec![];
		for i in 0 .. o {
			let offender = create_offender::<T>(i)?;
			offenders.push(offender);
		}

		let offenders = offenders.iter()
			.map(|id | (id, <T as pallet_session::Trait>::ValidatorIdOf::convert(id.clone()).expect("validator exist for this id")))
			.map(|(id, validator_id)| <T as pallet_session::historical::Trait>::FullIdentificationOf::convert(validator_id.clone()).map(|full_id| (validator_id, full_id)).expect("full identification exist for this validator"))
			.collect::<Vec<pallet_session::historical::IdentificationTuple<T>>>();


		let offence = UnresponsivenessOffence {
			session_index: 0,
			validator_set_count: 0,
			offenders,
		};

		let mut reporters = vec![];
		for i in 0 .. r {
			let reporter = account("reporter", i, SEED);
			reporters.push(reporter);
		}

	}: {
		let _ = <T as pallet_im_online::Trait>::ReportUnresponsiveness::report_offence(reporters, offence);
	}
}