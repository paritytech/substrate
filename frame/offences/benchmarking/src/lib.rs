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

mod mock;

use sp_std::prelude::*;
use sp_std::vec;

use frame_system::{RawOrigin, Module as System, Trait as SystemTrait};
use frame_benchmarking::{benchmarks, account};
use frame_support::traits::{Currency, OnInitialize};

use sp_runtime::{Perbill, traits::{Convert, StaticLookup, Saturating, UniqueSaturatedInto}};
use sp_staking::offence::{ReportOffence, Offence, OffenceDetails};

use pallet_balances::{Trait as BalancesTrait};
use pallet_babe::BabeEquivocationOffence;
use pallet_grandpa::{GrandpaEquivocationOffence, GrandpaTimeSlot};
use pallet_im_online::{Trait as ImOnlineTrait, Module as ImOnline, UnresponsivenessOffence};
use pallet_offences::{Trait as OffencesTrait, Module as Offences};
use pallet_session::historical::{Trait as HistoricalTrait, IdentificationTuple};
use pallet_session::{Trait as SessionTrait, SessionManager};
use pallet_staking::{
	Module as Staking, Trait as StakingTrait, RewardDestination, ValidatorPrefs,
	Exposure, IndividualExposure, ElectionStatus, MAX_NOMINATIONS, Event as StakingEvent
};

const SEED: u32 = 0;

const MAX_REPORTERS: u32 = 100;
const MAX_OFFENDERS: u32 = 100;
const MAX_NOMINATORS: u32 = 100;
const MAX_DEFERRED_OFFENCES: u32 = 100;

pub struct Module<T: Trait>(Offences<T>);

pub trait Trait:
	SessionTrait
	+ StakingTrait
	+ OffencesTrait
	+ ImOnlineTrait
	+ HistoricalTrait
	+ BalancesTrait
	+ IdTupleConvert<Self>
{}

/// A helper trait to make sure we can convert `IdentificationTuple` coming from historical
/// and the one required by offences.
pub trait IdTupleConvert<T: HistoricalTrait + OffencesTrait> {
	/// Convert identification tuple from `historical` trait to the one expected by `offences`.
	fn convert(id: IdentificationTuple<T>) -> <T as OffencesTrait>::IdentificationTuple;
}

impl<T: HistoricalTrait + OffencesTrait> IdTupleConvert<T> for T where
	<T as OffencesTrait>::IdentificationTuple: From<IdentificationTuple<T>>
{
	fn convert(id: IdentificationTuple<T>) -> <T as OffencesTrait>::IdentificationTuple {
		id.into()
	}
}

type LookupSourceOf<T> = <<T as SystemTrait>::Lookup as StaticLookup>::Source;
type BalanceOf<T> = <<T as StakingTrait>::Currency as Currency<<T as SystemTrait>::AccountId>>::Balance;

struct Offender<T: Trait> {
	pub controller: T::AccountId,
	pub stash: T::AccountId,
	pub nominator_stashes: Vec<T::AccountId>,
}

fn bond_amount<T: Trait>() -> BalanceOf<T> {
	T::Currency::minimum_balance().saturating_mul(10_000.into())
}

fn create_offender<T: Trait>(n: u32, nominators: u32) -> Result<Offender<T>, &'static str> {
	let stash: T::AccountId = account("stash", n, SEED);
	let controller: T::AccountId = account("controller", n, SEED);
	let controller_lookup: LookupSourceOf<T> = T::Lookup::unlookup(controller.clone());
	let reward_destination = RewardDestination::Staked;
	let raw_amount = bond_amount::<T>();
	// add twice as much balance to prevent the account from being killed.
	let free_amount = raw_amount.saturating_mul(2.into());
	T::Currency::make_free_balance_be(&stash, free_amount);
	let amount: BalanceOf<T> = raw_amount.into();
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
	let mut nominator_stashes = vec![];
	// Create n nominators
	for i in 0 .. nominators {
		let nominator_stash: T::AccountId = account("nominator stash", n * MAX_NOMINATORS + i, SEED);
		let nominator_controller: T::AccountId = account("nominator controller", n * MAX_NOMINATORS + i, SEED);
		let nominator_controller_lookup: LookupSourceOf<T> = T::Lookup::unlookup(nominator_controller.clone());
		T::Currency::make_free_balance_be(&nominator_stash, free_amount.into());

		Staking::<T>::bond(
			RawOrigin::Signed(nominator_stash.clone()).into(),
			nominator_controller_lookup.clone(),
			amount.clone(),
			reward_destination,
		)?;

		let selected_validators: Vec<LookupSourceOf<T>> = vec![controller_lookup.clone()];
		Staking::<T>::nominate(RawOrigin::Signed(nominator_controller.clone()).into(), selected_validators)?;

		individual_exposures.push(IndividualExposure {
			who: nominator_stash.clone(),
			value: amount.clone(),
		});
		nominator_stashes.push(nominator_stash.clone());
	}

	let exposure = Exposure {
		total: amount.clone() * n.into(),
		own: amount,
		others: individual_exposures,
	};
	let current_era = 0u32;
	Staking::<T>::add_era_stakers(current_era.into(), stash.clone().into(), exposure);

	Ok(Offender { controller, stash, nominator_stashes })
}

fn make_offenders<T: Trait>(num_offenders: u32, num_nominators: u32) -> Result<
	(Vec<IdentificationTuple<T>>, Vec<Offender<T>>),
	&'static str
> {
	Staking::<T>::new_session(0);

	let mut offenders = vec![];
	for i in 0 .. num_offenders {
		let offender = create_offender::<T>(i + 1, num_nominators)?;
		offenders.push(offender);
	}

	Staking::<T>::start_session(0);

	let id_tuples = offenders.iter()
		.map(|offender|
			<T as SessionTrait>::ValidatorIdOf::convert(offender.controller.clone())
				.expect("failed to get validator id from account id"))
		.map(|validator_id|
			<T as HistoricalTrait>::FullIdentificationOf::convert(validator_id.clone())
			.map(|full_id| (validator_id, full_id))
			.expect("failed to convert validator id to full identification"))
		.collect::<Vec<IdentificationTuple<T>>>();
	Ok((id_tuples, offenders))
}

#[cfg(test)]
fn check_events<T: Trait, I: Iterator<Item = <T as SystemTrait>::Event>>(expected: I) {
	let events = System::<T>::events() .into_iter()
		.map(|frame_system::EventRecord { event, .. }| event).collect::<Vec<_>>();
	let expected = expected.collect::<Vec<_>>();
	let lengths = (events.len(), expected.len());
	let length_mismatch = if lengths.0 != lengths.1 {
		fn pretty<D: std::fmt::Debug>(header: &str, ev: &[D]) {
			println!("{}", header);
			for (idx, ev) in ev.iter().enumerate() {
				println!("\t[{:04}] {:?}", idx, ev);
			}
		}
		pretty("--Got:", &events);
		pretty("--Expected:", &expected);
		format!("Mismatching length. Got: {}, expected: {}", lengths.0, lengths.1)
	} else { Default::default() };

	for (idx, (a, b)) in events.into_iter().zip(expected).enumerate() {
		assert_eq!(a, b, "Mismatch at: {}. {}", idx, length_mismatch);
	}

	if !length_mismatch.is_empty() {
		panic!(length_mismatch);
	}
}

benchmarks! {
	_ { }

	report_offence_im_online {
		let r in 1 .. MAX_REPORTERS;
		// we skip 1 offender, because in such case there is no slashing
		let o in 2 .. MAX_OFFENDERS;
		let n in 0 .. MAX_NOMINATORS.min(MAX_NOMINATIONS as u32);

		// Make r reporters
		let mut reporters = vec![];
		for i in 0 .. r {
			let reporter = account("reporter", i, SEED);
			reporters.push(reporter);
		}

		// make sure reporters actually get rewarded
		Staking::<T>::set_slash_reward_fraction(Perbill::one());

		let (offenders, raw_offenders) = make_offenders::<T>(o, n)?;
		let keys =  ImOnline::<T>::keys();
		let validator_set_count = keys.len() as u32;

		let slash_fraction = UnresponsivenessOffence::<T::AccountId>::slash_fraction(
			offenders.len() as u32, validator_set_count,
		);
		let offence = UnresponsivenessOffence {
			session_index: 0,
			validator_set_count,
			offenders,
		};
		assert_eq!(System::<T>::event_count(), 0);
	}: {
		let _ = <T as ImOnlineTrait>::ReportUnresponsiveness::report_offence(
			reporters.clone(),
			offence
		);
	}
	verify {
		// make sure the report was not deferred
		assert!(Offences::<T>::deferred_offences().is_empty());
		let slash_amount = slash_fraction * bond_amount::<T>().unique_saturated_into() as u32;
		let reward_amount = slash_amount * (1 + n) / 2;
		let mut slash_events = raw_offenders.into_iter()
			.flat_map(|offender| {
				core::iter::once(offender.stash).chain(offender.nominator_stashes.into_iter())
			})
			.map(|stash| <T as StakingTrait>::Event::from(
				StakingEvent::<T>::Slash(stash, BalanceOf::<T>::from(slash_amount))
			))
			.collect::<Vec<_>>();
		let reward_events = reporters.into_iter()
			.flat_map(|reporter| vec![
				frame_system::Event::<T>::NewAccount(reporter.clone()).into(),
				<T as BalancesTrait>::Event::from(
					pallet_balances::Event::<T>::Endowed(reporter.clone(), (reward_amount / r).into())
				).into()
			]);

		// rewards are applied after first offender and it's nominators
		let slash_rest = slash_events.split_off(1 + n as usize);

		// make sure that all slashes have been applied
		#[cfg(test)]
		check_events::<T, _>(
			std::iter::empty()
				.chain(slash_events.into_iter().map(Into::into))
				.chain(reward_events)
				.chain(slash_rest.into_iter().map(Into::into))
				.chain(std::iter::once(<T as OffencesTrait>::Event::from(
					pallet_offences::Event::Offence(
						UnresponsivenessOffence::<T>::ID,
						0_u32.to_le_bytes().to_vec(),
						true
					)
				).into()))
		);
	}

	report_offence_grandpa {
		let r in 1 .. MAX_REPORTERS;
		let n in 0 .. MAX_NOMINATORS.min(MAX_NOMINATIONS as u32);
		let o = 1;

		// Make r reporters
		let mut reporters = vec![];
		for i in 0 .. r {
			let reporter = account("reporter", i, SEED);
			reporters.push(reporter);
		}

		// make sure reporters actually get rewarded
		Staking::<T>::set_slash_reward_fraction(Perbill::one());

		let (mut offenders, raw_offenders) = make_offenders::<T>(o, n)?;
		let keys = ImOnline::<T>::keys();

		let offence = GrandpaEquivocationOffence {
			time_slot: GrandpaTimeSlot { set_id: 0, round: 0 },
			session_index: 0,
			validator_set_count: keys.len() as u32,
			offender: T::convert(offenders.pop().unwrap()),
		};
		assert_eq!(System::<T>::event_count(), 0);
	}: {
		let _ = Offences::<T>::report_offence(reporters, offence);
	}
	verify {
		// make sure the report was not deferred
		assert!(Offences::<T>::deferred_offences().is_empty());
		// make sure that all slashes have been applied
		assert_eq!(
			System::<T>::event_count(), 0
			+ 1 // offence
			+ 2 * r // reporter (reward + endowment)
			+ o // offenders slashed
			+ o * n // nominators slashed
		);
	}

	report_offence_babe {
		let r in 1 .. MAX_REPORTERS;
		let n in 0 .. MAX_NOMINATORS.min(MAX_NOMINATIONS as u32);
		let o = 1;

		// Make r reporters
		let mut reporters = vec![];
		for i in 0 .. r {
			let reporter = account("reporter", i, SEED);
			reporters.push(reporter);
		}

		// make sure reporters actually get rewarded
		Staking::<T>::set_slash_reward_fraction(Perbill::one());

		let (mut offenders, raw_offenders) = make_offenders::<T>(o, n)?;
		let keys =  ImOnline::<T>::keys();

		let offence = BabeEquivocationOffence {
			slot: 0,
			session_index: 0,
			validator_set_count: keys.len() as u32,
			offender: T::convert(offenders.pop().unwrap()),
		};
		assert_eq!(System::<T>::event_count(), 0);
	}: {
		let _ = Offences::<T>::report_offence(reporters, offence);
	}
	verify {
		// make sure the report was not deferred
		assert!(Offences::<T>::deferred_offences().is_empty());
		// make sure that all slashes have been applied
		assert_eq!(
			System::<T>::event_count(), 0
			+ 1 // offence
			+ 2 * r // reporter (reward + endowment)
			+ o // offenders slashed
			+ o * n // nominators slashed
		);
	}

	on_initialize {
		let d in 1 .. MAX_DEFERRED_OFFENCES;
		let o = 10;
		let n = 100;

		Staking::<T>::put_election_status(ElectionStatus::Closed);

		let mut deferred_offences = vec![];
		let offenders = make_offenders::<T>(o, n)?.0;
		let offence_details = offenders.into_iter()
			.map(|offender| OffenceDetails {
				offender: T::convert(offender),
				reporters: vec![],
			})
			.collect::<Vec<_>>();

		for i in 0 .. d {
			let fractions = offence_details.iter()
				.map(|_| Perbill::from_percent(100 * (i + 1) / MAX_DEFERRED_OFFENCES))
				.collect::<Vec<_>>();
			deferred_offences.push((offence_details.clone(), fractions.clone(), 0u32));
		}

		Offences::<T>::set_deferred_offences(deferred_offences);
		assert!(!Offences::<T>::deferred_offences().is_empty());
	}: {
		Offences::<T>::on_initialize(0.into());
	}
	verify {
		// make sure that all deferred offences were reported with Ok status.
		assert!(Offences::<T>::deferred_offences().is_empty());
		assert_eq!(
			System::<T>::event_count(), d * (0
			+ o // offenders slashed
			+ o * n // nominators slashed
		));
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mock::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_report_offence_im_online::<Test>());
			assert_ok!(test_benchmark_report_offence_grandpa::<Test>());
			assert_ok!(test_benchmark_report_offence_babe::<Test>());
			assert_ok!(test_benchmark_on_initialize::<Test>());
		});
	}
}
