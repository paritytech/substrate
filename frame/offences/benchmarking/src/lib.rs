// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

//! Offences pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]
#![cfg_attr(not(feature = "std"), no_std)]

mod mock;

use sp_std::{prelude::*, vec};

use frame_benchmarking::{account, benchmarks};
use frame_support::traits::{Currency, Get, ValidatorSet, ValidatorSetWithIdentification};
use frame_system::{Config as SystemConfig, Pallet as System, RawOrigin};

use sp_runtime::{
	traits::{Convert, Saturating, StaticLookup, UniqueSaturatedInto},
	Perbill,
};
use sp_staking::offence::{Offence, ReportOffence};

use pallet_babe::BabeEquivocationOffence;
use pallet_balances::Config as BalancesConfig;
use pallet_grandpa::{GrandpaEquivocationOffence, GrandpaTimeSlot};
use pallet_im_online::{Config as ImOnlineConfig, Pallet as ImOnline, UnresponsivenessOffence};
use pallet_offences::{Config as OffencesConfig, Pallet as Offences};
use pallet_session::{
	historical::{Config as HistoricalConfig, IdentificationTuple},
	Config as SessionConfig, SessionManager,
};
use pallet_staking::{
	Config as StakingConfig, Event as StakingEvent, Exposure, IndividualExposure,
	Pallet as Staking, RewardDestination, ValidatorPrefs,
};

const SEED: u32 = 0;

const MAX_REPORTERS: u32 = 100;
const MAX_OFFENDERS: u32 = 100;
const MAX_NOMINATORS: u32 = 100;

pub struct Pallet<T: Config>(Offences<T>);

pub trait Config:
	SessionConfig
	+ StakingConfig
	+ OffencesConfig
	+ ImOnlineConfig
	+ HistoricalConfig
	+ BalancesConfig
	+ IdTupleConvert<Self>
{
}

/// A helper trait to make sure we can convert `IdentificationTuple` coming from historical
/// and the one required by offences.
pub trait IdTupleConvert<T: HistoricalConfig + OffencesConfig> {
	/// Convert identification tuple from `historical` trait to the one expected by `offences`.
	fn convert(id: IdentificationTuple<T>) -> <T as OffencesConfig>::IdentificationTuple;
}

impl<T: HistoricalConfig + OffencesConfig> IdTupleConvert<T> for T
where
	<T as OffencesConfig>::IdentificationTuple: From<IdentificationTuple<T>>,
{
	fn convert(id: IdentificationTuple<T>) -> <T as OffencesConfig>::IdentificationTuple {
		id.into()
	}
}

type LookupSourceOf<T> = <<T as SystemConfig>::Lookup as StaticLookup>::Source;
type BalanceOf<T> =
	<<T as StakingConfig>::Currency as Currency<<T as SystemConfig>::AccountId>>::Balance;

struct Offender<T: Config> {
	pub controller: T::AccountId,
	pub stash: T::AccountId,
	pub nominator_stashes: Vec<T::AccountId>,
}

fn bond_amount<T: Config>() -> BalanceOf<T> {
	T::Currency::minimum_balance().saturating_mul(10_000u32.into())
}

fn create_offender<T: Config>(n: u32, nominators: u32) -> Result<Offender<T>, &'static str> {
	let stash: T::AccountId = account("stash", n, SEED);
	let controller: T::AccountId = account("controller", n, SEED);
	let controller_lookup: LookupSourceOf<T> = T::Lookup::unlookup(controller.clone());
	let reward_destination = RewardDestination::Staked;
	let amount = bond_amount::<T>();
	// add twice as much balance to prevent the account from being killed.
	let free_amount = amount.saturating_mul(2u32.into());
	T::Currency::make_free_balance_be(&stash, free_amount);
	Staking::<T>::bond(
		RawOrigin::Signed(stash.clone()).into(),
		controller_lookup.clone(),
		amount,
		reward_destination.clone(),
	)?;

	let validator_prefs =
		ValidatorPrefs { commission: Perbill::from_percent(50), ..Default::default() };
	Staking::<T>::validate(RawOrigin::Signed(controller.clone()).into(), validator_prefs)?;

	let mut individual_exposures = vec![];
	let mut nominator_stashes = vec![];
	// Create n nominators
	for i in 0..nominators {
		let nominator_stash: T::AccountId =
			account("nominator stash", n * MAX_NOMINATORS + i, SEED);
		let nominator_controller: T::AccountId =
			account("nominator controller", n * MAX_NOMINATORS + i, SEED);
		let nominator_controller_lookup: LookupSourceOf<T> =
			T::Lookup::unlookup(nominator_controller.clone());
		T::Currency::make_free_balance_be(&nominator_stash, free_amount);

		Staking::<T>::bond(
			RawOrigin::Signed(nominator_stash.clone()).into(),
			nominator_controller_lookup.clone(),
			amount,
			reward_destination.clone(),
		)?;

		let selected_validators: Vec<LookupSourceOf<T>> = vec![controller_lookup.clone()];
		Staking::<T>::nominate(
			RawOrigin::Signed(nominator_controller.clone()).into(),
			selected_validators,
		)?;

		individual_exposures
			.push(IndividualExposure { who: nominator_stash.clone(), value: amount });
		nominator_stashes.push(nominator_stash.clone());
	}

	let exposure = Exposure { total: amount * n.into(), own: amount, others: individual_exposures };
	let current_era = 0u32;
	Staking::<T>::add_era_stakers(current_era, stash.clone(), exposure);

	Ok(Offender { controller, stash, nominator_stashes })
}

fn make_offenders<T: Config>(
	num_offenders: u32,
	num_nominators: u32,
) -> Result<(Vec<IdentificationTuple<T>>, Vec<Offender<T>>), &'static str> {
	Staking::<T>::new_session(0);

	let mut offenders = vec![];
	for i in 0..num_offenders {
		let offender = create_offender::<T>(i + 1, num_nominators)?;
		offenders.push(offender);
	}

	Staking::<T>::start_session(0);

	let id_tuples = offenders
		.iter()
		.map(|offender| {
			<T as SessionConfig>::ValidatorIdOf::convert(offender.controller.clone())
				.expect("failed to get validator id from account id")
		})
		.map(|validator_id| {
			<T as HistoricalConfig>::FullIdentificationOf::convert(validator_id.clone())
				.map(|full_id| (validator_id, full_id))
				.expect("failed to convert validator id to full identification")
		})
		.collect::<Vec<IdentificationTuple<T>>>();
	Ok((id_tuples, offenders))
}

fn make_offenders_im_online<T: Config>(
	num_offenders: u32,
	num_nominators: u32,
) -> Result<(Vec<pallet_im_online::IdentificationTuple<T>>, Vec<Offender<T>>), &'static str> {
	Staking::<T>::new_session(0);

	let mut offenders = vec![];
	for i in 0..num_offenders {
		let offender = create_offender::<T>(i + 1, num_nominators)?;
		offenders.push(offender);
	}

	Staking::<T>::start_session(0);

	let id_tuples = offenders
		.iter()
		.map(|offender| {
			<
				<T as ImOnlineConfig>::ValidatorSet as ValidatorSet<T::AccountId>
			>::ValidatorIdOf::convert(offender.controller.clone())
			.expect("failed to get validator id from account id")
		})
		.map(|validator_id| {
			<
				<T as ImOnlineConfig>::ValidatorSet as ValidatorSetWithIdentification<T::AccountId>
			>::IdentificationOf::convert(validator_id.clone())
			.map(|full_id| (validator_id, full_id))
			.expect("failed to convert validator id to full identification")
		})
		.collect::<Vec<pallet_im_online::IdentificationTuple<T>>>();
	Ok((id_tuples, offenders))
}

#[cfg(test)]
fn check_events<T: Config, I: Iterator<Item = <T as SystemConfig>::RuntimeEvent>>(expected: I) {
	let events = System::<T>::events()
		.into_iter()
		.map(|frame_system::EventRecord { event, .. }| event)
		.collect::<Vec<_>>();
	let expected = expected.collect::<Vec<_>>();

	fn pretty<D: std::fmt::Debug>(header: &str, ev: &[D], offset: usize) {
		println!("{}", header);
		for (idx, ev) in ev.iter().enumerate() {
			println!("\t[{:04}] {:?}", idx + offset, ev);
		}
	}
	fn print_events<D: std::fmt::Debug>(idx: usize, events: &[D], expected: &[D]) {
		let window = 10;
		let start = idx.saturating_sub(window / 2);
		let end_got = (idx + window / 2).min(events.len());
		pretty("Got(window):", &events[start..end_got], start);
		let end_expected = (idx + window / 2).min(expected.len());
		pretty("Expected(window):", &expected[start..end_expected], start);
		println!("---------------");
		let start_got = events.len().saturating_sub(window);
		pretty("Got(end):", &events[start_got..], start_got);
		let start_expected = expected.len().saturating_sub(window);
		pretty("Expected(end):", &expected[start_expected..], start_expected);
	}
	let events_copy = events.clone();
	let expected_copy = expected.clone();

	for (idx, (a, b)) in events.into_iter().zip(expected).enumerate() {
		if a != b {
			print_events(idx, &events_copy, &expected_copy);
			println!("Mismatch at: {}", idx);
			println!("     Got: {:?}", b);
			println!("Expected: {:?}", a);
			if events_copy.len() != expected_copy.len() {
				println!(
					"Mismatching lengths. Got: {}, Expected: {}",
					events_copy.len(),
					expected_copy.len()
				)
			}
			panic!("Mismatching events.");
		}
	}

	if events_copy.len() != expected_copy.len() {
		print_events(0, &events_copy, &expected_copy);
		panic!("Mismatching lengths. Got: {}, Expected: {}", events_copy.len(), expected_copy.len())
	}
}

benchmarks! {
	report_offence_im_online {
		let r in 1 .. MAX_REPORTERS;
		// we skip 1 offender, because in such case there is no slashing
		let o in 2 .. MAX_OFFENDERS;
		let n in 0 .. MAX_NOMINATORS.min(<T as pallet_staking::Config>::MaxNominations::get());

		// Make r reporters
		let mut reporters = vec![];
		for i in 0 .. r {
			let reporter = account("reporter", i, SEED);
			reporters.push(reporter);
		}

		// make sure reporters actually get rewarded
		Staking::<T>::set_slash_reward_fraction(Perbill::one());

		let (offenders, raw_offenders) = make_offenders_im_online::<T>(o, n)?;
		let keys =  ImOnline::<T>::keys();
		let validator_set_count = keys.len() as u32;
		let offenders_count = offenders.len() as u32;
		let offence = UnresponsivenessOffence {
			session_index: 0,
			validator_set_count,
			offenders,
		};
		let slash_fraction = offence.slash_fraction(offenders_count);
		assert_eq!(System::<T>::event_count(), 0);
	}: {
		let _ = <T as ImOnlineConfig>::ReportUnresponsiveness::report_offence(
			reporters.clone(),
			offence
		);
	}
	verify {
		let bond_amount: u32 = UniqueSaturatedInto::<u32>::unique_saturated_into(bond_amount::<T>());
		let slash_amount = slash_fraction * bond_amount;
		let reward_amount = slash_amount.saturating_mul(1 + n) / 2;
		let reward = reward_amount / r;
		let slash = |id| core::iter::once(
			<T as StakingConfig>::RuntimeEvent::from(StakingEvent::<T>::Slashed{staker: id, amount: BalanceOf::<T>::from(slash_amount)})
		);
		let balance_slash = |id| core::iter::once(
			<T as BalancesConfig>::RuntimeEvent::from(pallet_balances::Event::<T>::Slashed{who: id, amount: slash_amount.into()})
		);
		let chill = |id| core::iter::once(
			<T as StakingConfig>::RuntimeEvent::from(StakingEvent::<T>::Chilled{stash: id})
		);
		let balance_deposit = |id, amount: u32|
			<T as BalancesConfig>::RuntimeEvent::from(pallet_balances::Event::<T>::Deposit{who: id, amount: amount.into()});
		let mut first = true;
		let slash_events = raw_offenders.into_iter()
			.flat_map(|offender| {
				let nom_slashes = offender.nominator_stashes.into_iter().flat_map(|nom| {
					balance_slash(nom.clone()).map(Into::into)
					.chain(slash(nom).map(Into::into))
				});

				let mut events = chill(offender.stash.clone()).map(Into::into)
					.chain(balance_slash(offender.stash.clone()).map(Into::into))
					.chain(slash(offender.stash).map(Into::into))
					.chain(nom_slashes)
					.collect::<Vec<_>>();

				// the first deposit creates endowed events, see `endowed_reward_events`
				if first {
					first = false;
					let mut reward_events = reporters.clone().into_iter()
						.flat_map(|reporter| vec![
							balance_deposit(reporter.clone(), reward).into(),
							frame_system::Event::<T>::NewAccount { account: reporter.clone() }.into(),
							<T as BalancesConfig>::RuntimeEvent::from(
								pallet_balances::Event::<T>::Endowed{account: reporter, free_balance: reward.into()}
							).into(),
						])
						.collect::<Vec<_>>();
					events.append(&mut reward_events);
					events.into_iter()
				} else {
					let mut reward_events = reporters.clone().into_iter()
						.map(|reporter| balance_deposit(reporter, reward).into())
						.collect::<Vec<_>>();
					events.append(&mut reward_events);
					events.into_iter()
				}
			})
			.collect::<Vec<_>>();



		#[cfg(test)]
		{
			// In case of error it's useful to see the inputs
			println!("Inputs: r: {}, o: {}, n: {}", r, o, n);
			// make sure that all slashes have been applied
			check_events::<T, _>(
				std::iter::empty()
					.chain(slash_events.into_iter().map(Into::into))
					.chain(std::iter::once(<T as OffencesConfig>::RuntimeEvent::from(
						pallet_offences::Event::Offence{
							kind: UnresponsivenessOffence::<T>::ID,
							timeslot: 0_u32.to_le_bytes().to_vec(),
						}
					).into()))
			);
		}
	}

	report_offence_grandpa {
		let n in 0 .. MAX_NOMINATORS.min(<T as pallet_staking::Config>::MaxNominations::get());

		// for grandpa equivocation reports the number of reporters
		// and offenders is always 1
		let reporters = vec![account("reporter", 1, SEED)];

		// make sure reporters actually get rewarded
		Staking::<T>::set_slash_reward_fraction(Perbill::one());

		let (mut offenders, raw_offenders) = make_offenders::<T>(1, n)?;
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
		// make sure that all slashes have been applied
		#[cfg(test)]
		assert_eq!(
			System::<T>::event_count(), 0
			+ 1 // offence
			+ 3 // reporter (reward + endowment)
			+ 2 // offenders slashed
			+ 1 // offenders chilled
			+ 2 * n // nominators slashed
		);
	}

	report_offence_babe {
		let n in 0 .. MAX_NOMINATORS.min(<T as pallet_staking::Config>::MaxNominations::get());

		// for babe equivocation reports the number of reporters
		// and offenders is always 1
		let reporters = vec![account("reporter", 1, SEED)];

		// make sure reporters actually get rewarded
		Staking::<T>::set_slash_reward_fraction(Perbill::one());

		let (mut offenders, raw_offenders) = make_offenders::<T>(1, n)?;
		let keys =  ImOnline::<T>::keys();

		let offence = BabeEquivocationOffence {
			slot: 0u64.into(),
			session_index: 0,
			validator_set_count: keys.len() as u32,
			offender: T::convert(offenders.pop().unwrap()),
		};
		assert_eq!(System::<T>::event_count(), 0);
	}: {
		let _ = Offences::<T>::report_offence(reporters, offence);
	}
	verify {
		// make sure that all slashes have been applied
		#[cfg(test)]
		assert_eq!(
			System::<T>::event_count(), 0
			+ 1 // offence
			+ 3 // reporter (reward + endowment)
			+ 2 // offenders slashed
			+ 1 // offenders chilled
			+ 2 * n // nominators slashed
		);
	}

	impl_benchmark_test_suite!(Pallet, crate::mock::new_test_ext(), crate::mock::Test);
}
