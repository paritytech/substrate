// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Testing utils for staking. Provides some common functions to setup staking state, such as
//! bonding validators, nominators, and generating different types of solutions.

use crate::{Pallet as Staking, *};
use frame_benchmarking::account;
use frame_system::RawOrigin;
use rand_chacha::{
	rand_core::{RngCore, SeedableRng},
	ChaChaRng,
};
use sp_io::hashing::blake2_256;

use frame_election_provider_support::SortedListProvider;
use frame_support::{pallet_prelude::*, traits::Currency};
use sp_runtime::{traits::StaticLookup, Perbill};
use sp_std::prelude::*;

const SEED: u32 = 0;

/// This function removes all validators and nominators from storage.
pub fn clear_validators_and_nominators<T: Config>() {
	#[allow(deprecated)]
	Validators::<T>::remove_all();

	// whenever we touch nominators counter we should update `T::VoterList` as well.
	#[allow(deprecated)]
	Nominators::<T>::remove_all();

	// NOTE: safe to call outside block production
	T::VoterList::unsafe_clear();
}

/// Grab a funded user.
pub fn create_funded_user<T: Config>(
	string: &'static str,
	n: u32,
	balance_factor: u32,
) -> T::AccountId {
	let user = account(string, n, SEED);
	let balance = T::Currency::minimum_balance() * balance_factor.into();
	let _ = T::Currency::make_free_balance_be(&user, balance);
	user
}

/// Grab a funded user with max Balance.
pub fn create_funded_user_with_balance<T: Config>(
	string: &'static str,
	n: u32,
	balance: BalanceOf<T>,
) -> T::AccountId {
	let user = account(string, n, SEED);
	let _ = T::Currency::make_free_balance_be(&user, balance);
	user
}

/// Create a stash and controller pair.
pub fn create_stash_controller<T: Config>(
	n: u32,
	balance_factor: u32,
	destination: RewardDestination<T::AccountId>,
) -> Result<(T::AccountId, T::AccountId), &'static str> {
	let stash = create_funded_user::<T>("stash", n, balance_factor);
	let controller = create_funded_user::<T>("controller", n, balance_factor);
	let controller_lookup = T::Lookup::unlookup(controller.clone());
	let amount = T::Currency::minimum_balance() * (balance_factor / 10).max(1).into();
	Staking::<T>::bond(
		RawOrigin::Signed(stash.clone()).into(),
		controller_lookup,
		amount,
		destination,
	)?;
	Ok((stash, controller))
}

/// Create a stash and controller pair with fixed balance.
pub fn create_stash_controller_with_balance<T: Config>(
	n: u32,
	balance: crate::BalanceOf<T>,
	destination: RewardDestination<T::AccountId>,
) -> Result<(T::AccountId, T::AccountId), &'static str> {
	let stash = create_funded_user_with_balance::<T>("stash", n, balance);
	let controller = create_funded_user_with_balance::<T>("controller", n, balance);
	let controller_lookup = T::Lookup::unlookup(controller.clone());

	Staking::<T>::bond(
		RawOrigin::Signed(stash.clone()).into(),
		controller_lookup,
		balance,
		destination,
	)?;
	Ok((stash, controller))
}

/// Create a stash and controller pair, where the controller is dead, and payouts go to controller.
/// This is used to test worst case payout scenarios.
pub fn create_stash_and_dead_controller<T: Config>(
	n: u32,
	balance_factor: u32,
	destination: RewardDestination<T::AccountId>,
) -> Result<(T::AccountId, T::AccountId), &'static str> {
	let stash = create_funded_user::<T>("stash", n, balance_factor);
	// controller has no funds
	let controller = create_funded_user::<T>("controller", n, 0);
	let controller_lookup = T::Lookup::unlookup(controller.clone());
	let amount = T::Currency::minimum_balance() * (balance_factor / 10).max(1).into();
	Staking::<T>::bond(
		RawOrigin::Signed(stash.clone()).into(),
		controller_lookup,
		amount,
		destination,
	)?;
	Ok((stash, controller))
}

/// create `max` validators.
pub fn create_validators<T: Config>(
	max: u32,
	balance_factor: u32,
) -> Result<Vec<AccountIdLookupOf<T>>, &'static str> {
	create_validators_with_seed::<T>(max, balance_factor, 0)
}

/// create `max` validators, with a seed to help unintentional prevent account collisions.
pub fn create_validators_with_seed<T: Config>(
	max: u32,
	balance_factor: u32,
	seed: u32,
) -> Result<Vec<AccountIdLookupOf<T>>, &'static str> {
	let mut validators: Vec<AccountIdLookupOf<T>> = Vec::with_capacity(max as usize);
	for i in 0..max {
		let (stash, controller) =
			create_stash_controller::<T>(i + seed, balance_factor, RewardDestination::Staked)?;
		let validator_prefs =
			ValidatorPrefs { commission: Perbill::from_percent(50), ..Default::default() };
		Staking::<T>::validate(RawOrigin::Signed(controller).into(), validator_prefs)?;
		let stash_lookup = T::Lookup::unlookup(stash);
		validators.push(stash_lookup);
	}
	Ok(validators)
}

/// This function generates validators and nominators who are randomly nominating
/// `edge_per_nominator` random validators (until `to_nominate` if provided).
///
/// NOTE: This function will remove any existing validators or nominators to ensure
/// we are working with a clean state.
///
/// Parameters:
/// - `validators`: number of bonded validators
/// - `nominators`: number of bonded nominators.
/// - `edge_per_nominator`: number of edge (vote) per nominator.
/// - `randomize_stake`: whether to randomize the stakes.
/// - `to_nominate`: if `Some(n)`, only the first `n` bonded validator are voted upon. Else, all of
///   them are considered and `edge_per_nominator` random validators are voted for.
///
/// Return the validators chosen to be nominated.
pub fn create_validators_with_nominators_for_era<T: Config>(
	validators: u32,
	nominators: u32,
	edge_per_nominator: usize,
	randomize_stake: bool,
	to_nominate: Option<u32>,
) -> Result<Vec<AccountIdLookupOf<T>>, &'static str> {
	clear_validators_and_nominators::<T>();

	let mut validators_stash: Vec<AccountIdLookupOf<T>> = Vec::with_capacity(validators as usize);
	let mut rng = ChaChaRng::from_seed(SEED.using_encoded(blake2_256));

	// Create validators
	for i in 0..validators {
		let balance_factor = if randomize_stake { rng.next_u32() % 255 + 10 } else { 100u32 };
		let (v_stash, v_controller) =
			create_stash_controller::<T>(i, balance_factor, RewardDestination::Staked)?;
		let validator_prefs =
			ValidatorPrefs { commission: Perbill::from_percent(50), ..Default::default() };
		Staking::<T>::validate(RawOrigin::Signed(v_controller.clone()).into(), validator_prefs)?;
		let stash_lookup = T::Lookup::unlookup(v_stash.clone());
		validators_stash.push(stash_lookup.clone());
	}

	let to_nominate = to_nominate.unwrap_or(validators_stash.len() as u32) as usize;
	let validator_chosen = validators_stash[0..to_nominate].to_vec();

	// Create nominators
	for j in 0..nominators {
		let balance_factor = if randomize_stake { rng.next_u32() % 255 + 10 } else { 100u32 };
		let (_n_stash, n_controller) =
			create_stash_controller::<T>(u32::MAX - j, balance_factor, RewardDestination::Staked)?;

		// Have them randomly validate
		let mut available_validators = validator_chosen.clone();
		let mut selected_validators: Vec<AccountIdLookupOf<T>> =
			Vec::with_capacity(edge_per_nominator);

		for _ in 0..validators.min(edge_per_nominator as u32) {
			let selected = rng.next_u32() as usize % available_validators.len();
			let validator = available_validators.remove(selected);
			selected_validators.push(validator);
		}
		Staking::<T>::nominate(
			RawOrigin::Signed(n_controller.clone()).into(),
			selected_validators,
		)?;
	}

	ValidatorCount::<T>::put(validators);

	Ok(validator_chosen)
}

/// get the current era.
pub fn current_era<T: Config>() -> EraIndex {
	<Pallet<T>>::current_era().unwrap_or(0)
}
