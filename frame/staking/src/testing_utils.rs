// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

use crate::*;
use crate::Module as Staking;
use frame_benchmarking::account;
use frame_system::RawOrigin;
use sp_io::hashing::blake2_256;
use rand_chacha::{rand_core::{RngCore, SeedableRng}, ChaChaRng};
use sp_npos_elections::*;

const SEED: u32 = 0;

/// This function removes all validators and nominators from storage.
pub fn clear_validators_and_nominators<T: Config>() {
	Validators::<T>::remove_all();
	Nominators::<T>::remove_all();
}

/// Grab a funded user.
pub fn create_funded_user<T: Config>(
	string: &'static str,
	n: u32,
	balance_factor: u32,
) -> T::AccountId {
	let user = account(string, n, SEED);
	let balance = T::Currency::minimum_balance() * balance_factor.into();
	T::Currency::make_free_balance_be(&user, balance);
	// ensure T::CurrencyToVote will work correctly.
	T::Currency::issue(balance);
	user
}

/// Create a stash and controller pair.
pub fn create_stash_controller<T: Config>(
	n: u32,
	balance_factor: u32,
	destination: RewardDestination<T::AccountId>,
)
	-> Result<(T::AccountId, T::AccountId), &'static str>
{
	let stash = create_funded_user::<T>("stash", n, balance_factor);
	let controller = create_funded_user::<T>("controller", n, balance_factor);
	let controller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(controller.clone());
	let amount = T::Currency::minimum_balance() * (balance_factor / 10).max(1).into();
	Staking::<T>::bond(RawOrigin::Signed(stash.clone()).into(), controller_lookup, amount, destination)?;
	return Ok((stash, controller))
}

/// Create a stash and controller pair, where the controller is dead, and payouts go to controller.
/// This is used to test worst case payout scenarios.
pub fn create_stash_and_dead_controller<T: Config>(
	n: u32,
	balance_factor: u32,
	destination: RewardDestination<T::AccountId>,
)
	-> Result<(T::AccountId, T::AccountId), &'static str>
{
	let stash = create_funded_user::<T>("stash", n, balance_factor);
	// controller has no funds
	let controller = create_funded_user::<T>("controller", n, 0);
	let controller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(controller.clone());
	let amount = T::Currency::minimum_balance() * (balance_factor / 10).max(1).into();
	Staking::<T>::bond(RawOrigin::Signed(stash.clone()).into(), controller_lookup, amount, destination)?;
	return Ok((stash, controller))
}

/// create `max` validators.
pub fn create_validators<T: Config>(
	max: u32,
	balance_factor: u32,
) -> Result<Vec<<T::Lookup as StaticLookup>::Source>, &'static str> {
	let mut validators: Vec<<T::Lookup as StaticLookup>::Source> = Vec::with_capacity(max as usize);
	for i in 0 .. max {
		let (stash, controller) = create_stash_controller::<T>(i, balance_factor, RewardDestination::Staked)?;
		let validator_prefs = ValidatorPrefs {
			commission: Perbill::from_percent(50),
			.. Default::default()
		};
		Staking::<T>::validate(RawOrigin::Signed(controller).into(), validator_prefs)?;
		let stash_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(stash);
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
/// - `to_nominate`: if `Some(n)`, only the first `n` bonded validator are voted upon.
///    Else, all of them are considered and `edge_per_nominator` random validators are voted for.
///
/// Return the validators choosen to be nominated.
pub fn create_validators_with_nominators_for_era<T: Config>(
	validators: u32,
	nominators: u32,
	edge_per_nominator: usize,
	randomize_stake: bool,
	to_nominate: Option<u32>,
) -> Result<Vec<<T::Lookup as StaticLookup>::Source>, &'static str> {
	clear_validators_and_nominators::<T>();

	let mut validators_stash: Vec<<T::Lookup as StaticLookup>::Source>
		= Vec::with_capacity(validators as usize);
	let mut rng = ChaChaRng::from_seed(SEED.using_encoded(blake2_256));

	// Create validators
	for i in 0 .. validators {
		let balance_factor = if randomize_stake { rng.next_u32() % 255 + 10 } else { 100u32 };
		let (v_stash, v_controller) = create_stash_controller::<T>(i, balance_factor, RewardDestination::Staked)?;
		let validator_prefs = ValidatorPrefs {
			commission: Perbill::from_percent(50),
			.. Default::default()
		};
		Staking::<T>::validate(RawOrigin::Signed(v_controller.clone()).into(), validator_prefs)?;
		let stash_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(v_stash.clone());
		validators_stash.push(stash_lookup.clone());
	}

	let to_nominate = to_nominate.unwrap_or(validators_stash.len() as u32) as usize;
	let validator_choosen = validators_stash[0..to_nominate].to_vec();

	// Create nominators
	for j in 0 .. nominators {
		let balance_factor = if randomize_stake { rng.next_u32() % 255 + 10 } else { 100u32 };
		let (_n_stash, n_controller) = create_stash_controller::<T>(
			u32::max_value() - j,
			balance_factor,
			RewardDestination::Staked,
		)?;

		// Have them randomly validate
		let mut available_validators = validator_choosen.clone();
		let mut selected_validators: Vec<<T::Lookup as StaticLookup>::Source> =
			Vec::with_capacity(edge_per_nominator);

		for _ in 0 .. validators.min(edge_per_nominator as u32) {
			let selected = rng.next_u32() as usize % available_validators.len();
			let validator = available_validators.remove(selected);
			selected_validators.push(validator);
		}
		Staking::<T>::nominate(RawOrigin::Signed(n_controller.clone()).into(), selected_validators)?;
	}

	ValidatorCount::put(validators);

	Ok(validator_choosen)
}


/// Build a _really bad_ but acceptable solution for election. This should always yield a solution
/// which has a less score than the seq-phragmen.
pub fn get_weak_solution<T: Config>(
	do_reduce: bool,
) -> (Vec<ValidatorIndex>, CompactAssignments, ElectionScore, ElectionSize) {
	let mut backing_stake_of: BTreeMap<T::AccountId, BalanceOf<T>> = BTreeMap::new();

	// self stake
	<Validators<T>>::iter().for_each(|(who, _p)| {
		*backing_stake_of.entry(who.clone()).or_insert_with(|| Zero::zero()) +=
			<Module<T>>::slashable_balance_of(&who)
	});

	// elect winners. We chose the.. least backed ones.
	let mut sorted: Vec<T::AccountId> = backing_stake_of.keys().cloned().collect();
	sorted.sort_by_key(|x| backing_stake_of.get(x).unwrap());
	let winners: Vec<T::AccountId> = sorted
		.iter()
		.rev()
		.cloned()
		.take(<Module<T>>::validator_count() as usize)
		.collect();

	let mut staked_assignments: Vec<StakedAssignment<T::AccountId>> = Vec::new();
	// you could at this point start adding some of the nominator's stake, but for now we don't.
	// This solution must be bad.

	// add self support to winners.
	winners.iter().for_each(|w| {
		staked_assignments.push(StakedAssignment {
			who: w.clone(),
			distribution: vec![(
				w.clone(),
				<Module<T>>::slashable_balance_of_vote_weight(
					&w,
					T::Currency::total_issuance(),
				).into(),
			)],
		})
	});

	if do_reduce {
		reduce(&mut staked_assignments);
	}

	// helpers for building the compact
	let snapshot_validators = <Module<T>>::snapshot_validators().unwrap();
	let snapshot_nominators = <Module<T>>::snapshot_nominators().unwrap();

	let nominator_index = |a: &T::AccountId| -> Option<NominatorIndex> {
		snapshot_nominators
			.iter()
			.position(|x| x == a)
			.and_then(|i| <usize as TryInto<NominatorIndex>>::try_into(i).ok())
	};
	let validator_index = |a: &T::AccountId| -> Option<ValidatorIndex> {
		snapshot_validators
			.iter()
			.position(|x| x == a)
			.and_then(|i| <usize as TryInto<ValidatorIndex>>::try_into(i).ok())
	};

	// convert back to ratio assignment. This takes less space.
	let low_accuracy_assignment = assignment_staked_to_ratio_normalized(staked_assignments)
		.expect("Failed to normalize");

	// re-calculate score based on what the chain will decode.
	let score = {
		let staked = assignment_ratio_to_staked::<_, OffchainAccuracy, _>(
			low_accuracy_assignment.clone(),
			<Module<T>>::slashable_balance_of_fn(),
		);

		let support_map =
			to_support_map::<T::AccountId>(winners.as_slice(), staked.as_slice()).unwrap();
		support_map.evaluate()
	};

	// compact encode the assignment.
	let compact = CompactAssignments::from_assignment(
		low_accuracy_assignment,
		nominator_index,
		validator_index,
	)
	.unwrap();

	// winners to index.
	let winners = winners
		.into_iter()
		.map(|w| {
			snapshot_validators
				.iter()
				.position(|v| *v == w)
				.unwrap()
				.try_into()
				.unwrap()
		})
		.collect::<Vec<ValidatorIndex>>();

	let size = ElectionSize {
		validators: snapshot_validators.len() as ValidatorIndex,
		nominators: snapshot_nominators.len() as NominatorIndex,
	};

	(winners, compact, score, size)
}

/// Create a solution for seq-phragmen. This uses the same internal function as used by the offchain
/// worker code.
pub fn get_seq_phragmen_solution<T: Config>(
	do_reduce: bool,
) -> (
	Vec<ValidatorIndex>,
	CompactAssignments,
	ElectionScore,
	ElectionSize,
) {
	let iters = offchain_election::get_balancing_iters::<T>();

	let sp_npos_elections::ElectionResult {
		winners,
		assignments,
	} = <Module<T>>::do_phragmen::<OffchainAccuracy>(iters).unwrap();

	offchain_election::prepare_submission::<T>(
		assignments,
		winners,
		do_reduce,
		T::BlockWeights::get().max_block,
	)
	.unwrap()
}

/// Returns a solution in which only one winner is elected with just a self vote.
pub fn get_single_winner_solution<T: Config>(
	winner: T::AccountId,
) -> Result<
	(
		Vec<ValidatorIndex>,
		CompactAssignments,
		ElectionScore,
		ElectionSize,
	),
	&'static str,
> {
	let snapshot_validators = <Module<T>>::snapshot_validators().unwrap();
	let snapshot_nominators = <Module<T>>::snapshot_nominators().unwrap();

	let val_index = snapshot_validators
		.iter()
		.position(|x| *x == winner)
		.ok_or("not a validator")?;
	let nom_index = snapshot_nominators
		.iter()
		.position(|x| *x == winner)
		.ok_or("not a nominator")?;

	let stake = <Staking<T>>::slashable_balance_of(&winner);
	let stake =
		<T::CurrencyToVote>::to_vote(stake, T::Currency::total_issuance()) as ExtendedBalance;

	let val_index = val_index as ValidatorIndex;
	let nom_index = nom_index as NominatorIndex;

	let winners = vec![val_index];
	let compact = CompactAssignments {
		votes1: vec![(nom_index, val_index)],
		..Default::default()
	};
	let score = [stake, stake, stake * stake];
	let size = ElectionSize {
		validators: snapshot_validators.len() as ValidatorIndex,
		nominators: snapshot_nominators.len() as NominatorIndex,
	};

	Ok((winners, compact, score, size))
}

/// get the active era.
pub fn current_era<T: Config>() -> EraIndex {
	<Module<T>>::current_era().unwrap_or(0)
}

/// initialize the first era.
pub fn init_active_era() {
	ActiveEra::put(ActiveEraInfo {
		index: 1,
		start: None,
	})
}

/// Create random assignments for the given list of winners. Each assignment will have
/// MAX_NOMINATIONS edges.
pub fn create_assignments_for_offchain<T: Config>(
	num_assignments: u32,
	winners: Vec<<T::Lookup as StaticLookup>::Source>,
) -> Result<
	(
		Vec<(T::AccountId, ExtendedBalance)>,
		Vec<Assignment<T::AccountId, OffchainAccuracy>>,
	),
	&'static str
> {
	let ratio = OffchainAccuracy::from_rational_approximation(1, MAX_NOMINATIONS);
	let assignments: Vec<Assignment<T::AccountId, OffchainAccuracy>> = <Nominators<T>>::iter()
		.take(num_assignments as usize)
		.map(|(n, t)| Assignment {
			who: n,
			distribution: t.targets.iter().map(|v| (v.clone(), ratio)).collect(),
		})
		.collect();

	ensure!(assignments.len() == num_assignments as usize, "must bench for `a` assignments");

	let winners = winners.into_iter().map(|v| {
		(<T::Lookup as StaticLookup>::lookup(v).unwrap(), 0)
	}).collect();

	Ok((winners, assignments))
}
