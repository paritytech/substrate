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

//! Testing utils for staking. Needs the `testing-utils` feature to be enabled.
//!
//! Note that these helpers should NOT be used with the actual crate tests, but are rather designed
//! for when the module is being externally tested (i.e. fuzzing, benchmarking, e2e tests). Enabling
//! this feature in the current crate's Cargo.toml will leak all of this into a normal release
//! build. Just don't do it. TODO: update this.

use crate::*;
use crate::Module as Staking;
use frame_benchmarking::{account};
use frame_system::RawOrigin;
use sp_io::hashing::blake2_256;
use rand_chacha::{rand_core::{RngCore, SeedableRng}, ChaChaRng};
use sp_phragmen::{
	build_support_map, evaluate_support, reduce, Assignment, PhragmenScore, StakedAssignment,
};

const SEED: u32 = 0;

/// Grab a funded user.
pub fn create_funded_user<T: Trait>(string: &'static str, n: u32, balance_factor: u32) -> T::AccountId {
	let user = account(string, n, SEED);
	let balance = T::Currency::minimum_balance() * balance_factor.into();
	T::Currency::make_free_balance_be(&user, balance);
	// ensure T::CurrencyToVote will work correctly.
	T::Currency::issue(balance);
	user
}

/// Create a stash and controller pair.
pub fn create_stash_controller<T: Trait>(n: u32, balance_factor: u32)
	-> Result<(T::AccountId, T::AccountId), &'static str>
{
	let stash = create_funded_user::<T>("stash", n, balance_factor);
	let controller = create_funded_user::<T>("controller", n, balance_factor);
	let controller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(controller.clone());
	let reward_destination = RewardDestination::Staked;
	let amount = T::Currency::minimum_balance() * (balance_factor / 10).max(1).into();
	Staking::<T>::bond(RawOrigin::Signed(stash.clone()).into(), controller_lookup, amount, reward_destination)?;
	return Ok((stash, controller))
}

/// create `max` validators.
pub fn create_validators<T: Trait>(max: u32, balance_factor: u32) -> Result<Vec<<T::Lookup as StaticLookup>::Source>, &'static str> {
	let mut validators: Vec<<T::Lookup as StaticLookup>::Source> = Vec::with_capacity(max as usize);
	for i in 0 .. max {
		let (stash, controller) = create_stash_controller::<T>(i, balance_factor)?;
		let validator_prefs = ValidatorPrefs {
			commission: Perbill::from_percent(50),
		};
		Staking::<T>::validate(RawOrigin::Signed(controller).into(), validator_prefs)?;
		let stash_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(stash);
		validators.push(stash_lookup);
	}
	Ok(validators)
}

/// This function generates v validators and n nominators who are randomly nominating
/// `e` random validators.
pub fn create_validators_with_nominators_for_era<T: Trait>(
	v: u32,
	n: u32,
	e: usize,
	randomized: bool,
) -> Result<(), &'static str> {
	let mut validators: Vec<<T::Lookup as StaticLookup>::Source> = Vec::with_capacity(v as usize);
	let mut rng = ChaChaRng::from_seed(SEED.using_encoded(blake2_256));

	// Create v validators
	for i in 0 .. v {
		let balance_factor = if randomized { rng.next_u32() % 255 + 10 } else { 100u32 };
		let (v_stash, v_controller) = create_stash_controller::<T>(i, balance_factor)?;
		let validator_prefs = ValidatorPrefs {
			commission: Perbill::from_percent(50),
		};
		Staking::<T>::validate(RawOrigin::Signed(v_controller.clone()).into(), validator_prefs)?;
		let stash_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(v_stash.clone());
		validators.push(stash_lookup.clone());
	}

	// Create n nominators
	for j in 0 .. n {
		let balance_factor = if randomized { rng.next_u32() % 255 + 10 } else { 100u32 };
		let (_n_stash, n_controller) = create_stash_controller::<T>(
			u32::max_value() - j,
			balance_factor,
		)?;

		// Have them randomly validate
		let mut available_validators = validators.clone();
		let mut selected_validators: Vec<<T::Lookup as StaticLookup>::Source> = Vec::with_capacity(e);
		for _ in 0 .. v.min(e as u32) {
			let selected = rng.next_u32() as usize % available_validators.len();
			let validator = available_validators.remove(selected);
			selected_validators.push(validator);
		}
		Staking::<T>::nominate(RawOrigin::Signed(n_controller.clone()).into(), selected_validators)?;
	}

	ValidatorCount::put(v);

	Ok(())
}


/// Build a _really bad_ but acceptable solution for election. This should always yield a solution
/// which has a less score than the seq-phragmen.
pub fn get_weak_solution<T: Trait>(
	do_reduce: bool,
) -> (Vec<ValidatorIndex>, CompactAssignments, PhragmenScore, ElectionSize) {
	let mut backing_stake_of: BTreeMap<T::AccountId, BalanceOf<T>> = BTreeMap::new();

	// self stake
	<Validators<T>>::iter().for_each(|(who, _p)| {
		*backing_stake_of.entry(who.clone()).or_insert(Zero::zero()) +=
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
				<T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(
					<Module<T>>::slashable_balance_of(&w),
				) as ExtendedBalance,
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
	let stake_of = |who: &T::AccountId| -> ExtendedBalance {
		<T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(
			<Module<T>>::slashable_balance_of(who),
		) as ExtendedBalance
	};

	// convert back to ratio assignment. This takes less space.
	let low_accuracy_assignment: Vec<Assignment<T::AccountId, OffchainAccuracy>> =
		staked_assignments
			.into_iter()
			.map(|sa| sa.into_assignment(true))
			.collect();

	// re-calculate score based on what the chain will decode.
	let score = {
		let staked: Vec<StakedAssignment<T::AccountId>> = low_accuracy_assignment
			.iter()
			.map(|a| {
				let stake = stake_of(&a.who);
				a.clone().into_staked(stake, true)
			})
			.collect();

		let (support_map, _) =
			build_support_map::<T::AccountId>(winners.as_slice(), staked.as_slice());
		evaluate_support::<T::AccountId>(&support_map)
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
pub fn get_seq_phragmen_solution<T: Trait>(
	do_reduce: bool,
) -> (Vec<ValidatorIndex>, CompactAssignments, PhragmenScore, ElectionSize) {
	let sp_phragmen::PhragmenResult {
		winners,
		assignments,
	} = <Module<T>>::do_phragmen::<OffchainAccuracy>().unwrap();

	offchain_election::prepare_submission::<T>(assignments, winners, do_reduce).unwrap()
}

/// get the active era.
pub fn current_era<T: Trait>() -> EraIndex {
	<Module<T>>::current_era().unwrap_or(0)
}

/// initialize the first era.
pub fn init_active_era() {
	ActiveEra::put(ActiveEraInfo {
		index: 1,
		start: None,
	})
}
