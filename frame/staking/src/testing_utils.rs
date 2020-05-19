// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
use sp_phragmen::*;

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
///
/// `to_nominate` is the number of validator to nominate.
///
/// return the validators choosen to be nominated.
pub fn create_validators_with_nominators_for_era<T: Trait>(
	v: u32,
	n: u32,
	e: usize,
	randomized: bool,
	to_nominate: Option<u32>,
) -> Result<Vec<<T::Lookup as StaticLookup>::Source>, &'static str> {
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

	let to_nominate = to_nominate.unwrap_or(validators.len() as u32) as usize;
	let validator_choosen = validators[0..to_nominate].to_vec();

	// Create n nominators
	for j in 0 .. n {
		let balance_factor = if randomized { rng.next_u32() % 255 + 10 } else { 100u32 };
		let (_n_stash, n_controller) = create_stash_controller::<T>(
			u32::max_value() - j,
			balance_factor,
		)?;

		// Have them randomly validate
		let mut available_validators = validator_choosen.clone();
		let mut selected_validators: Vec<<T::Lookup as StaticLookup>::Source> = Vec::with_capacity(e);
		for _ in 0 .. v.min(e as u32) {
			let selected = rng.next_u32() as usize % available_validators.len();
			let validator = available_validators.remove(selected);
			selected_validators.push(validator);
		}
		Staking::<T>::nominate(RawOrigin::Signed(n_controller.clone()).into(), selected_validators)?;
	}

	ValidatorCount::put(v);

	Ok(validator_choosen)
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
	let stake_of = |who: &T::AccountId| -> VoteWeight {
		<T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(
			<Module<T>>::slashable_balance_of(who),
		)
	};

	// convert back to ratio assignment. This takes less space.
	let low_accuracy_assignment: Vec<Assignment<T::AccountId, OffchainAccuracy>> =
		staked_assignments
			.into_iter()
			.map(|sa| sa.into_assignment(true))
			.collect();

	// re-calculate score based on what the chain will decode.
	let score = {
		let staked = assignment_ratio_to_staked::<_, OffchainAccuracy, _>(
			low_accuracy_assignment.clone(),
			stake_of
		);

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

/// Trims a compact assignment to contain only up to the given count edges.
pub fn trim_compact_to_assignments<T: Trait>(
	mut compact: CompactAssignments,
	winners: Vec<ValidatorIndex>,
	n: usize,
) -> Result<(CompactAssignments, PhragmenScore), &'static str> {
	let snapshot_validators = <Module<T>>::snapshot_validators().unwrap();
	let snapshot_nominators = <Module<T>>::snapshot_nominators().unwrap();

	let validator_at = |index: ValidatorIndex| -> Option<T::AccountId> {
		snapshot_validators.get(index as usize).cloned()
	};
	let nominator_at = |index: NominatorIndex| -> Option<T::AccountId> {
		snapshot_nominators.get(index as usize).cloned()
	};

	let self_votes_len = compact.votes1.iter().filter(|x|
		nominator_at(x.0) == validator_at(x.1)
	).count();

	if n < self_votes_len {
		return Err("cannot have a < w");
	}

	if compact.len() > n {
		let mut index = 0;
		loop {
			match index + 1 {
				1 => if let Some(pos) = compact.votes1.iter().position(|x| nominator_at(x.0) != validator_at(x.1)) {
					compact.votes1.remove(pos);
				}
				2 => if compact.votes2.len() > 0 { let _ = compact.votes2.pop(); }
				3 => if compact.votes3.len() > 0 { let _ = compact.votes3.pop(); }
				4 => if compact.votes4.len() > 0 { let _ = compact.votes4.pop(); }
				5 => if compact.votes5.len() > 0 { let _ = compact.votes5.pop(); }
				6 => if compact.votes6.len() > 0 { let _ = compact.votes6.pop(); }
				7 => if compact.votes7.len() > 0 { let _ = compact.votes7.pop(); }
				8 => if compact.votes8.len() > 0 { let _ = compact.votes8.pop(); }
				9 => if compact.votes9.len() > 0 { let _ = compact.votes9.pop(); }
				10 => if compact.votes10.len() > 0 { let _ = compact.votes10.pop(); }
				11 => if compact.votes11.len() > 0 { let _ = compact.votes11.pop(); }
				12 => if compact.votes12.len() > 0 { let _ = compact.votes12.pop(); }
				13 => if compact.votes13.len() > 0 { let _ = compact.votes13.pop(); }
				14 => if compact.votes14.len() > 0 { let _ = compact.votes14.pop(); }
				15 => if compact.votes15.len() > 0 { let _ = compact.votes15.pop(); }
				16 => if compact.votes16.len() > 0 { let _ = compact.votes16.pop(); }
				_ => unreachable!()
			}

			if compact.len() <= n { break; }
			index = index + 1;
			index = index % 16;
		}
	} else {
		panic!("This solution is already smaller!");
	}

	// now re-compute the score all over again...
	let stake_of = |who: &T::AccountId| -> VoteWeight {
		<T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(
			<Module<T>>::slashable_balance_of(who),
		)
	};

	let score = {
		let winners = winners.into_iter().map(|idx| validator_at(idx).unwrap()).collect::<Vec<_>>();
		let assignments = compact.clone().into_assignment(nominator_at, validator_at).unwrap();
		let staked = assignment_ratio_to_staked::<_, OffchainAccuracy, _>(assignments, stake_of);
		let (support_map, _) = build_support_map::<T::AccountId>(winners.as_slice(), staked.as_slice());
		evaluate_support::<T::AccountId>(&support_map)
	};

	Ok((compact, score))
}

/// initialize the first era.
pub fn init_active_era() {
	ActiveEra::put(ActiveEraInfo {
		index: 1,
		start: None,
	})
}
