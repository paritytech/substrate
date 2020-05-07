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
//! build. Just don't do it.

use crate::*;
use codec::{Decode, Encode};
use frame_support::assert_ok;
use frame_system::RawOrigin;
use pallet_indices::address::Address;
use rand::Rng;
use sp_core::hashing::blake2_256;
use sp_phragmen::{
	build_support_map, evaluate_support, reduce, Assignment, PhragmenScore, StakedAssignment,
};

const CTRL_PREFIX: u32 = 1000;
const NOMINATOR_PREFIX: u32 = 1_000_000;

/// A dummy suer.
pub const USER: u32 = 999_999_999;

/// Address type of the `T`
pub type AddressOf<T> = Address<<T as frame_system::Trait>::AccountId, u32>;

/// Random number in the range `[a, b]`.
pub fn random(a: u32, b: u32) -> u32 {
	rand::thread_rng().gen_range(a, b)
}

/// Set the desired validator count, with related storage items.
pub fn set_validator_count<T: Trait>(to_elect: u32) {
	ValidatorCount::put(to_elect);
	MinimumValidatorCount::put(to_elect / 2);
	<EraElectionStatus<T>>::put(ElectionStatus::Closed);
}

/// Build an account with the given index.
pub fn account<T: Trait>(index: u32) -> T::AccountId {
	let entropy = (b"benchmark/staking", index).using_encoded(blake2_256);
	T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
}

/// Build an address given Index
pub fn address<T: Trait>(index: u32) -> AddressOf<T> {
	pallet_indices::address::Address::Id(account::<T>(index))
}

/// Generate signed origin from `who`.
pub fn signed<T: Trait>(who: T::AccountId) -> T::Origin {
	RawOrigin::Signed(who).into()
}

/// Generate signed origin from `index`.
pub fn signed_account<T: Trait>(index: u32) -> T::Origin {
	signed::<T>(account::<T>(index))
}

/// Bond a validator.
pub fn bond_validator<T: Trait>(stash: T::AccountId, ctrl: u32, val: BalanceOf<T>)
where
	T::Lookup: StaticLookup<Source = AddressOf<T>>,
{
	let _ = T::Currency::make_free_balance_be(&stash, val);
	assert_ok!(<Module<T>>::bond(
		signed::<T>(stash),
		address::<T>(ctrl),
		val,
		RewardDestination::Controller
	));
	assert_ok!(<Module<T>>::validate(
		signed_account::<T>(ctrl),
		ValidatorPrefs::default()
	));
}

pub fn bond_nominator<T: Trait>(
	stash: T::AccountId,
	ctrl: u32,
	val: BalanceOf<T>,
	target: Vec<AddressOf<T>>,
) where
	T::Lookup: StaticLookup<Source = AddressOf<T>>,
{
	let _ = T::Currency::make_free_balance_be(&stash, val);
	assert_ok!(<Module<T>>::bond(
		signed::<T>(stash),
		address::<T>(ctrl),
		val,
		RewardDestination::Controller
	));
	assert_ok!(<Module<T>>::nominate(signed_account::<T>(ctrl), target));
}

/// Bond `nun_validators` validators and `num_nominator` nominators with `edge_per_voter` random
/// votes per nominator.
pub fn setup_chain_stakers<T: Trait>(num_validators: u32, num_voters: u32, edge_per_voter: u32)
where
	T::Lookup: StaticLookup<Source = AddressOf<T>>,
{
	(0..num_validators).for_each(|i| {
		bond_validator::<T>(
			account::<T>(i),
			i + CTRL_PREFIX,
			<BalanceOf<T>>::from(random(1, 1000)) * T::Currency::minimum_balance(),
		);
	});

	(0..num_voters).for_each(|i| {
		let mut targets: Vec<AddressOf<T>> = Vec::with_capacity(edge_per_voter as usize);
		let mut all_targets = (0..num_validators)
			.map(|t| address::<T>(t))
			.collect::<Vec<_>>();
		assert!(num_validators >= edge_per_voter);
		(0..edge_per_voter).for_each(|_| {
			let target = all_targets.remove(random(0, all_targets.len() as u32 - 1) as usize);
			targets.push(target);
		});
		bond_nominator::<T>(
			account::<T>(i + NOMINATOR_PREFIX),
			i + NOMINATOR_PREFIX + CTRL_PREFIX,
			<BalanceOf<T>>::from(random(1, 1000)) * T::Currency::minimum_balance(),
			targets,
		);
	});

	<Module<T>>::create_stakers_snapshot();
}

/// Build a _really bad_ but acceptable solution for election. This should always yield a solution
/// which has a less score than the seq-phragmen.
pub fn get_weak_solution<T: Trait>(
	do_reduce: bool,
) -> (Vec<ValidatorIndex>, CompactAssignments, PhragmenScore) {
	let mut backing_stake_of: BTreeMap<T::AccountId, BalanceOf<T>> = BTreeMap::new();

	// self stake
	<Validators<T>>::iter().for_each(|(who, _p)| {
		*backing_stake_of.entry(who.clone()).or_insert(Zero::zero()) +=
			<Module<T>>::slashable_balance_of(&who)
	});

	// add nominator stuff
	<Nominators<T>>::iter().for_each(|(who, nomination)| {
		nomination.targets.into_iter().for_each(|v| {
			*backing_stake_of.entry(v).or_insert(Zero::zero()) +=
				<Module<T>>::slashable_balance_of(&who)
		})
	});

	// elect winners
	let mut sorted: Vec<T::AccountId> = backing_stake_of.keys().cloned().collect();
	sorted.sort_by_key(|x| backing_stake_of.get(x).unwrap());
	let winners: Vec<T::AccountId> = sorted
		.iter()
		.cloned()
		.take(<Module<T>>::validator_count() as usize)
		.collect();

	let mut staked_assignments: Vec<StakedAssignment<T::AccountId>> = Vec::new();
	<Nominators<T>>::iter().for_each(|(who, nomination)| {
		let mut dist: Vec<(T::AccountId, ExtendedBalance)> = Vec::new();
		nomination.targets.into_iter().for_each(|v| {
			if winners.iter().find(|&w| *w == v).is_some() {
				dist.push((v, ExtendedBalance::zero()));
			}
		});

		if dist.len() == 0 {
			return;
		}

		// assign real stakes. just split the stake.
		let stake = <T::CurrencyToVote as Convert<BalanceOf<T>, u64>>::convert(
			<Module<T>>::slashable_balance_of(&who),
		) as ExtendedBalance;

		let mut sum: ExtendedBalance = Zero::zero();
		let dist_len = dist.len() as ExtendedBalance;

		// assign main portion
		// only take the first half into account. This should highly imbalance stuff, which is good.
		dist.iter_mut()
			.take(if dist_len > 1 {
				(dist_len as usize) / 2
			} else {
				1
			})
			.for_each(|(_, w)| {
				let partial = stake / dist_len;
				*w = partial;
				sum += partial;
			});

		// assign the leftover to last.
		let leftover = stake - sum;
		let last = dist.last_mut().unwrap();
		last.1 += leftover;

		staked_assignments.push(StakedAssignment {
			who,
			distribution: dist,
		});
	});

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

	(winners, compact, score)
}

/// Create a solution for seq-phragmen. This uses the same internal function as used by the offchain
/// worker code.
pub fn get_seq_phragmen_solution<T: Trait>(
	do_reduce: bool,
) -> (Vec<ValidatorIndex>, CompactAssignments, PhragmenScore) {
	let sp_phragmen::PhragmenResult {
		winners,
		assignments,
	} = <Module<T>>::do_phragmen::<OffchainAccuracy>().unwrap();

	offchain_election::prepare_submission::<T>(assignments, winners, do_reduce).unwrap()
}

/// Remove all validator, nominators, votes and exposures.
pub fn clean<T: Trait>(era: EraIndex)
	where
		<T as frame_system::Trait>::AccountId: codec::EncodeLike<u32>,
		u32: codec::EncodeLike<T::AccountId>,
{
	<Validators<T>>::iter().for_each(|(k, _)| {
		let ctrl = <Module<T>>::bonded(&k).unwrap();
		<Bonded<T>>::remove(&k);
		<Validators<T>>::remove(&k);
		<Ledger<T>>::remove(&ctrl);
		<ErasStakers<T>>::remove(k, era);
	});
	<Nominators<T>>::iter().for_each(|(k, _)| <Nominators<T>>::remove(k));
	<Ledger<T>>::remove_all();
	<Bonded<T>>::remove_all();
	<QueuedElected<T>>::kill();
	QueuedScore::kill();
}

/// get the active era.
pub fn active_era<T: Trait>() -> EraIndex {
	<Module<T>>::active_era().unwrap().index
}

/// initialize the first era.
pub fn init_active_era() {
	ActiveEra::put(ActiveEraInfo {
		index: 1,
		start: None,
	})
}
