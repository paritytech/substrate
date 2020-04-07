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

//! Staking pallet benchmarking.

use super::*;

use rand_chacha::{rand_core::{RngCore, SeedableRng}, ChaChaRng};

use sp_runtime::traits::{Dispatchable, One};
use sp_io::hashing::blake2_256;

use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account};

use crate::Module as Staking;
use frame_system::Module as System;

const SEED: u32 = 0;

fn create_funded_user<T: Trait>(string: &'static str, n: u32) -> T::AccountId {
	let user = account(string, n, SEED);
	let balance = T::Currency::minimum_balance() * 100.into();
	T::Currency::make_free_balance_be(&user, balance);
	user
}

pub fn create_stash_controller<T: Trait>(n: u32) -> Result<(T::AccountId, T::AccountId), &'static str> {
	let stash = create_funded_user::<T>("stash", n);
	let controller = create_funded_user::<T>("controller", n);
	let controller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(controller.clone());
	let reward_destination = RewardDestination::Staked;
	let amount = T::Currency::minimum_balance() * 10.into();
	Staking::<T>::bond(RawOrigin::Signed(stash.clone()).into(), controller_lookup, amount, reward_destination)?;
	return Ok((stash, controller))
}

fn create_validators<T: Trait>(max: u32) -> Result<Vec<<T::Lookup as StaticLookup>::Source>, &'static str> {
	let mut validators: Vec<<T::Lookup as StaticLookup>::Source> = Vec::with_capacity(max as usize);
	for i in 0 .. max {
		let (stash, controller) = create_stash_controller::<T>(i)?;
		let validator_prefs = ValidatorPrefs {
			commission: Perbill::from_percent(50),
		};
		Staking::<T>::validate(RawOrigin::Signed(controller).into(), validator_prefs)?;
		let stash_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(stash);
		validators.push(stash_lookup);
	}
	Ok(validators)
}

// This function generates v validators and n nominators who are randomly nominating up to MAX_NOMINATIONS.
pub fn create_validators_with_nominators_for_era<T: Trait>(v: u32, n: u32) -> Result<(), &'static str> {
	let mut validators: Vec<<T::Lookup as StaticLookup>::Source> = Vec::with_capacity(v as usize);
	let mut rng = ChaChaRng::from_seed(SEED.using_encoded(blake2_256));

	// Create v validators
	for i in 0 .. v {
		let (v_stash, v_controller) = create_stash_controller::<T>(i)?;
		let validator_prefs = ValidatorPrefs {
			commission: Perbill::from_percent(50),
		};
		Staking::<T>::validate(RawOrigin::Signed(v_controller.clone()).into(), validator_prefs)?;
		let stash_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(v_stash.clone());
		validators.push(stash_lookup.clone());
	}

	// Create n nominators
	for j in 0 .. n {
		let (_n_stash, n_controller) = create_stash_controller::<T>(u32::max_value() - j)?;

		// Have them randomly validate
		let mut available_validators = validators.clone();
		let mut selected_validators: Vec<<T::Lookup as StaticLookup>::Source> = Vec::with_capacity(MAX_NOMINATIONS);
		for _ in 0 .. v.min(MAX_NOMINATIONS as u32) {
			let selected = rng.next_u32() as usize % available_validators.len();
			let validator = available_validators.remove(selected);
			selected_validators.push(validator);
		}
		Staking::<T>::nominate(RawOrigin::Signed(n_controller.clone()).into(), selected_validators)?;
	}

	ValidatorCount::put(v);

	Ok(())
}

// This function generates one validator being nominated by n nominators, and returns
//the validator stash account. It also starts an era and creates pending payouts.
pub fn create_validator_with_nominators<T: Trait>(n: u32, upper_bound: u32) -> Result<T::AccountId, &'static str> {
	let mut points_total = 0;
	let mut points_individual = Vec::new();

	MinimumValidatorCount::put(0);

	let (v_stash, v_controller) = create_stash_controller::<T>(0)?;
	let validator_prefs = ValidatorPrefs {
		commission: Perbill::from_percent(50),
	};
	Staking::<T>::validate(RawOrigin::Signed(v_controller.clone()).into(), validator_prefs)?;
	let stash_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(v_stash.clone());

	points_total += 10;
	points_individual.push((v_stash.clone(), 10));

	// Give the validator n nominators, but keep total users in the system the same.
	for i in 0 .. upper_bound {
		let (_n_stash, n_controller) = create_stash_controller::<T>(u32::max_value() - i)?;
		if i < n {
			Staking::<T>::nominate(RawOrigin::Signed(n_controller.clone()).into(), vec![stash_lookup.clone()])?;
		}
	}

	ValidatorCount::put(1);

	// Start a new Era
	let new_validators = Staking::<T>::new_era(SessionIndex::one()).unwrap();

	assert!(new_validators.len() == 1);

	// Give Era Points
	let reward = EraRewardPoints::<T::AccountId> {
		total: points_total,
		individual: points_individual.into_iter().collect(),
	};

	let current_era = CurrentEra::get().unwrap();
	ErasRewardPoints::<T>::insert(current_era, reward);

	// Create reward pool
	let total_payout = T::Currency::minimum_balance() * 1000.into();
	<ErasValidatorReward<T>>::insert(current_era, total_payout);

	Ok(v_stash)
}

benchmarks! {
	_{
		// User account seed
		let u in 0 .. 1000 => ();
	}

	bond {
		let u in ...;
		let stash = create_funded_user::<T>("stash",u);
		let controller = create_funded_user::<T>("controller", u);
		let controller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(controller);
		let reward_destination = RewardDestination::Staked;
		let amount = T::Currency::minimum_balance() * 10.into();
	}: _(RawOrigin::Signed(stash), controller_lookup, amount, reward_destination)

	bond_extra {
		let u in ...;
		let (stash, _) = create_stash_controller::<T>(u)?;
		let max_additional = T::Currency::minimum_balance() * 10.into();
	}: _(RawOrigin::Signed(stash), max_additional)

	unbond {
		let u in ...;
		let (_, controller) = create_stash_controller::<T>(u)?;
		let amount = T::Currency::minimum_balance() * 10.into();
	}: _(RawOrigin::Signed(controller), amount)

	// Worst case scenario, everything is removed after the bonding duration
	withdraw_unbonded {
		let u in ...;
		let (stash, controller) = create_stash_controller::<T>(u)?;
		let amount = T::Currency::minimum_balance() * 10.into();
		Staking::<T>::unbond(RawOrigin::Signed(controller.clone()).into(), amount)?;
		let current_block = System::<T>::block_number();
		// let unbond_block = current_block + T::BondingDuration::get().into() + 10.into();
		// System::<T>::set_block_number(unbond_block);
	}: _(RawOrigin::Signed(controller))

	validate {
		let u in ...;
		let (_, controller) = create_stash_controller::<T>(u)?;
		let prefs = ValidatorPrefs::default();
	}: _(RawOrigin::Signed(controller), prefs)

	// Worst case scenario, MAX_NOMINATIONS
	nominate {
		let n in 1 .. MAX_NOMINATIONS as u32;
		let (_, controller) = create_stash_controller::<T>(n + 1)?;
		let validators = create_validators::<T>(n)?;
	}: _(RawOrigin::Signed(controller), validators)

	chill {
		let u in ...;
		let (_, controller) = create_stash_controller::<T>(u)?;
	}: _(RawOrigin::Signed(controller))

	set_payee {
		let u in ...;
		let (_, controller) = create_stash_controller::<T>(u)?;
	}: _(RawOrigin::Signed(controller), RewardDestination::Controller)

	set_controller {
		let u in ...;
		let (stash, _) = create_stash_controller::<T>(u)?;
		let new_controller = create_funded_user::<T>("new_controller", u);
		let new_controller_lookup = T::Lookup::unlookup(new_controller);
	}: _(RawOrigin::Signed(stash), new_controller_lookup)

	set_validator_count {
		let c in 0 .. 1000;
	}: _(RawOrigin::Root, c)

	force_no_eras { let i in 0 .. 1; }: _(RawOrigin::Root)

	force_new_era {let i in 0 .. 1; }: _(RawOrigin::Root)

	force_new_era_always { let i in 0 .. 1; }: _(RawOrigin::Root)

	// Worst case scenario, the list of invulnerables is very long.
	set_invulnerables {
		let v in 0 .. 1000;
		let mut invulnerables = Vec::new();
		for i in 0 .. v {
			invulnerables.push(account("invulnerable", i, SEED));
		}
	}: _(RawOrigin::Root, invulnerables)

	force_unstake {
		let u in ...;
		let (stash, _) = create_stash_controller::<T>(u)?;
	}: _(RawOrigin::Root, stash)

	cancel_deferred_slash {
		let s in 1 .. 1000;
		let mut unapplied_slashes = Vec::new();
		let era = EraIndex::one();
		for _ in 0 .. 1000 {
			unapplied_slashes.push(UnappliedSlash::<T::AccountId, BalanceOf<T>>::default());
		}
		UnappliedSlashes::<T>::insert(era, &unapplied_slashes);

		let slash_indices: Vec<u32> = (0 .. s).collect();
	}: _(RawOrigin::Root, era, slash_indices)

	payout_stakers {
		let n in 1 .. MAX_NOMINATIONS as u32;
		let validator = create_validator_with_nominators::<T>(n, MAX_NOMINATIONS as u32)?;
		let current_era = CurrentEra::get().unwrap();
		let caller = account("caller", n, SEED);
	}: _(RawOrigin::Signed(caller), validator, current_era)

	rebond {
		let l in 1 .. 1000;
		let (_, controller) = create_stash_controller::<T>(u)?;
		let mut staking_ledger = Ledger::<T>::get(controller.clone()).unwrap();
		let unlock_chunk = UnlockChunk::<BalanceOf<T>> {
			value: 1.into(),
			era: EraIndex::zero(),
		};
		for _ in 0 .. l {
			staking_ledger.unlocking.push(unlock_chunk.clone())
		}
		Ledger::<T>::insert(controller.clone(), staking_ledger);
	}: _(RawOrigin::Signed(controller), (l + 100).into())

	set_history_depth {
		let e in 1 .. 100;
		HistoryDepth::put(e);
		CurrentEra::put(e);
		for i in 0 .. e {
			<ErasStakers<T>>::insert(i, T::AccountId::default(), Exposure::<T::AccountId, BalanceOf<T>>::default());
			<ErasStakersClipped<T>>::insert(i, T::AccountId::default(), Exposure::<T::AccountId, BalanceOf<T>>::default());
			<ErasValidatorPrefs<T>>::insert(i, T::AccountId::default(), ValidatorPrefs::default());
			<ErasValidatorReward<T>>::insert(i, BalanceOf::<T>::one());
			<ErasRewardPoints<T>>::insert(i, EraRewardPoints::<T::AccountId>::default());
			<ErasTotalStake<T>>::insert(i, BalanceOf::<T>::one());
			ErasStartSessionIndex::insert(i, i);
		}
	}: _(RawOrigin::Root, EraIndex::zero())

	reap_stash {
		let u in 1 .. 1000;
		let (stash, controller) = create_stash_controller::<T>(u)?;
		T::Currency::make_free_balance_be(&stash, 0.into());
	}: _(RawOrigin::Signed(controller), stash)

	new_era {
		let v in 1 .. 10;
		let n in 1 .. 100;
		MinimumValidatorCount::put(0);
		create_validators_with_nominators_for_era::<T>(v, n)?;
		let session_index = SessionIndex::one();
	}: {
		let validators = Staking::<T>::new_era(session_index).ok_or("`new_era` failed")?;
		assert!(validators.len() == v as usize);
	}

	do_slash {
		let l in 1 .. 1000;
		let (stash, controller) = create_stash_controller::<T>(0)?;
		let mut staking_ledger = Ledger::<T>::get(controller.clone()).unwrap();
		let unlock_chunk = UnlockChunk::<BalanceOf<T>> {
			value: 1.into(),
			era: EraIndex::zero(),
		};
		for _ in 0 .. l {
			staking_ledger.unlocking.push(unlock_chunk.clone())
		}
		Ledger::<T>::insert(controller.clone(), staking_ledger.clone());
		let slash_amount = T::Currency::minimum_balance() * 10.into();
	}: {
		crate::slashing::do_slash::<T>(
			&stash,
			slash_amount,
			&mut BalanceOf::<T>::zero(),
			&mut NegativeImbalanceOf::<T>::zero()
		);
	}

	payout_all {
		let v in 1 .. 10;
		let n in 1 .. 100;
		MinimumValidatorCount::put(0);
		create_validators_with_nominators_for_era::<T>(v, n)?;
		// Start a new Era
		let new_validators = Staking::<T>::new_era(SessionIndex::one()).unwrap();
		assert!(new_validators.len() == v as usize);

		let current_era = CurrentEra::get().unwrap();
		let mut points_total = 0;
		let mut points_individual = Vec::new();
		let mut payout_calls = Vec::new();

		for validator in new_validators.iter() {
			points_total += 10;
			points_individual.push((validator.clone(), 10));
			payout_calls.push(Call::<T>::payout_stakers(validator.clone(), current_era))
		}

		// Give Era Points
		let reward = EraRewardPoints::<T::AccountId> {
			total: points_total,
			individual: points_individual.into_iter().collect(),
		};

		ErasRewardPoints::<T>::insert(current_era, reward);

		// Create reward pool
		let total_payout = T::Currency::minimum_balance() * 1000.into();
		<ErasValidatorReward<T>>::insert(current_era, total_payout);

		let caller: T::AccountId = account("caller", 0, SEED);
	}: {
		for call in payout_calls {
			call.dispatch(RawOrigin::Signed(caller.clone()).into())?;
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mock::{ExtBuilder, Test, Balances, Staking, Origin};
	use frame_support::assert_ok;

	#[test]
	fn create_validators_with_nominators_for_era_works() {
		ExtBuilder::default().has_stakers(false).build().execute_with(|| {
			let v = 10;
			let n = 100;

			create_validators_with_nominators_for_era::<Test>(v,n).unwrap();

			let count_validators = Validators::<Test>::iter().count();
			let count_nominators = Nominators::<Test>::iter().count();

			assert_eq!(count_validators, v as usize);
			assert_eq!(count_nominators, n as usize);
		});
	}

	#[test]
	fn create_validator_with_nominators_works() {
		ExtBuilder::default().has_stakers(false).build().execute_with(|| {
			let n = 10;

			let validator_stash = create_validator_with_nominators::<Test>(
				n,
				MAX_NOMINATIONS as u32,
			).unwrap();

			let current_era = CurrentEra::get().unwrap();

			let original_free_balance = Balances::free_balance(&validator_stash);
			assert_ok!(Staking::payout_stakers(Origin::signed(1337), validator_stash, current_era));
			let new_free_balance = Balances::free_balance(&validator_stash);

			assert!(original_free_balance < new_free_balance);
		});
	}

	#[test]
	fn test_payout_all() {
		ExtBuilder::default().has_stakers(false).build().execute_with(|| {
			let v = 10;
			let n = 100;

			let selected_benchmark = SelectedBenchmark::payout_all;
			let c = vec![(frame_benchmarking::BenchmarkParameter::v, v), (frame_benchmarking::BenchmarkParameter::n, n)];
			let closure_to_benchmark =
				<SelectedBenchmark as frame_benchmarking::BenchmarkingSetup<Test>>::instance(
					&selected_benchmark,
					&c
				).unwrap();

			assert_ok!(closure_to_benchmark());
		});
	}

	#[test]
	fn test_benchmarks() {
		ExtBuilder::default().has_stakers(false).build().execute_with(|| {
			assert_ok!(test_benchmark_bond::<Test>());
			assert_ok!(test_benchmark_bond_extra::<Test>());
			assert_ok!(test_benchmark_unbond::<Test>());
			assert_ok!(test_benchmark_withdraw_unbonded::<Test>());
			assert_ok!(test_benchmark_validate::<Test>());
			assert_ok!(test_benchmark_nominate::<Test>());
			assert_ok!(test_benchmark_chill::<Test>());
			assert_ok!(test_benchmark_set_payee::<Test>());
			assert_ok!(test_benchmark_set_controller::<Test>());
			assert_ok!(test_benchmark_set_validator_count::<Test>());
			assert_ok!(test_benchmark_force_no_eras::<Test>());
			assert_ok!(test_benchmark_force_new_era::<Test>());
			assert_ok!(test_benchmark_force_new_era_always::<Test>());
			assert_ok!(test_benchmark_set_invulnerables::<Test>());
			assert_ok!(test_benchmark_force_unstake::<Test>());
			assert_ok!(test_benchmark_cancel_deferred_slash::<Test>());
			assert_ok!(test_benchmark_payout_stakers::<Test>());
			assert_ok!(test_benchmark_rebond::<Test>());
			assert_ok!(test_benchmark_set_history_depth::<Test>());
			assert_ok!(test_benchmark_reap_stash::<Test>());
			assert_ok!(test_benchmark_new_era::<Test>());
			assert_ok!(test_benchmark_do_slash::<Test>());
			assert_ok!(test_benchmark_payout_all::<Test>());
		});
	}
}
