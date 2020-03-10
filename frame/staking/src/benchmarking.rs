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

use frame_system::RawOrigin;
use frame_benchmarking::{benchmarks, account};
use sp_runtime::traits::One;

use crate::Module as Staking;
use frame_system::Module as System;

const SEED: u32 = 0;
// TODO: We should make this configurable
const MAX_NOMINATIONS: u32 = 16;

fn create_funded_user<T: Trait>(string: &'static str, n: u32) -> T::AccountId {
    let user = account(string, n, SEED);
    let balance = T::Currency::minimum_balance() * 100.into();
    T::Currency::make_free_balance_be(&user, balance);
    return user
}

fn create_stash_controller<T: Trait>(n: u32) -> Result<(T::AccountId, T::AccountId), &'static str> {
    let stash = create_funded_user::<T>("stash", n);
    let controller = create_funded_user::<T>("controller", n);
    let controller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(controller.clone());
    let reward_destination = RewardDestination::Staked;
    let amount = T::Currency::minimum_balance() * 10.into();
    Staking::<T>::bond(RawOrigin::Signed(stash.clone()).into(), controller_lookup, amount, reward_destination)?;
    return Ok((stash, controller))
}

fn create_stash_controller2<T: Trait>(n: u32) -> Result<(T::AccountId, T::AccountId), &'static str> {
    let stash = create_funded_user::<T>("stash2", n);
    let controller = create_funded_user::<T>("controller2", n);
    let controller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(controller.clone());
    let reward_destination = RewardDestination::Staked;
    let amount = T::Currency::minimum_balance() * 10.into();
    Staking::<T>::bond(RawOrigin::Signed(stash.clone()).into(), controller_lookup, amount, reward_destination)?;
    return Ok((stash, controller))
}

fn create_validators<T: Trait>(max: u32) -> Result<Vec<<T::Lookup as StaticLookup>::Source>, &'static str> {
    let mut validators: Vec<<T::Lookup as StaticLookup>::Source> = Vec::new();
    for i in 0 .. max {
        let (stash, controller) = create_stash_controller::<T>(i)?;
        let validator_prefs = ValidatorPrefs {
            commission: Perbill::from_percent(50),
        };
        Staking::<T>::validate(RawOrigin::Signed(controller).into(), validator_prefs)?;
        let stash_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(stash);
        validators.push(stash_lookup);
    }
    return Ok(validators)
}

// This function generates v validators each of whom have n nominators and payouts
// for the current era.
pub fn create_validators_with_nominators<T: Trait>(v: u32, n: u32) -> Result<Vec<T::AccountId>, &'static str> {
    let mut validators: Vec<T::AccountId> = Vec::new();
    let mut points_total = 0;
    let mut points_individual = Vec::new();

    // Create v validators
    for i in 0 .. v {
        let (v_stash, v_controller) = create_stash_controller::<T>(i)?;
        let validator_prefs = ValidatorPrefs {
            commission: Perbill::from_percent(50),
        };
        Staking::<T>::validate(RawOrigin::Signed(v_controller.clone()).into(), validator_prefs)?;
        let stash_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(v_stash.clone());
        validators.push(v_controller.clone());

        points_total += 10;
        points_individual.push((v_stash, 10));

        // Give each validator n nominators
        for j in 0 .. n {
            let (_n_stash, n_controller) = create_stash_controller2::<T>(n * i + j)?;
            Staking::<T>::nominate(RawOrigin::Signed(n_controller.clone()).into(), vec![stash_lookup.clone()])?;
        }
    }
    
    ValidatorCount::put(v);
    
    // Start a new Era
    let new_validators = Staking::<T>::new_era(SessionIndex::one()).unwrap();

    assert!(new_validators.len() == v as usize);

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

    Ok(validators)
}

// This function generates one validator being nominated by n nominators
pub fn create_validator_with_nominators<T: Trait>(n: u32, upper_bound: u32) -> Result<T::AccountId, &'static str> {
    let mut validators: Vec<T::AccountId> = Vec::new();
    let mut points_total = 0;
    let mut points_individual = Vec::new();

    // Create v validators
    for i in 0 .. DEFAULT_MINIMUM_VALIDATOR_COUNT {
        let (v_stash, v_controller) = create_stash_controller::<T>(i)?;
        let validator_prefs = ValidatorPrefs {
            commission: Perbill::from_percent(50),
        };
        Staking::<T>::validate(RawOrigin::Signed(v_controller.clone()).into(), validator_prefs)?;
        let stash_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(v_stash.clone());
        validators.push(v_controller.clone());

        points_total += 10;
        points_individual.push((v_stash, 10));

        // Give each validator n nominators, but keep total users in the system the same.
        for j in 0 .. upper_bound {
            let (_n_stash, n_controller) = create_stash_controller2::<T>(upper_bound * i + j)?;
            if j < n {
                Staking::<T>::nominate(RawOrigin::Signed(n_controller.clone()).into(), vec![stash_lookup.clone()])?;
            }
        }
    }
    
    ValidatorCount::put(DEFAULT_MINIMUM_VALIDATOR_COUNT);
    
    // Start a new Era
    let new_validators = Staking::<T>::new_era(SessionIndex::one()).unwrap();

    assert!(new_validators.len() == DEFAULT_MINIMUM_VALIDATOR_COUNT as usize);

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

    Ok(validators[0].clone())
}

// This function generates one nominator nominating v validators
pub fn create_nominator_with_validators<T: Trait>(v: u32) -> Result<(T::AccountId, Vec<T::AccountId>), &'static str> {
    let mut validators = Vec::new();
    let mut points_total = 0;
    let mut points_individual = Vec::new();

    // Create v validators
    let mut validator_lookups = Vec::new();
    for i in 0 .. v.max(DEFAULT_MINIMUM_VALIDATOR_COUNT) {
        let (v_stash, v_controller) = create_stash_controller::<T>(i)?;
        let validator_prefs = ValidatorPrefs {
            commission: Perbill::from_percent(50),
        };
        Staking::<T>::validate(RawOrigin::Signed(v_controller.clone()).into(), validator_prefs)?;
        let stash_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(v_stash.clone());

        points_total += 10;
        points_individual.push((v_stash.clone(), 10));
        validator_lookups.push(stash_lookup);
        // Add to the list if it is less than the number we want the nominator to have
        if validators.len() < v as usize {
            validators.push(v_stash.clone())
        }
    }

    // Create a nominator
    let (_n_stash, n_controller) = create_stash_controller2::<T>(0)?;
    Staking::<T>::nominate(RawOrigin::Signed(n_controller.clone()).into(), validator_lookups)?;
    
    ValidatorCount::put(v);
    
    // Start a new Era
    let new_validators = Staking::<T>::new_era(SessionIndex::one()).unwrap();

    assert!(new_validators.len() == v as usize);

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

    Ok((n_controller, validators))
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
        let n in 1 .. MAX_NOMINATIONS;
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

    force_no_eras { }: _(RawOrigin::Root)

    force_new_era { }: _(RawOrigin::Root)

    force_new_era_always { }: _(RawOrigin::Root)

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

    // cancel_deferred_slash {

    // }: _()

    payout_validator {
        let n in 1 .. MAX_NOMINATIONS;
        let validator = create_validator_with_nominators::<T>(n, MAX_NOMINATIONS)?;
        let current_era = CurrentEra::get().unwrap();
     }: _(RawOrigin::Signed(validator), current_era)

     payout_nominator {
        let v in 0 .. MAX_NOMINATIONS;
        let (nominator, validators) = crate::benchmarking::create_nominator_with_validators::<T>(v)?;
		let current_era = CurrentEra::get().unwrap();
		let find_nominator = validators.into_iter().map(|x| (x, 0)).collect();
     }: _(RawOrigin::Signed(nominator), current_era, find_nominator)

     rebond {
        let l in 1 .. 1000;
        let (_, controller) = create_stash_controller::<T>(u)?;
        let mut staking_ledger = Ledger::<T>::get(controller.clone()).unwrap();
        let unlock_chunk = UnlockChunk::<BalanceOf<T>> {
            value: 1.into(),
            era: EraIndex::zero(),
        };
        for i in 0 .. l {
            staking_ledger.unlocking.push(unlock_chunk.clone())
        }
        Ledger::<T>::insert(controller.clone(), staking_ledger);
     }: _(RawOrigin::Signed(controller), (l + 100).into())

    //  set_history_depth {

    //  }

    reap_stash {
        let u in 1 .. 1000;
        let (stash, controller) = create_stash_controller::<T>(u)?;
        T::Currency::make_free_balance_be(&stash, 0.into());
    }: _(RawOrigin::Signed(controller), stash)
}
