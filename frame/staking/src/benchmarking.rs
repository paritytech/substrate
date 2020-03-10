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

// This function generates all the storage items for a set of validators, each of whom have
// nominators, and all of whom have some reward.
pub fn create_validators_with_nominators<T: Trait>(v: u32, n: u32) -> Result<(Vec<T::AccountId>, Vec<T::AccountId>), &'static str> {
    let mut validators: Vec<T::AccountId> = Vec::new();
    let mut points_total = 0;
    let mut points_individual = Vec::new();
    let mut nominators: Vec<T::AccountId> = Vec::new();

    for i in 0 .. v {
        let (stash, controller) = create_stash_controller::<T>(i)?;
        let validator_prefs = ValidatorPrefs {
            commission: Perbill::from_percent(50),
        };
        Staking::<T>::validate(RawOrigin::Signed(controller.clone()).into(), validator_prefs)?;
        let stash_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(stash.clone());
        validators.push(controller.clone());
        points_total += i;
        points_individual.push((stash, i));

        // Give each validator n nominators
        for j in 0 .. n {
            let (stash, controller) = create_stash_controller2::<T>(n * i + j)?;
            Staking::<T>::nominate(RawOrigin::Signed(controller.clone()).into(), vec![stash_lookup.clone()])?;
            nominators.push(controller);
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

    Ok((validators, nominators))
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
        let n in 1 .. 1000;
        let v in DEFAULT_MINIMUM_VALIDATOR_COUNT .. 100;
        let (validators, nominators) = create_validators_with_nominators::<T>(v, n)?;
        let current_era = CurrentEra::get().unwrap();
        let user: T::AccountId = validators[validators.len() - 1].clone();
     }: _(RawOrigin::Signed(user), current_era)
}
