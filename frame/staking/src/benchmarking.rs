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

use crate::Module as Staking;
use frame_system::Module as System;

const SEED: u32 = 0;

fn create_funded_user<T: Trait>(n: u32) -> T::AccountId {
    let user = account("user", n, SEED);
    let balance = T::Currency::minimum_balance() * 100.into();
    T::Currency::make_free_balance_be(&user, balance);
    return user
}

fn create_stash_controller<T: Trait>(n: u32) -> Result<(T::AccountId, T::AccountId), &'static str> {
    let stash = create_funded_user::<T>(n);
    let controller = create_funded_user::<T>(n + 1);
    let controller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(controller.clone());
    let reward_destination = RewardDestination::Staked;
    let amount = T::Currency::minimum_balance() * 10.into();
    Staking::<T>::bond(RawOrigin::Signed(stash.clone()).into(), controller_lookup, amount, reward_destination).unwrap();
    return Ok((stash, controller))
}

benchmarks! {
    _{}

    bond {
        let u in 0 .. 1000;
        let stash = create_funded_user::<T>(u);
        let controller = account("controller", u, SEED);
        let controller_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(controller);
        let reward_destination = RewardDestination::Staked;
        let amount = T::Currency::minimum_balance() * 10.into();
    }: _(RawOrigin::Signed(stash), controller_lookup, amount, reward_destination)

    bond_extra {
        let u in 0 .. 1000;
        let (stash, _) = create_stash_controller::<T>(u)?;
        let max_additional = T::Currency::minimum_balance() * 10.into();
    }: _(RawOrigin::Signed(stash), max_additional)

    unbond {
        let u in 0 .. 1000;
        let (_, controller) = create_stash_controller::<T>(u)?;
        let amount = T::Currency::minimum_balance() * 10.into();
    }: _(RawOrigin::Signed(controller), amount)

    withdraw_unbonded {
        let u in 0 .. 1000;
        let (stash, controller) = create_stash_controller::<T>(u)?;
        let amount = T::Currency::minimum_balance() * 10.into();
        Staking::<T>::unbond(RawOrigin::Signed(controller.clone()).into(), amount)?;
        let current_block = System::<T>::block_number();
        // let unbond_block = current_block + T::BondingDuration::get().into() + 10.into();
        // System::<T>::set_block_number(unbond_block);
    }: _(RawOrigin::Signed(controller))

}
