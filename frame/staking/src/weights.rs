// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Autogenerated weights for pallet_staking
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 4.0.0-dev
//! DATE: 2022-05-24, STEPS: `50`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE: `[]`
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 1024

// Executed Command:
// ./target/production/substrate
// benchmark
// pallet
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_staking
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --template=./.maintain/frame-weight-template.hbs
// --output=./frame/staking/src/weights.rs

#![cfg_attr(rustfmt, rustfmt_skip)]
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{RefTimeWeight, Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_staking.
pub trait WeightInfo {
	fn bond() -> Weight;
	fn bond_extra() -> Weight;
	fn unbond() -> Weight;
	fn withdraw_unbonded_update(s: u32, ) -> Weight;
	fn withdraw_unbonded_kill(s: u32, ) -> Weight;
	fn validate() -> Weight;
	fn kick(k: u32, ) -> Weight;
	fn nominate(n: u32, ) -> Weight;
	fn chill() -> Weight;
	fn set_payee() -> Weight;
	fn set_controller() -> Weight;
	fn set_validator_count() -> Weight;
	fn force_no_eras() -> Weight;
	fn force_new_era() -> Weight;
	fn force_new_era_always() -> Weight;
	fn set_invulnerables(v: u32, ) -> Weight;
	fn force_unstake(s: u32, ) -> Weight;
	fn cancel_deferred_slash(s: u32, ) -> Weight;
	fn payout_stakers_dead_controller(n: u32, ) -> Weight;
	fn payout_stakers_alive_staked(n: u32, ) -> Weight;
	fn rebond(l: u32, ) -> Weight;
	fn set_history_depth(e: u32, ) -> Weight;
	fn reap_stash(s: u32, ) -> Weight;
	fn new_era(v: u32, n: u32, ) -> Weight;
	fn get_npos_voters(v: u32, n: u32, s: u32, ) -> Weight;
	fn get_npos_targets(v: u32, ) -> Weight;
	fn set_staking_configs_all_set() -> Weight;
	fn set_staking_configs_all_remove() -> Weight;
	fn chill_other() -> Weight;
	fn force_apply_min_commission() -> Weight;
}

/// Weights for pallet_staking using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	// Storage: Staking Bonded (r:1 w:1)
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Staking HistoryDepth (r:1 w:0)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Staking Payee (r:0 w:1)
	fn bond() -> Weight {
		Weight::from_ref_time(43_992_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().reads(5 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(4 as RefTimeWeight))
	}
	// Storage: Staking Bonded (r:1 w:0)
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: BagsList ListNodes (r:3 w:3)
	// Storage: BagsList ListBags (r:2 w:2)
	fn bond_extra() -> Weight {
		Weight::from_ref_time(75_827_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().reads(8 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(7 as RefTimeWeight))
	}
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: Staking Nominators (r:1 w:0)
	// Storage: Staking MinNominatorBond (r:1 w:0)
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	// Storage: BagsList ListNodes (r:3 w:3)
	// Storage: Staking Bonded (r:1 w:0)
	// Storage: BagsList ListBags (r:2 w:2)
	fn unbond() -> Weight {
		Weight::from_ref_time(81_075_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().reads(12 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(8 as RefTimeWeight))
	}
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn withdraw_unbonded_update(s: u32, ) -> Weight {
		Weight::from_ref_time(35_763_000 as RefTimeWeight)
			// Standard Error: 0
			.saturating_add(Weight::from_ref_time(57_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(4 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(3 as RefTimeWeight))
	}
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Staking Bonded (r:1 w:1)
	// Storage: Staking SlashingSpans (r:1 w:0)
	// Storage: Staking Validators (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:1)
	// Storage: Staking CounterForNominators (r:1 w:1)
	// Storage: BagsList ListNodes (r:2 w:2)
	// Storage: BagsList ListBags (r:1 w:1)
	// Storage: BagsList CounterForListNodes (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Staking Payee (r:0 w:1)
	fn withdraw_unbonded_kill(_s: u32, ) -> Weight {
		Weight::from_ref_time(66_938_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().reads(13 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(11 as RefTimeWeight))
	}
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: Staking MinValidatorBond (r:1 w:0)
	// Storage: Staking MinCommission (r:1 w:0)
	// Storage: Staking Validators (r:1 w:1)
	// Storage: Staking MaxValidatorsCount (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:0)
	// Storage: Staking Bonded (r:1 w:0)
	// Storage: BagsList ListNodes (r:1 w:1)
	// Storage: BagsList ListBags (r:1 w:1)
	// Storage: BagsList CounterForListNodes (r:1 w:1)
	// Storage: Staking CounterForValidators (r:1 w:1)
	fn validate() -> Weight {
		Weight::from_ref_time(52_943_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().reads(11 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(5 as RefTimeWeight))
	}
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:1)
	fn kick(k: u32, ) -> Weight {
		Weight::from_ref_time(23_264_000 as RefTimeWeight)
			// Standard Error: 11_000
			.saturating_add(Weight::from_ref_time(8_006_000 as RefTimeWeight).saturating_mul(k as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads((1 as RefTimeWeight).saturating_mul(k as RefTimeWeight)))
			.saturating_add(T::DbWeight::get().writes((1 as RefTimeWeight).saturating_mul(k as RefTimeWeight)))
	}
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: Staking MinNominatorBond (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:1)
	// Storage: Staking MaxNominatorsCount (r:1 w:0)
	// Storage: Staking Validators (r:2 w:0)
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Staking Bonded (r:1 w:0)
	// Storage: BagsList ListNodes (r:2 w:2)
	// Storage: BagsList ListBags (r:1 w:1)
	// Storage: BagsList CounterForListNodes (r:1 w:1)
	// Storage: Staking CounterForNominators (r:1 w:1)
	fn nominate(n: u32, ) -> Weight {
		Weight::from_ref_time(56_596_000 as RefTimeWeight)
			// Standard Error: 14_000
			.saturating_add(Weight::from_ref_time(3_644_000 as RefTimeWeight).saturating_mul(n as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(12 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads((1 as RefTimeWeight).saturating_mul(n as RefTimeWeight)))
			.saturating_add(T::DbWeight::get().writes(6 as RefTimeWeight))
	}
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: Staking Validators (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:1)
	// Storage: Staking CounterForNominators (r:1 w:1)
	// Storage: BagsList ListNodes (r:2 w:2)
	// Storage: BagsList ListBags (r:1 w:1)
	// Storage: BagsList CounterForListNodes (r:1 w:1)
	fn chill() -> Weight {
		Weight::from_ref_time(51_117_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().reads(8 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(6 as RefTimeWeight))
	}
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: Staking Payee (r:0 w:1)
	fn set_payee() -> Weight {
		Weight::from_ref_time(11_223_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Staking Bonded (r:1 w:1)
	// Storage: Staking Ledger (r:2 w:2)
	fn set_controller() -> Weight {
		Weight::from_ref_time(19_826_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().reads(3 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(3 as RefTimeWeight))
	}
	// Storage: Staking ValidatorCount (r:0 w:1)
	fn set_validator_count() -> Weight {
		Weight::from_ref_time(3_789_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Staking ForceEra (r:0 w:1)
	fn force_no_eras() -> Weight {
		Weight::from_ref_time(3_793_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Staking ForceEra (r:0 w:1)
	fn force_new_era() -> Weight {
		Weight::from_ref_time(3_802_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Staking ForceEra (r:0 w:1)
	fn force_new_era_always() -> Weight {
		Weight::from_ref_time(3_762_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Staking Invulnerables (r:0 w:1)
	fn set_invulnerables(v: u32, ) -> Weight {
		Weight::from_ref_time(4_318_000 as RefTimeWeight)
			// Standard Error: 0
			.saturating_add(Weight::from_ref_time(10_000 as RefTimeWeight).saturating_mul(v as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Staking Bonded (r:1 w:1)
	// Storage: Staking SlashingSpans (r:1 w:0)
	// Storage: Staking Validators (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:1)
	// Storage: Staking CounterForNominators (r:1 w:1)
	// Storage: BagsList ListNodes (r:2 w:2)
	// Storage: BagsList ListBags (r:1 w:1)
	// Storage: BagsList CounterForListNodes (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Staking Ledger (r:0 w:1)
	// Storage: Staking Payee (r:0 w:1)
	// Storage: Staking SpanSlash (r:0 w:2)
	fn force_unstake(s: u32, ) -> Weight {
		Weight::from_ref_time(65_265_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(1_029_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(11 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(12 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Staking UnappliedSlashes (r:1 w:1)
	fn cancel_deferred_slash(s: u32, ) -> Weight {
		Weight::from_ref_time(903_312_000 as RefTimeWeight)
			// Standard Error: 56_000
			.saturating_add(Weight::from_ref_time(4_968_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Staking HistoryDepth (r:1 w:0)
	// Storage: Staking ErasValidatorReward (r:1 w:0)
	// Storage: Staking Bonded (r:2 w:0)
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: Staking ErasStakersClipped (r:1 w:0)
	// Storage: Staking ErasRewardPoints (r:1 w:0)
	// Storage: Staking ErasValidatorPrefs (r:1 w:0)
	// Storage: Staking Payee (r:2 w:0)
	// Storage: System Account (r:2 w:2)
	fn payout_stakers_dead_controller(n: u32, ) -> Weight {
		Weight::from_ref_time(87_569_000 as RefTimeWeight)
			// Standard Error: 14_000
			.saturating_add(Weight::from_ref_time(24_232_000 as RefTimeWeight).saturating_mul(n as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(10 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads((3 as RefTimeWeight).saturating_mul(n as RefTimeWeight)))
			.saturating_add(T::DbWeight::get().writes(2 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes((1 as RefTimeWeight).saturating_mul(n as RefTimeWeight)))
	}
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Staking HistoryDepth (r:1 w:0)
	// Storage: Staking ErasValidatorReward (r:1 w:0)
	// Storage: Staking Bonded (r:2 w:0)
	// Storage: Staking Ledger (r:2 w:2)
	// Storage: Staking ErasStakersClipped (r:1 w:0)
	// Storage: Staking ErasRewardPoints (r:1 w:0)
	// Storage: Staking ErasValidatorPrefs (r:1 w:0)
	// Storage: Staking Payee (r:2 w:0)
	// Storage: System Account (r:2 w:2)
	// Storage: Balances Locks (r:2 w:2)
	fn payout_stakers_alive_staked(n: u32, ) -> Weight {
		Weight::from_ref_time(98_839_000 as RefTimeWeight)
			// Standard Error: 21_000
			.saturating_add(Weight::from_ref_time(34_480_000 as RefTimeWeight).saturating_mul(n as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(11 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads((5 as RefTimeWeight).saturating_mul(n as RefTimeWeight)))
			.saturating_add(T::DbWeight::get().writes(3 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes((3 as RefTimeWeight).saturating_mul(n as RefTimeWeight)))
	}
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	// Storage: BagsList ListNodes (r:3 w:3)
	// Storage: Staking Bonded (r:1 w:0)
	// Storage: BagsList ListBags (r:2 w:2)
	fn rebond(l: u32, ) -> Weight {
		Weight::from_ref_time(74_865_000 as RefTimeWeight)
			// Standard Error: 3_000
			.saturating_add(Weight::from_ref_time(64_000 as RefTimeWeight).saturating_mul(l as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(9 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(8 as RefTimeWeight))
	}
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Staking HistoryDepth (r:1 w:1)
	// Storage: Staking ErasStakersClipped (r:0 w:2)
	// Storage: Staking ErasValidatorPrefs (r:0 w:2)
	// Storage: Staking ErasValidatorReward (r:0 w:1)
	// Storage: Staking ErasRewardPoints (r:0 w:1)
	// Storage: Staking ErasStakers (r:0 w:2)
	// Storage: Staking ErasTotalStake (r:0 w:1)
	// Storage: Staking ErasStartSessionIndex (r:0 w:1)
	fn set_history_depth(e: u32, ) -> Weight {
		Weight::from_ref_time(0 as RefTimeWeight)
			// Standard Error: 62_000
			.saturating_add(Weight::from_ref_time(22_829_000 as RefTimeWeight).saturating_mul(e as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(4 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes((7 as RefTimeWeight).saturating_mul(e as RefTimeWeight)))
	}
	// Storage: System Account (r:1 w:1)
	// Storage: Staking Bonded (r:1 w:1)
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: Staking SlashingSpans (r:1 w:1)
	// Storage: Staking Validators (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:1)
	// Storage: Staking CounterForNominators (r:1 w:1)
	// Storage: BagsList ListNodes (r:2 w:2)
	// Storage: BagsList ListBags (r:1 w:1)
	// Storage: BagsList CounterForListNodes (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Staking Payee (r:0 w:1)
	// Storage: Staking SpanSlash (r:0 w:1)
	fn reap_stash(s: u32, ) -> Weight {
		Weight::from_ref_time(70_933_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(1_021_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(12 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(12 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: BagsList CounterForListNodes (r:1 w:0)
	// Storage: Staking SlashingSpans (r:1 w:0)
	// Storage: BagsList ListBags (r:200 w:0)
	// Storage: BagsList ListNodes (r:101 w:0)
	// Storage: Staking Nominators (r:101 w:0)
	// Storage: Staking Validators (r:2 w:0)
	// Storage: Staking Bonded (r:101 w:0)
	// Storage: Staking Ledger (r:101 w:0)
	// Storage: Staking CounterForValidators (r:1 w:0)
	// Storage: Staking ValidatorCount (r:1 w:0)
	// Storage: Staking MinimumValidatorCount (r:1 w:0)
	// Storage: Staking CurrentEra (r:1 w:1)
	// Storage: Staking HistoryDepth (r:1 w:0)
	// Storage: Staking ErasStakersClipped (r:0 w:1)
	// Storage: Staking ErasValidatorPrefs (r:0 w:1)
	// Storage: Staking ErasStakers (r:0 w:1)
	// Storage: Staking ErasTotalStake (r:0 w:1)
	// Storage: Staking ErasStartSessionIndex (r:0 w:1)
	fn new_era(v: u32, n: u32, ) -> Weight {
		Weight::from_ref_time(0 as RefTimeWeight)
			// Standard Error: 897_000
			.saturating_add(Weight::from_ref_time(213_100_000 as RefTimeWeight).saturating_mul(v as RefTimeWeight))
			// Standard Error: 45_000
			.saturating_add(Weight::from_ref_time(31_123_000 as RefTimeWeight).saturating_mul(n as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(208 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads((5 as RefTimeWeight).saturating_mul(v as RefTimeWeight)))
			.saturating_add(T::DbWeight::get().reads((4 as RefTimeWeight).saturating_mul(n as RefTimeWeight)))
			.saturating_add(T::DbWeight::get().writes(3 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes((3 as RefTimeWeight).saturating_mul(v as RefTimeWeight)))
	}
	// Storage: BagsList CounterForListNodes (r:1 w:0)
	// Storage: Staking SlashingSpans (r:21 w:0)
	// Storage: BagsList ListBags (r:200 w:0)
	// Storage: BagsList ListNodes (r:1500 w:0)
	// Storage: Staking Nominators (r:1500 w:0)
	// Storage: Staking Validators (r:500 w:0)
	// Storage: Staking Bonded (r:1500 w:0)
	// Storage: Staking Ledger (r:1500 w:0)
	fn get_npos_voters(v: u32, n: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(0 as RefTimeWeight)
			// Standard Error: 116_000
			.saturating_add(Weight::from_ref_time(23_745_000 as RefTimeWeight).saturating_mul(v as RefTimeWeight))
			// Standard Error: 116_000
			.saturating_add(Weight::from_ref_time(22_497_000 as RefTimeWeight).saturating_mul(n as RefTimeWeight))
			// Standard Error: 3_968_000
			.saturating_add(Weight::from_ref_time(20_676_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(202 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads((5 as RefTimeWeight).saturating_mul(v as RefTimeWeight)))
			.saturating_add(T::DbWeight::get().reads((4 as RefTimeWeight).saturating_mul(n as RefTimeWeight)))
			.saturating_add(T::DbWeight::get().reads((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Staking Validators (r:501 w:0)
	fn get_npos_targets(v: u32, ) -> Weight {
		Weight::from_ref_time(0 as RefTimeWeight)
			// Standard Error: 36_000
			.saturating_add(Weight::from_ref_time(8_097_000 as RefTimeWeight).saturating_mul(v as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().reads((1 as RefTimeWeight).saturating_mul(v as RefTimeWeight)))
	}
	// Storage: Staking MinCommission (r:0 w:1)
	// Storage: Staking MinValidatorBond (r:0 w:1)
	// Storage: Staking MaxValidatorsCount (r:0 w:1)
	// Storage: Staking ChillThreshold (r:0 w:1)
	// Storage: Staking MaxNominatorsCount (r:0 w:1)
	// Storage: Staking MinNominatorBond (r:0 w:1)
	fn set_staking_configs_all_set() -> Weight {
		Weight::from_ref_time(7_041_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().writes(6 as RefTimeWeight))
	}
	// Storage: Staking MinCommission (r:0 w:1)
	// Storage: Staking MinValidatorBond (r:0 w:1)
	// Storage: Staking MaxValidatorsCount (r:0 w:1)
	// Storage: Staking ChillThreshold (r:0 w:1)
	// Storage: Staking MaxNominatorsCount (r:0 w:1)
	// Storage: Staking MinNominatorBond (r:0 w:1)
	fn set_staking_configs_all_remove() -> Weight {
		Weight::from_ref_time(6_495_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().writes(6 as RefTimeWeight))
	}
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:1)
	// Storage: Staking ChillThreshold (r:1 w:0)
	// Storage: Staking MaxNominatorsCount (r:1 w:0)
	// Storage: Staking CounterForNominators (r:1 w:1)
	// Storage: Staking MinNominatorBond (r:1 w:0)
	// Storage: Staking Validators (r:1 w:0)
	// Storage: BagsList ListNodes (r:2 w:2)
	// Storage: BagsList ListBags (r:1 w:1)
	// Storage: BagsList CounterForListNodes (r:1 w:1)
	fn chill_other() -> Weight {
		Weight::from_ref_time(62_014_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().reads(11 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(6 as RefTimeWeight))
	}
	// Storage: Staking MinCommission (r:1 w:0)
	// Storage: Staking Validators (r:1 w:1)
	fn force_apply_min_commission() -> Weight {
		Weight::from_ref_time(12_814_000 as RefTimeWeight)
			.saturating_add(T::DbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(T::DbWeight::get().writes(1 as RefTimeWeight))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	// Storage: Staking Bonded (r:1 w:1)
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Staking HistoryDepth (r:1 w:0)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Staking Payee (r:0 w:1)
	fn bond() -> Weight {
		Weight::from_ref_time(43_992_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().reads(5 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(4 as RefTimeWeight))
	}
	// Storage: Staking Bonded (r:1 w:0)
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: BagsList ListNodes (r:3 w:3)
	// Storage: BagsList ListBags (r:2 w:2)
	fn bond_extra() -> Weight {
		Weight::from_ref_time(75_827_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().reads(8 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(7 as RefTimeWeight))
	}
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: Staking Nominators (r:1 w:0)
	// Storage: Staking MinNominatorBond (r:1 w:0)
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	// Storage: BagsList ListNodes (r:3 w:3)
	// Storage: Staking Bonded (r:1 w:0)
	// Storage: BagsList ListBags (r:2 w:2)
	fn unbond() -> Weight {
		Weight::from_ref_time(81_075_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().reads(12 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(8 as RefTimeWeight))
	}
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	fn withdraw_unbonded_update(s: u32, ) -> Weight {
		Weight::from_ref_time(35_763_000 as RefTimeWeight)
			// Standard Error: 0
			.saturating_add(Weight::from_ref_time(57_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(4 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(3 as RefTimeWeight))
	}
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Staking Bonded (r:1 w:1)
	// Storage: Staking SlashingSpans (r:1 w:0)
	// Storage: Staking Validators (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:1)
	// Storage: Staking CounterForNominators (r:1 w:1)
	// Storage: BagsList ListNodes (r:2 w:2)
	// Storage: BagsList ListBags (r:1 w:1)
	// Storage: BagsList CounterForListNodes (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Staking Payee (r:0 w:1)
	fn withdraw_unbonded_kill(_s: u32, ) -> Weight {
		Weight::from_ref_time(66_938_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().reads(13 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(11 as RefTimeWeight))
	}
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: Staking MinValidatorBond (r:1 w:0)
	// Storage: Staking MinCommission (r:1 w:0)
	// Storage: Staking Validators (r:1 w:1)
	// Storage: Staking MaxValidatorsCount (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:0)
	// Storage: Staking Bonded (r:1 w:0)
	// Storage: BagsList ListNodes (r:1 w:1)
	// Storage: BagsList ListBags (r:1 w:1)
	// Storage: BagsList CounterForListNodes (r:1 w:1)
	// Storage: Staking CounterForValidators (r:1 w:1)
	fn validate() -> Weight {
		Weight::from_ref_time(52_943_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().reads(11 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(5 as RefTimeWeight))
	}
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:1)
	fn kick(k: u32, ) -> Weight {
		Weight::from_ref_time(23_264_000 as RefTimeWeight)
			// Standard Error: 11_000
			.saturating_add(Weight::from_ref_time(8_006_000 as RefTimeWeight).saturating_mul(k as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads((1 as RefTimeWeight).saturating_mul(k as RefTimeWeight)))
			.saturating_add(RocksDbWeight::get().writes((1 as RefTimeWeight).saturating_mul(k as RefTimeWeight)))
	}
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: Staking MinNominatorBond (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:1)
	// Storage: Staking MaxNominatorsCount (r:1 w:0)
	// Storage: Staking Validators (r:2 w:0)
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Staking Bonded (r:1 w:0)
	// Storage: BagsList ListNodes (r:2 w:2)
	// Storage: BagsList ListBags (r:1 w:1)
	// Storage: BagsList CounterForListNodes (r:1 w:1)
	// Storage: Staking CounterForNominators (r:1 w:1)
	fn nominate(n: u32, ) -> Weight {
		Weight::from_ref_time(56_596_000 as RefTimeWeight)
			// Standard Error: 14_000
			.saturating_add(Weight::from_ref_time(3_644_000 as RefTimeWeight).saturating_mul(n as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(12 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads((1 as RefTimeWeight).saturating_mul(n as RefTimeWeight)))
			.saturating_add(RocksDbWeight::get().writes(6 as RefTimeWeight))
	}
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: Staking Validators (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:1)
	// Storage: Staking CounterForNominators (r:1 w:1)
	// Storage: BagsList ListNodes (r:2 w:2)
	// Storage: BagsList ListBags (r:1 w:1)
	// Storage: BagsList CounterForListNodes (r:1 w:1)
	fn chill() -> Weight {
		Weight::from_ref_time(51_117_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().reads(8 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(6 as RefTimeWeight))
	}
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: Staking Payee (r:0 w:1)
	fn set_payee() -> Weight {
		Weight::from_ref_time(11_223_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Staking Bonded (r:1 w:1)
	// Storage: Staking Ledger (r:2 w:2)
	fn set_controller() -> Weight {
		Weight::from_ref_time(19_826_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().reads(3 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(3 as RefTimeWeight))
	}
	// Storage: Staking ValidatorCount (r:0 w:1)
	fn set_validator_count() -> Weight {
		Weight::from_ref_time(3_789_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Staking ForceEra (r:0 w:1)
	fn force_no_eras() -> Weight {
		Weight::from_ref_time(3_793_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Staking ForceEra (r:0 w:1)
	fn force_new_era() -> Weight {
		Weight::from_ref_time(3_802_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Staking ForceEra (r:0 w:1)
	fn force_new_era_always() -> Weight {
		Weight::from_ref_time(3_762_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Staking Invulnerables (r:0 w:1)
	fn set_invulnerables(v: u32, ) -> Weight {
		Weight::from_ref_time(4_318_000 as RefTimeWeight)
			// Standard Error: 0
			.saturating_add(Weight::from_ref_time(10_000 as RefTimeWeight).saturating_mul(v as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Staking Bonded (r:1 w:1)
	// Storage: Staking SlashingSpans (r:1 w:0)
	// Storage: Staking Validators (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:1)
	// Storage: Staking CounterForNominators (r:1 w:1)
	// Storage: BagsList ListNodes (r:2 w:2)
	// Storage: BagsList ListBags (r:1 w:1)
	// Storage: BagsList CounterForListNodes (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Staking Ledger (r:0 w:1)
	// Storage: Staking Payee (r:0 w:1)
	// Storage: Staking SpanSlash (r:0 w:2)
	fn force_unstake(s: u32, ) -> Weight {
		Weight::from_ref_time(65_265_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(1_029_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(11 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(12 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Staking UnappliedSlashes (r:1 w:1)
	fn cancel_deferred_slash(s: u32, ) -> Weight {
		Weight::from_ref_time(903_312_000 as RefTimeWeight)
			// Standard Error: 56_000
			.saturating_add(Weight::from_ref_time(4_968_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
	}
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Staking HistoryDepth (r:1 w:0)
	// Storage: Staking ErasValidatorReward (r:1 w:0)
	// Storage: Staking Bonded (r:2 w:0)
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: Staking ErasStakersClipped (r:1 w:0)
	// Storage: Staking ErasRewardPoints (r:1 w:0)
	// Storage: Staking ErasValidatorPrefs (r:1 w:0)
	// Storage: Staking Payee (r:2 w:0)
	// Storage: System Account (r:2 w:2)
	fn payout_stakers_dead_controller(n: u32, ) -> Weight {
		Weight::from_ref_time(87_569_000 as RefTimeWeight)
			// Standard Error: 14_000
			.saturating_add(Weight::from_ref_time(24_232_000 as RefTimeWeight).saturating_mul(n as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(10 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads((3 as RefTimeWeight).saturating_mul(n as RefTimeWeight)))
			.saturating_add(RocksDbWeight::get().writes(2 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes((1 as RefTimeWeight).saturating_mul(n as RefTimeWeight)))
	}
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Staking HistoryDepth (r:1 w:0)
	// Storage: Staking ErasValidatorReward (r:1 w:0)
	// Storage: Staking Bonded (r:2 w:0)
	// Storage: Staking Ledger (r:2 w:2)
	// Storage: Staking ErasStakersClipped (r:1 w:0)
	// Storage: Staking ErasRewardPoints (r:1 w:0)
	// Storage: Staking ErasValidatorPrefs (r:1 w:0)
	// Storage: Staking Payee (r:2 w:0)
	// Storage: System Account (r:2 w:2)
	// Storage: Balances Locks (r:2 w:2)
	fn payout_stakers_alive_staked(n: u32, ) -> Weight {
		Weight::from_ref_time(98_839_000 as RefTimeWeight)
			// Standard Error: 21_000
			.saturating_add(Weight::from_ref_time(34_480_000 as RefTimeWeight).saturating_mul(n as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(11 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads((5 as RefTimeWeight).saturating_mul(n as RefTimeWeight)))
			.saturating_add(RocksDbWeight::get().writes(3 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes((3 as RefTimeWeight).saturating_mul(n as RefTimeWeight)))
	}
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: System Account (r:1 w:1)
	// Storage: BagsList ListNodes (r:3 w:3)
	// Storage: Staking Bonded (r:1 w:0)
	// Storage: BagsList ListBags (r:2 w:2)
	fn rebond(l: u32, ) -> Weight {
		Weight::from_ref_time(74_865_000 as RefTimeWeight)
			// Standard Error: 3_000
			.saturating_add(Weight::from_ref_time(64_000 as RefTimeWeight).saturating_mul(l as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(9 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(8 as RefTimeWeight))
	}
	// Storage: Staking CurrentEra (r:1 w:0)
	// Storage: Staking HistoryDepth (r:1 w:1)
	// Storage: Staking ErasStakersClipped (r:0 w:2)
	// Storage: Staking ErasValidatorPrefs (r:0 w:2)
	// Storage: Staking ErasValidatorReward (r:0 w:1)
	// Storage: Staking ErasRewardPoints (r:0 w:1)
	// Storage: Staking ErasStakers (r:0 w:2)
	// Storage: Staking ErasTotalStake (r:0 w:1)
	// Storage: Staking ErasStartSessionIndex (r:0 w:1)
	fn set_history_depth(e: u32, ) -> Weight {
		Weight::from_ref_time(0 as RefTimeWeight)
			// Standard Error: 62_000
			.saturating_add(Weight::from_ref_time(22_829_000 as RefTimeWeight).saturating_mul(e as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(4 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes((7 as RefTimeWeight).saturating_mul(e as RefTimeWeight)))
	}
	// Storage: System Account (r:1 w:1)
	// Storage: Staking Bonded (r:1 w:1)
	// Storage: Staking Ledger (r:1 w:1)
	// Storage: Staking SlashingSpans (r:1 w:1)
	// Storage: Staking Validators (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:1)
	// Storage: Staking CounterForNominators (r:1 w:1)
	// Storage: BagsList ListNodes (r:2 w:2)
	// Storage: BagsList ListBags (r:1 w:1)
	// Storage: BagsList CounterForListNodes (r:1 w:1)
	// Storage: Balances Locks (r:1 w:1)
	// Storage: Staking Payee (r:0 w:1)
	// Storage: Staking SpanSlash (r:0 w:1)
	fn reap_stash(s: u32, ) -> Weight {
		Weight::from_ref_time(70_933_000 as RefTimeWeight)
			// Standard Error: 1_000
			.saturating_add(Weight::from_ref_time(1_021_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(12 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(12 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: BagsList CounterForListNodes (r:1 w:0)
	// Storage: Staking SlashingSpans (r:1 w:0)
	// Storage: BagsList ListBags (r:200 w:0)
	// Storage: BagsList ListNodes (r:101 w:0)
	// Storage: Staking Nominators (r:101 w:0)
	// Storage: Staking Validators (r:2 w:0)
	// Storage: Staking Bonded (r:101 w:0)
	// Storage: Staking Ledger (r:101 w:0)
	// Storage: Staking CounterForValidators (r:1 w:0)
	// Storage: Staking ValidatorCount (r:1 w:0)
	// Storage: Staking MinimumValidatorCount (r:1 w:0)
	// Storage: Staking CurrentEra (r:1 w:1)
	// Storage: Staking HistoryDepth (r:1 w:0)
	// Storage: Staking ErasStakersClipped (r:0 w:1)
	// Storage: Staking ErasValidatorPrefs (r:0 w:1)
	// Storage: Staking ErasStakers (r:0 w:1)
	// Storage: Staking ErasTotalStake (r:0 w:1)
	// Storage: Staking ErasStartSessionIndex (r:0 w:1)
	fn new_era(v: u32, n: u32, ) -> Weight {
		Weight::from_ref_time(0 as RefTimeWeight)
			// Standard Error: 897_000
			.saturating_add(Weight::from_ref_time(213_100_000 as RefTimeWeight).saturating_mul(v as RefTimeWeight))
			// Standard Error: 45_000
			.saturating_add(Weight::from_ref_time(31_123_000 as RefTimeWeight).saturating_mul(n as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(208 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads((5 as RefTimeWeight).saturating_mul(v as RefTimeWeight)))
			.saturating_add(RocksDbWeight::get().reads((4 as RefTimeWeight).saturating_mul(n as RefTimeWeight)))
			.saturating_add(RocksDbWeight::get().writes(3 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes((3 as RefTimeWeight).saturating_mul(v as RefTimeWeight)))
	}
	// Storage: BagsList CounterForListNodes (r:1 w:0)
	// Storage: Staking SlashingSpans (r:21 w:0)
	// Storage: BagsList ListBags (r:200 w:0)
	// Storage: BagsList ListNodes (r:1500 w:0)
	// Storage: Staking Nominators (r:1500 w:0)
	// Storage: Staking Validators (r:500 w:0)
	// Storage: Staking Bonded (r:1500 w:0)
	// Storage: Staking Ledger (r:1500 w:0)
	fn get_npos_voters(v: u32, n: u32, s: u32, ) -> Weight {
		Weight::from_ref_time(0 as RefTimeWeight)
			// Standard Error: 116_000
			.saturating_add(Weight::from_ref_time(23_745_000 as RefTimeWeight).saturating_mul(v as RefTimeWeight))
			// Standard Error: 116_000
			.saturating_add(Weight::from_ref_time(22_497_000 as RefTimeWeight).saturating_mul(n as RefTimeWeight))
			// Standard Error: 3_968_000
			.saturating_add(Weight::from_ref_time(20_676_000 as RefTimeWeight).saturating_mul(s as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(202 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads((5 as RefTimeWeight).saturating_mul(v as RefTimeWeight)))
			.saturating_add(RocksDbWeight::get().reads((4 as RefTimeWeight).saturating_mul(n as RefTimeWeight)))
			.saturating_add(RocksDbWeight::get().reads((1 as RefTimeWeight).saturating_mul(s as RefTimeWeight)))
	}
	// Storage: Staking Validators (r:501 w:0)
	fn get_npos_targets(v: u32, ) -> Weight {
		Weight::from_ref_time(0 as RefTimeWeight)
			// Standard Error: 36_000
			.saturating_add(Weight::from_ref_time(8_097_000 as RefTimeWeight).saturating_mul(v as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads(1 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().reads((1 as RefTimeWeight).saturating_mul(v as RefTimeWeight)))
	}
	// Storage: Staking MinCommission (r:0 w:1)
	// Storage: Staking MinValidatorBond (r:0 w:1)
	// Storage: Staking MaxValidatorsCount (r:0 w:1)
	// Storage: Staking ChillThreshold (r:0 w:1)
	// Storage: Staking MaxNominatorsCount (r:0 w:1)
	// Storage: Staking MinNominatorBond (r:0 w:1)
	fn set_staking_configs_all_set() -> Weight {
		Weight::from_ref_time(7_041_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().writes(6 as RefTimeWeight))
	}
	// Storage: Staking MinCommission (r:0 w:1)
	// Storage: Staking MinValidatorBond (r:0 w:1)
	// Storage: Staking MaxValidatorsCount (r:0 w:1)
	// Storage: Staking ChillThreshold (r:0 w:1)
	// Storage: Staking MaxNominatorsCount (r:0 w:1)
	// Storage: Staking MinNominatorBond (r:0 w:1)
	fn set_staking_configs_all_remove() -> Weight {
		Weight::from_ref_time(6_495_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().writes(6 as RefTimeWeight))
	}
	// Storage: Staking Ledger (r:1 w:0)
	// Storage: Staking Nominators (r:1 w:1)
	// Storage: Staking ChillThreshold (r:1 w:0)
	// Storage: Staking MaxNominatorsCount (r:1 w:0)
	// Storage: Staking CounterForNominators (r:1 w:1)
	// Storage: Staking MinNominatorBond (r:1 w:0)
	// Storage: Staking Validators (r:1 w:0)
	// Storage: BagsList ListNodes (r:2 w:2)
	// Storage: BagsList ListBags (r:1 w:1)
	// Storage: BagsList CounterForListNodes (r:1 w:1)
	fn chill_other() -> Weight {
		Weight::from_ref_time(62_014_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().reads(11 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(6 as RefTimeWeight))
	}
	// Storage: Staking MinCommission (r:1 w:0)
	// Storage: Staking Validators (r:1 w:1)
	fn force_apply_min_commission() -> Weight {
		Weight::from_ref_time(12_814_000 as RefTimeWeight)
			.saturating_add(RocksDbWeight::get().reads(2 as RefTimeWeight))
			.saturating_add(RocksDbWeight::get().writes(1 as RefTimeWeight))
	}
}
