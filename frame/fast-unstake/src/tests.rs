// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Tests for pallet-fast-unstake.

use super::*;
use crate::{mock::*, types::*, weights::WeightInfo, Event};
use frame_support::{assert_noop, assert_ok, bounded_vec, pallet_prelude::*, traits::Currency};
use pallet_nomination_pools::{BondedPools, LastPoolId, RewardPools};
use pallet_staking::{CurrentEra, IndividualExposure, RewardDestination};

use sp_runtime::{traits::BadOrigin, DispatchError, ModuleError};
use sp_staking::StakingInterface;

#[test]
fn test_setup_works() {
	ExtBuilder::default().build_and_execute(|| {
		assert_eq!(BondedPools::<T>::count(), 1);
		assert_eq!(RewardPools::<T>::count(), 1);
		assert_eq!(Staking::bonding_duration(), 3);
		let last_pool = LastPoolId::<T>::get();
		assert_eq!(last_pool, 1);
	});
}

#[test]
fn register_works() {
	ExtBuilder::default().build_and_execute(|| {
		// Controller account registers for fast unstake.
		assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), Some(1_u32)));
		// Ensure stash is in the queue.
		assert_ne!(Queue::<T>::get(1), None);
	});
}

#[test]
fn cannot_register_if_not_bonded() {
	ExtBuilder::default().build_and_execute(|| {
		// Mint accounts 1 and 2 with 200 tokens.
		for _ in 1..2 {
			let _ = Balances::make_free_balance_be(&1, 200);
		}
		// Attempt to fast unstake.
		assert_noop!(
			FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1), Some(1_u32)),
			Error::<T>::NotController
		);
	});
}

#[test]
fn cannot_register_if_in_queue() {
	ExtBuilder::default().build_and_execute(|| {
		// Insert some Queue item
		Queue::<T>::insert(1, Some(1_u32));
		// Cannot re-register, already in queue
		assert_noop!(
			FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), Some(1_u32)),
			Error::<T>::AlreadyQueued
		);
	});
}

#[test]
fn cannot_register_if_head() {
	ExtBuilder::default().build_and_execute(|| {
		// Insert some Head item for stash
		Head::<T>::put(UnstakeRequest { stash: 1, checked: bounded_vec![], maybe_pool_id: None });
		// Controller attempts to regsiter
		assert_noop!(
			FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), Some(1_u32)),
			Error::<T>::AlreadyHead
		);
	});
}

#[test]
fn cannot_register_if_has_unlocking_chunks() {
	ExtBuilder::default().build_and_execute(|| {
		// Start unbonding half of staked tokens
		assert_ok!(Staking::unbond(RuntimeOrigin::signed(2), 50_u128));
		// Cannot register for fast unstake with unlock chunks active
		assert_noop!(
			FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), Some(1_u32)),
			Error::<T>::NotFullyBonded
		);
	});
}

#[test]
fn deregister_works() {
	ExtBuilder::default().build_and_execute(|| {
		// Controller account registers for fast unstake.
		assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), Some(1_u32)));
		// Controller then changes mind and deregisters.
		assert_ok!(FastUnstake::deregister(RuntimeOrigin::signed(2)));
		// Ensure stash no longer exists in the queue.
		assert_eq!(Queue::<T>::get(1), None);
	});
}

#[test]
fn cannot_deregister_if_not_controller() {
	ExtBuilder::default().build_and_execute(|| {
		// Controller account registers for fast unstake.
		assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), Some(1_u32)));
		// Stash tries to deregister.
		assert_noop!(FastUnstake::deregister(RuntimeOrigin::signed(1)), Error::<T>::NotController);
	});
}

#[test]
fn cannot_deregister_if_not_queued() {
	ExtBuilder::default().build_and_execute(|| {
		// Controller tries to deregister without first registering
		assert_noop!(FastUnstake::deregister(RuntimeOrigin::signed(2)), Error::<T>::NotQueued);
	});
}

#[test]
fn cannot_deregister_already_head() {
	ExtBuilder::default().build_and_execute(|| {
		// Controller attempts to register, should fail
		assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), Some(1_u32)));
		// Insert some Head item for stash.
		Head::<T>::put(UnstakeRequest { stash: 1, checked: bounded_vec![], maybe_pool_id: None });
		// Controller attempts to deregister
		assert_noop!(FastUnstake::deregister(RuntimeOrigin::signed(2)), Error::<T>::AlreadyHead);
	});
}

#[test]
fn control_works() {
	ExtBuilder::default().build_and_execute(|| {
		// account with control (root) origin wants to only check 1 era per block.
		assert_ok!(FastUnstake::control(RuntimeOrigin::root(), 1_u32));
	});
}

#[test]
fn control_must_be_control_origin() {
	ExtBuilder::default().build_and_execute(|| {
		// account without control (root) origin wants to only check 1 era per block.
		assert_noop!(FastUnstake::control(RuntimeOrigin::signed(1), 1_u32), BadOrigin);
	});
}

mod on_idle {
	use super::*;

	#[test]
	fn early_exit() {
		ExtBuilder::default().build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(BondingDuration::get() + 1);
			CurrentEra::<T>::put(BondingDuration::get());

			// set up Queue item
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), Some(1)));
			assert_eq!(Queue::<T>::get(1), Some(Some(1)));

			// call on_idle with no remaining weight
			FastUnstake::on_idle(System::block_number(), Weight::from_ref_time(0));

			// assert nothing changed in Queue and Head
			assert_eq!(Head::<T>::get(), None);
			assert_eq!(Queue::<T>::get(1), Some(Some(1)));
		});
	}

	#[test]
	fn respects_weight() {
		ExtBuilder::default().build_and_execute(|| {
			// we want to check all eras in one block...
			ErasToCheckPerBlock::<T>::put(BondingDuration::get() + 1);
			CurrentEra::<T>::put(BondingDuration::get());

			// given
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), Some(1)));
			assert_eq!(Queue::<T>::get(1), Some(Some(1)));

			assert_eq!(Queue::<T>::count(), 1);
			assert_eq!(Head::<T>::get(), None);

			// when: call fast unstake with not enough weight to process the whole thing, just one
			// era.
			let remaining_weight = <T as Config>::WeightInfo::on_idle_check(
				pallet_staking::ValidatorCount::<T>::get() * 1,
			);
			assert_eq!(FastUnstake::on_idle(0, remaining_weight), remaining_weight);

			// then
			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![Event::Checking { stash: 1, eras: vec![3] }]
			);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest { stash: 1, checked: bounded_vec![3], maybe_pool_id: Some(1) })
			);

			// when: another 1 era.
			let remaining_weight = <T as Config>::WeightInfo::on_idle_check(
				pallet_staking::ValidatorCount::<T>::get() * 1,
			);
			assert_eq!(FastUnstake::on_idle(0, remaining_weight), remaining_weight);

			// then:
			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![Event::Checking { stash: 1, eras: bounded_vec![2] }]
			);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2],
					maybe_pool_id: Some(1)
				})
			);

			// when: then 5 eras, we only need 2 more.
			let remaining_weight = <T as Config>::WeightInfo::on_idle_check(
				pallet_staking::ValidatorCount::<T>::get() * 5,
			);
			assert_eq!(
				FastUnstake::on_idle(0, remaining_weight),
				// note the amount of weight consumed: 2 eras worth of weight.
				<T as Config>::WeightInfo::on_idle_check(
					pallet_staking::ValidatorCount::<T>::get() * 2,
				)
			);

			// then:
			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![Event::Checking { stash: 1, eras: vec![1, 0] }]
			);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2, 1, 0],
					maybe_pool_id: Some(1)
				})
			);

			// when: not enough weight to unstake:
			let remaining_weight =
				<T as Config>::WeightInfo::on_idle_unstake() - Weight::from_ref_time(1);
			assert_eq!(FastUnstake::on_idle(0, remaining_weight), Weight::from_ref_time(0));

			// then nothing happens:
			assert_eq!(fast_unstake_events_since_last_call(), vec![]);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2, 1, 0],
					maybe_pool_id: Some(1)
				})
			);

			// when: enough weight to get over at least one iteration: then we are unblocked and can
			// unstake.
			let remaining_weight = <T as Config>::WeightInfo::on_idle_check(
				pallet_staking::ValidatorCount::<T>::get() * 1,
			);
			assert_eq!(
				FastUnstake::on_idle(0, remaining_weight),
				<T as Config>::WeightInfo::on_idle_unstake()
			);

			// then we finish the unbonding:
			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![Event::Unstaked { stash: 1, maybe_pool_id: Some(1), result: Ok(()) }]
			);
			assert_eq!(Head::<T>::get(), None,);

			assert_unstaked(&1);
		});
	}

	#[test]
	fn if_head_not_set_one_random_fetched_from_queue() {
		ExtBuilder::default().build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(BondingDuration::get() + 1);
			CurrentEra::<T>::put(BondingDuration::get());

			// given
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), None));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(4), None));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(6), None));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(8), None));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(10), None));

			assert_eq!(Queue::<T>::count(), 5);
			assert_eq!(Head::<T>::get(), None);

			// when
			next_block(true);

			// then
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2, 1, 0],
					maybe_pool_id: None
				})
			);
			assert_eq!(Queue::<T>::count(), 4);

			// when
			next_block(true);

			// then
			assert_eq!(Head::<T>::get(), None,);
			assert_eq!(Queue::<T>::count(), 4);

			// when
			next_block(true);

			// then
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 5,
					checked: bounded_vec![3, 2, 1, 0],
					maybe_pool_id: None
				}),
			);
			assert_eq!(Queue::<T>::count(), 3);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::Checking { stash: 1, eras: vec![3, 2, 1, 0] },
					Event::Unstaked { stash: 1, maybe_pool_id: None, result: Ok(()) },
					Event::Checking { stash: 5, eras: vec![3, 2, 1, 0] }
				]
			);
		});
	}

	#[test]
	fn successful_multi_queue() {
		ExtBuilder::default().build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(BondingDuration::get() + 1);
			CurrentEra::<T>::put(BondingDuration::get());

			// register multi accounts for fast unstake
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), Some(1)));
			assert_eq!(Queue::<T>::get(1), Some(Some(1)));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(4), Some(1)));
			assert_eq!(Queue::<T>::get(3), Some(Some(1)));

			// assert 2 queue items are in Queue & None in Head to start with
			assert_eq!(Queue::<T>::count(), 2);
			assert_eq!(Head::<T>::get(), None);

			// process on idle and check eras for next Queue item
			next_block(true);

			// process on idle & let go of current Head
			next_block(true);

			// confirm Head / Queue items remaining
			assert_eq!(Queue::<T>::count(), 1);
			assert_eq!(Head::<T>::get(), None);

			// process on idle and check eras for next Queue item
			next_block(true);

			// process on idle & let go of current Head
			next_block(true);

			// Head & Queue should now be empty
			assert_eq!(Head::<T>::get(), None);
			assert_eq!(Queue::<T>::count(), 0);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::Checking { stash: 1, eras: vec![3, 2, 1, 0] },
					Event::Unstaked { stash: 1, maybe_pool_id: Some(1), result: Ok(()) },
					Event::Checking { stash: 3, eras: vec![3, 2, 1, 0] },
					Event::Unstaked { stash: 3, maybe_pool_id: Some(1), result: Ok(()) },
				]
			);

			assert_unstaked(&1);
			assert_unstaked(&3);
		});
	}

	#[test]
	fn successful_unstake_without_pool_join() {
		ExtBuilder::default().build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(BondingDuration::get() + 1);
			CurrentEra::<T>::put(BondingDuration::get());

			// register for fast unstake
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), None));
			assert_eq!(Queue::<T>::get(1), Some(None));

			// process on idle
			next_block(true);

			// assert queue item has been moved to head
			assert_eq!(Queue::<T>::get(1), None);

			// assert head item present
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2, 1, 0],
					maybe_pool_id: None
				})
			);

			next_block(true);
			assert_eq!(Head::<T>::get(), None,);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::Checking { stash: 1, eras: vec![3, 2, 1, 0] },
					Event::Unstaked { stash: 1, maybe_pool_id: None, result: Ok(()) }
				]
			);
			assert_unstaked(&1);
		});
	}

	#[test]
	fn successful_unstake_joining_bad_pool() {
		ExtBuilder::default().build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(BondingDuration::get() + 1);
			CurrentEra::<T>::put(BondingDuration::get());

			// register for fast unstake
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), Some(0)));
			assert_eq!(Queue::<T>::get(1), Some(Some(0)));

			// process on idle
			next_block(true);

			// assert queue item has been moved to head
			assert_eq!(Queue::<T>::get(1), None);

			// assert head item present
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2, 1, 0],
					maybe_pool_id: Some(0)
				})
			);

			next_block(true);
			assert_eq!(Head::<T>::get(), None,);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::Checking { stash: 1, eras: vec![3, 2, 1, 0] },
					Event::Unstaked {
						stash: 1,
						maybe_pool_id: Some(0),
						result: Err(DispatchError::Module(ModuleError {
							index: 4,
							error: [0, 0, 0, 0],
							message: None
						}))
					}
				]
			);
			assert_unstaked(&1);
		});
	}

	#[test]
	fn successful_unstake_all_eras_per_block() {
		ExtBuilder::default().build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(BondingDuration::get() + 1);
			CurrentEra::<T>::put(BondingDuration::get());

			// register for fast unstake
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), Some(1_u32)));
			assert_eq!(Queue::<T>::get(1), Some(Some(1)));

			// process on idle
			next_block(true);

			// assert queue item has been moved to head
			assert_eq!(Queue::<T>::get(1), None);

			// assert head item present
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2, 1, 0],
					maybe_pool_id: Some(1)
				})
			);

			next_block(true);
			assert_eq!(Head::<T>::get(), None,);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::Checking { stash: 1, eras: vec![3, 2, 1, 0] },
					Event::Unstaked { stash: 1, maybe_pool_id: Some(1), result: Ok(()) }
				]
			);
			assert_unstaked(&1);
			assert!(pallet_nomination_pools::PoolMembers::<T>::contains_key(&1));
		});
	}

	#[test]
	fn successful_unstake_one_era_per_block() {
		ExtBuilder::default().build_and_execute(|| {
			// put 1 era per block
			ErasToCheckPerBlock::<T>::put(1);
			CurrentEra::<T>::put(BondingDuration::get());

			// register for fast unstake
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), Some(1_u32)));
			assert_eq!(Queue::<T>::get(1), Some(Some(1)));

			// process on idle
			next_block(true);

			// assert queue item has been moved to head
			assert_eq!(Queue::<T>::get(1), None);

			// assert head item present
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest { stash: 1, checked: bounded_vec![3], maybe_pool_id: Some(1) })
			);

			next_block(true);

			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2],
					maybe_pool_id: Some(1)
				})
			);

			next_block(true);

			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2, 1],
					maybe_pool_id: Some(1)
				})
			);

			next_block(true);

			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2, 1, 0],
					maybe_pool_id: Some(1)
				})
			);

			next_block(true);

			assert_eq!(Head::<T>::get(), None,);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::Checking { stash: 1, eras: vec![3] },
					Event::Checking { stash: 1, eras: vec![2] },
					Event::Checking { stash: 1, eras: vec![1] },
					Event::Checking { stash: 1, eras: vec![0] },
					Event::Unstaked { stash: 1, maybe_pool_id: Some(1), result: Ok(()) }
				]
			);
			assert_unstaked(&1);
			assert!(pallet_nomination_pools::PoolMembers::<T>::contains_key(&1));
		});
	}

	#[test]
	fn old_checked_era_pruned() {
		// the only scenario where checked era pruning (checked.retain) comes handy is a follows:
		// the whole vector is full and at capacity and in the next call we are ready to unstake,
		// but then a new era happens.
		ExtBuilder::default().build_and_execute(|| {
			// given
			ErasToCheckPerBlock::<T>::put(1);
			CurrentEra::<T>::put(BondingDuration::get());

			// register for fast unstake
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), None));
			assert_eq!(Queue::<T>::get(1), Some(None));

			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest { stash: 1, checked: bounded_vec![3], maybe_pool_id: None })
			);

			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest { stash: 1, checked: bounded_vec![3, 2], maybe_pool_id: None })
			);

			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2, 1],
					maybe_pool_id: None
				})
			);

			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2, 1, 0],
					maybe_pool_id: None
				})
			);

			// when: a new era happens right before one is free.
			CurrentEra::<T>::put(CurrentEra::<T>::get().unwrap() + 1);
			ExtBuilder::register_stakers_for_era(CurrentEra::<T>::get().unwrap());

			// then
			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					// note era 0 is pruned to keep the vector length sane.
					checked: bounded_vec![3, 2, 1, 4],
					maybe_pool_id: None
				})
			);

			next_block(true);
			assert_eq!(Head::<T>::get(), None);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::Checking { stash: 1, eras: vec![3] },
					Event::Checking { stash: 1, eras: vec![2] },
					Event::Checking { stash: 1, eras: vec![1] },
					Event::Checking { stash: 1, eras: vec![0] },
					Event::Checking { stash: 1, eras: vec![4] },
					Event::Unstaked { stash: 1, maybe_pool_id: None, result: Ok(()) }
				]
			);
			assert_unstaked(&1);
		});
	}

	#[test]
	fn unstake_paused_mid_election() {
		ExtBuilder::default().build_and_execute(|| {
			// give: put 1 era per block
			ErasToCheckPerBlock::<T>::put(1);
			CurrentEra::<T>::put(BondingDuration::get());

			// register for fast unstake
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), Some(1_u32)));

			// process 2 blocks
			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest { stash: 1, checked: bounded_vec![3], maybe_pool_id: Some(1) })
			);

			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2],
					maybe_pool_id: Some(1)
				})
			);

			// when
			Ongoing::set(true);

			// then nothing changes
			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2],
					maybe_pool_id: Some(1)
				})
			);

			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2],
					maybe_pool_id: Some(1)
				})
			);

			// then we register a new era.
			Ongoing::set(false);
			CurrentEra::<T>::put(CurrentEra::<T>::get().unwrap() + 1);
			ExtBuilder::register_stakers_for_era(CurrentEra::<T>::get().unwrap());

			// then we can progress again, but notice that the new era that had to be checked.
			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2, 4],
					maybe_pool_id: Some(1)
				})
			);

			// progress to end
			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 1,
					checked: bounded_vec![3, 2, 4, 1],
					maybe_pool_id: Some(1)
				})
			);

			// but notice that we don't care about era 0 instead anymore! we're done.
			next_block(true);
			assert_eq!(Head::<T>::get(), None);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::Checking { stash: 1, eras: vec![3] },
					Event::Checking { stash: 1, eras: vec![2] },
					Event::Checking { stash: 1, eras: vec![4] },
					Event::Checking { stash: 1, eras: vec![1] },
					Event::Unstaked { stash: 1, maybe_pool_id: Some(1), result: Ok(()) }
				]
			);

			assert_unstaked(&1);
			assert!(pallet_nomination_pools::PoolMembers::<T>::contains_key(&1));
		});
	}

	#[test]
	fn exposed_nominator_cannot_unstake() {
		ExtBuilder::default().build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(1);
			SlashPerEra::set(7);
			CurrentEra::<T>::put(BondingDuration::get());

			// create an exposed nominator in era 1
			let exposed = 666 as AccountId;
			pallet_staking::ErasStakers::<T>::mutate(1, VALIDATORS_PER_ERA, |expo| {
				expo.others.push(IndividualExposure { who: exposed, value: 0 as Balance });
			});
			Balances::make_free_balance_be(&exposed, 100);
			assert_ok!(Staking::bond(
				RuntimeOrigin::signed(exposed),
				exposed,
				10,
				RewardDestination::Staked
			));
			assert_ok!(Staking::nominate(RuntimeOrigin::signed(exposed), vec![exposed]));

			// register the exposed one.
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(exposed), None));

			// a few blocks later, we realize they are slashed
			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: exposed,
					checked: bounded_vec![3],
					maybe_pool_id: None
				})
			);
			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: exposed,
					checked: bounded_vec![3, 2],
					maybe_pool_id: None
				})
			);
			next_block(true);
			assert_eq!(Head::<T>::get(), None);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				// we slash them by 21, since we checked 3 eras in total (3, 2, 1).
				vec![
					Event::Checking { stash: exposed, eras: vec![3] },
					Event::Checking { stash: exposed, eras: vec![2] },
					Event::Slashed { stash: exposed, amount: 3 * 7 }
				]
			);
		});
	}

	#[test]
	fn exposed_nominator_cannot_unstake_multi_check() {
		ExtBuilder::default().build_and_execute(|| {
			// same as the previous check, but we check 2 eras per block, and we make the exposed be
			// exposed in era 0, so that it is detected halfway in a check era.
			ErasToCheckPerBlock::<T>::put(2);
			SlashPerEra::set(7);
			CurrentEra::<T>::put(BondingDuration::get());

			// create an exposed nominator in era 1
			let exposed = 666 as AccountId;
			pallet_staking::ErasStakers::<T>::mutate(0, VALIDATORS_PER_ERA, |expo| {
				expo.others.push(IndividualExposure { who: exposed, value: 0 as Balance });
			});
			Balances::make_free_balance_be(&exposed, 100);
			assert_ok!(Staking::bond(
				RuntimeOrigin::signed(exposed),
				exposed,
				10,
				RewardDestination::Staked
			));
			assert_ok!(Staking::nominate(RuntimeOrigin::signed(exposed), vec![exposed]));

			// register the exposed one.
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(exposed), None));

			// a few blocks later, we realize they are slashed
			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: exposed,
					checked: bounded_vec![3, 2],
					maybe_pool_id: None
				})
			);
			next_block(true);
			assert_eq!(Head::<T>::get(), None);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				// we slash them by 28, since we checked 4 eras in total.
				vec![
					Event::Checking { stash: exposed, eras: vec![3, 2] },
					Event::Slashed { stash: exposed, amount: 4 * 7 }
				]
			);
		});
	}

	#[test]
	fn validators_cannot_bail() {
		ExtBuilder::default().build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(BondingDuration::get() + 1);
			CurrentEra::<T>::put(BondingDuration::get());

			// a validator switches role and register...
			assert_ok!(Staking::nominate(
				RuntimeOrigin::signed(VALIDATOR_PREFIX),
				vec![VALIDATOR_PREFIX]
			));
			assert_ok!(FastUnstake::register_fast_unstake(
				RuntimeOrigin::signed(VALIDATOR_PREFIX),
				None
			));

			// but they indeed are exposed!
			assert!(pallet_staking::ErasStakers::<T>::contains_key(
				BondingDuration::get() - 1,
				VALIDATOR_PREFIX
			));

			// process a block, this validator is exposed and has been slashed.
			next_block(true);
			assert_eq!(Head::<T>::get(), None);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![Event::Slashed { stash: 100, amount: 100 }]
			);
		});
	}

	#[test]
	fn unexposed_validator_can_fast_unstake() {
		ExtBuilder::default().build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(BondingDuration::get() + 1);
			CurrentEra::<T>::put(BondingDuration::get());

			// create a new validator that 100% not exposed.
			Balances::make_free_balance_be(&42, 100);
			assert_ok!(Staking::bond(RuntimeOrigin::signed(42), 42, 10, RewardDestination::Staked));
			assert_ok!(Staking::validate(RuntimeOrigin::signed(42), Default::default()));

			// let them register:
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(42), None));

			// 2 block's enough to unstake them.
			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stash: 42,
					checked: bounded_vec![3, 2, 1, 0],
					maybe_pool_id: None
				})
			);
			next_block(true);
			assert_eq!(Head::<T>::get(), None);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::Checking { stash: 42, eras: vec![3, 2, 1, 0] },
					Event::Unstaked { stash: 42, maybe_pool_id: None, result: Ok(()) }
				]
			);
		});
	}
}

mod signed_extension {
	use super::*;
	use sp_runtime::traits::SignedExtension;

	const STAKING_CALL: crate::mock::RuntimeCall =
		crate::mock::RuntimeCall::Staking(pallet_staking::Call::<T>::chill {});

	#[test]
	fn does_nothing_if_not_queued() {
		ExtBuilder::default().build_and_execute(|| {
			assert!(PreventStakingOpsIfUnbonding::<T>::new()
				.pre_dispatch(&1, &STAKING_CALL, &Default::default(), Default::default())
				.is_ok());
		})
	}

	#[test]
	fn prevents_queued() {
		ExtBuilder::default().build_and_execute(|| {
			// given: stash for 2 is 1.
			// when
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), None));

			// then
			// stash can't.
			assert!(PreventStakingOpsIfUnbonding::<T>::new()
				.pre_dispatch(&1, &STAKING_CALL, &Default::default(), Default::default())
				.is_err());

			// controller can't.
			assert!(PreventStakingOpsIfUnbonding::<T>::new()
				.pre_dispatch(&2, &STAKING_CALL, &Default::default(), Default::default())
				.is_err());
		})
	}

	#[test]
	fn prevents_head_stash() {
		ExtBuilder::default().build_and_execute(|| {
			// given: stash for 2 is 1.
			// when
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2), None));

			ErasToCheckPerBlock::<T>::put(1);
			CurrentEra::<T>::put(BondingDuration::get());
			next_block(true);

			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest { stash: 1, checked: bounded_vec![3], maybe_pool_id: None })
			);

			// then
			// stash can't
			assert!(PreventStakingOpsIfUnbonding::<T>::new()
				.pre_dispatch(&2, &STAKING_CALL, &Default::default(), Default::default())
				.is_err());

			// controller can't
			assert!(PreventStakingOpsIfUnbonding::<T>::new()
				.pre_dispatch(&1, &STAKING_CALL, &Default::default(), Default::default())
				.is_err());
		})
	}
}
