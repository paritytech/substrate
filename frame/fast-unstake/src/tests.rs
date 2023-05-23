// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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
use crate::{mock::*, types::*, Event};
use frame_support::{pallet_prelude::*, testing_prelude::*, traits::Currency};
use pallet_staking::{CurrentEra, RewardDestination};

use sp_runtime::traits::BadOrigin;
use sp_staking::StakingInterface;

#[test]
fn test_setup_works() {
	ExtBuilder::default().build_and_execute(|| {
		assert_eq!(Staking::bonding_duration(), 3);
	});
}

#[test]
fn register_works() {
	ExtBuilder::default().build_and_execute(|| {
		ErasToCheckPerBlock::<T>::put(1);
		// Controller account registers for fast unstake.
		assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));
		// Ensure stash is in the queue.
		assert_ne!(Queue::<T>::get(1), None);
	});
}

#[test]
fn register_insufficient_funds_fails() {
	use pallet_balances::Error as BalancesError;
	ExtBuilder::default().build_and_execute(|| {
		ErasToCheckPerBlock::<T>::put(1);
		<T as Config>::Currency::make_free_balance_be(&1, 3);

		// Controller account registers for fast unstake.
		assert_noop!(
			FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)),
			BalancesError::<T, _>::InsufficientBalance,
		);

		// Ensure stash is in the queue.
		assert_eq!(Queue::<T>::get(1), None);
	});
}

#[test]
fn register_disabled_fails() {
	ExtBuilder::default().build_and_execute(|| {
		assert_noop!(
			FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)),
			Error::<T>::CallNotAllowed
		);
	});
}

#[test]
fn cannot_register_if_not_bonded() {
	ExtBuilder::default().build_and_execute(|| {
		ErasToCheckPerBlock::<T>::put(1);
		// Mint accounts 1 and 2 with 200 tokens.
		for _ in 1..2 {
			let _ = Balances::make_free_balance_be(&1, 200);
		}
		// Attempt to fast unstake.
		assert_noop!(
			FastUnstake::register_fast_unstake(RuntimeOrigin::signed(2)),
			Error::<T>::NotController
		);
	});
}

#[test]
fn cannot_register_if_in_queue() {
	ExtBuilder::default().build_and_execute(|| {
		ErasToCheckPerBlock::<T>::put(1);
		// Insert some Queue item
		Queue::<T>::insert(1, 10);
		// Cannot re-register, already in queue
		assert_noop!(
			FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)),
			Error::<T>::AlreadyQueued
		);
	});
}

#[test]
fn cannot_register_if_head() {
	ExtBuilder::default().build_and_execute(|| {
		ErasToCheckPerBlock::<T>::put(1);
		// Insert some Head item for stash
		Head::<T>::put(UnstakeRequest {
			stashes: bounded_vec![(1, Deposit::get())],
			checked: bounded_vec![],
		});
		// Controller attempts to regsiter
		assert_noop!(
			FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)),
			Error::<T>::AlreadyHead
		);
	});
}

#[test]
fn cannot_register_if_has_unlocking_chunks() {
	ExtBuilder::default().build_and_execute(|| {
		ErasToCheckPerBlock::<T>::put(1);
		// Start unbonding half of staked tokens
		assert_ok!(Staking::unbond(RuntimeOrigin::signed(1), 50_u128));
		// Cannot register for fast unstake with unlock chunks active
		assert_noop!(
			FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)),
			Error::<T>::NotFullyBonded
		);
	});
}

#[test]
fn deregister_works() {
	ExtBuilder::default().build_and_execute(|| {
		ErasToCheckPerBlock::<T>::put(1);

		assert_eq!(<T as Config>::Currency::reserved_balance(&1), 0);

		// Controller account registers for fast unstake.
		assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));
		assert_eq!(<T as Config>::Currency::reserved_balance(&1), Deposit::get());

		// Controller then changes mind and deregisters.
		assert_ok!(FastUnstake::deregister(RuntimeOrigin::signed(1)));
		assert_eq!(<T as Config>::Currency::reserved_balance(&1), 0);

		// Ensure stash no longer exists in the queue.
		assert_eq!(Queue::<T>::get(1), None);
	});
}

#[test]
fn deregister_disabled_fails() {
	ExtBuilder::default().build_and_execute(|| {
		ErasToCheckPerBlock::<T>::put(1);
		assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));
		ErasToCheckPerBlock::<T>::put(0);
		assert_noop!(FastUnstake::deregister(RuntimeOrigin::signed(1)), Error::<T>::CallNotAllowed);
	});
}

#[test]
fn cannot_deregister_if_not_controller() {
	ExtBuilder::default().build_and_execute(|| {
		ErasToCheckPerBlock::<T>::put(1);
		// Controller (same as stash) account registers for fast unstake.
		assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));
		// Another account tries to deregister.
		assert_noop!(FastUnstake::deregister(RuntimeOrigin::signed(2)), Error::<T>::NotController);
	});
}

#[test]
fn cannot_deregister_if_not_queued() {
	ExtBuilder::default().build_and_execute(|| {
		ErasToCheckPerBlock::<T>::put(1);
		// Controller tries to deregister without first registering
		assert_noop!(FastUnstake::deregister(RuntimeOrigin::signed(1)), Error::<T>::NotQueued);
	});
}

#[test]
fn cannot_deregister_already_head() {
	ExtBuilder::default().build_and_execute(|| {
		ErasToCheckPerBlock::<T>::put(1);
		// Controller attempts to register, should fail
		assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));
		// Insert some Head item for stash.
		Head::<T>::put(UnstakeRequest {
			stashes: bounded_vec![(1, Deposit::get())],
			checked: bounded_vec![],
		});
		// Controller attempts to deregister
		assert_noop!(FastUnstake::deregister(RuntimeOrigin::signed(1)), Error::<T>::AlreadyHead);
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
		assert_noop!(FastUnstake::control(RuntimeOrigin::signed(2), 1_u32), BadOrigin);
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
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));
			assert_eq!(Queue::<T>::get(1), Some(Deposit::get()));

			// call on_idle with no remaining weight
			FastUnstake::on_idle(System::block_number(), Weight::from_parts(0, 0));

			// assert nothing changed in Queue and Head
			assert_eq!(Head::<T>::get(), None);
			assert_eq!(Queue::<T>::get(1), Some(Deposit::get()));
		});
	}

	#[test]
	fn if_head_not_set_one_random_fetched_from_queue() {
		ExtBuilder::default().build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(BondingDuration::get() + 1);
			CurrentEra::<T>::put(BondingDuration::get());

			// given
			assert_eq!(<T as Config>::Currency::reserved_balance(&1), 0);

			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(3)));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(5)));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(7)));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(9)));

			assert_eq!(<T as Config>::Currency::reserved_balance(&1), Deposit::get());

			assert_eq!(Queue::<T>::count(), 5);
			assert_eq!(Head::<T>::get(), None);

			// when
			next_block(true);

			// then
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3, 2, 1, 0]
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
					stashes: bounded_vec![(5, Deposit::get())],
					checked: bounded_vec![3, 2, 1, 0]
				}),
			);
			assert_eq!(Queue::<T>::count(), 3);

			assert_eq!(<T as Config>::Currency::reserved_balance(&1), 0);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::BatchChecked { eras: vec![3, 2, 1, 0] },
					Event::Unstaked { stash: 1, result: Ok(()) },
					Event::BatchFinished { size: 1 },
					Event::BatchChecked { eras: vec![3, 2, 1, 0] }
				]
			);
		});
	}

	#[docify::export]
	#[test]
	fn successful_multi_queue() {
		ExtBuilder::default().build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(BondingDuration::get() + 1);
			CurrentEra::<T>::put(BondingDuration::get());

			// register multi accounts for fast unstake
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));
			assert_eq!(Queue::<T>::get(1), Some(Deposit::get()));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(3)));
			assert_eq!(Queue::<T>::get(3), Some(Deposit::get()));

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
					Event::BatchChecked { eras: vec![3, 2, 1, 0] },
					Event::Unstaked { stash: 1, result: Ok(()) },
					Event::BatchFinished { size: 1 },
					Event::BatchChecked { eras: vec![3, 2, 1, 0] },
					Event::Unstaked { stash: 3, result: Ok(()) },
					Event::BatchFinished { size: 1 },
				]
			);

			assert_unstaked(&1);
			assert_unstaked(&3);
		});
	}

	#[docify::export]
	#[test]
	fn successful_unstake() {
		ExtBuilder::default().build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(BondingDuration::get() + 1);
			CurrentEra::<T>::put(BondingDuration::get());

			// register for fast unstake
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));
			assert_eq!(Queue::<T>::get(1), Some(Deposit::get()));

			// process on idle
			next_block(true);

			// assert queue item has been moved to head
			assert_eq!(Queue::<T>::get(1), None);

			// assert head item present
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3, 2, 1, 0]
				})
			);

			next_block(true);
			assert_eq!(Head::<T>::get(), None,);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::BatchChecked { eras: vec![3, 2, 1, 0] },
					Event::Unstaked { stash: 1, result: Ok(()) },
					Event::BatchFinished { size: 1 }
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

			Balances::make_free_balance_be(&2, 100);

			// register for fast unstake
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));
			assert_eq!(Queue::<T>::get(1), Some(Deposit::get()));

			// process on idle
			next_block(true);

			// assert queue item has been moved to head
			assert_eq!(Queue::<T>::get(1), None);

			// assert head item present
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3, 2, 1, 0]
				})
			);

			next_block(true);
			assert_eq!(Head::<T>::get(), None,);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::BatchChecked { eras: vec![3, 2, 1, 0] },
					Event::Unstaked { stash: 1, result: Ok(()) },
					Event::BatchFinished { size: 1 }
				]
			);
			assert_unstaked(&1);
		});
	}

	#[test]
	fn successful_unstake_one_era_per_block() {
		ExtBuilder::default().build_and_execute(|| {
			// put 1 era per block
			ErasToCheckPerBlock::<T>::put(1);
			CurrentEra::<T>::put(BondingDuration::get());

			// register for fast unstake
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));
			assert_eq!(Queue::<T>::get(1), Some(Deposit::get()));

			// process on idle
			next_block(true);

			// assert queue item has been moved to head
			assert_eq!(Queue::<T>::get(1), None);

			// assert head item present
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3]
				})
			);

			next_block(true);

			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3, 2]
				})
			);

			next_block(true);

			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3, 2, 1]
				})
			);

			next_block(true);

			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3, 2, 1, 0]
				})
			);

			next_block(true);

			assert_eq!(Head::<T>::get(), None,);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::BatchChecked { eras: vec![3] },
					Event::BatchChecked { eras: vec![2] },
					Event::BatchChecked { eras: vec![1] },
					Event::BatchChecked { eras: vec![0] },
					Event::Unstaked { stash: 1, result: Ok(()) },
					Event::BatchFinished { size: 1 }
				]
			);
			assert_unstaked(&1);
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
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));
			assert_eq!(Queue::<T>::get(1), Some(Deposit::get()));

			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3]
				})
			);

			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3, 2]
				})
			);

			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3, 2, 1]
				})
			);

			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3, 2, 1, 0]
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
					stashes: bounded_vec![(1, Deposit::get())],
					// note era 0 is pruned to keep the vector length sane.
					checked: bounded_vec![3, 2, 1, 4],
				})
			);

			next_block(true);
			assert_eq!(Head::<T>::get(), None);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::BatchChecked { eras: vec![3] },
					Event::BatchChecked { eras: vec![2] },
					Event::BatchChecked { eras: vec![1] },
					Event::BatchChecked { eras: vec![0] },
					Event::BatchChecked { eras: vec![4] },
					Event::Unstaked { stash: 1, result: Ok(()) },
					Event::BatchFinished { size: 1 }
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
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));

			// process 2 blocks
			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3]
				})
			);

			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3, 2]
				})
			);

			// when
			Ongoing::set(true);

			// then nothing changes
			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3, 2]
				})
			);

			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3, 2]
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
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3, 2, 4]
				})
			);

			// progress to end
			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get())],
					checked: bounded_vec![3, 2, 4, 1]
				})
			);

			// but notice that we don't care about era 0 instead anymore! we're done.
			next_block(true);
			assert_eq!(Head::<T>::get(), None);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::BatchChecked { eras: vec![3] },
					Event::BatchChecked { eras: vec![2] },
					Event::BatchChecked { eras: vec![4] },
					Event::BatchChecked { eras: vec![1] },
					Event::Unstaked { stash: 1, result: Ok(()) },
					Event::BatchFinished { size: 1 }
				]
			);

			assert_unstaked(&1);
		});
	}

	#[docify::export]
	#[test]
	fn exposed_nominator_cannot_unstake() {
		ExtBuilder::default().build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(1);
			CurrentEra::<T>::put(BondingDuration::get());

			// create an exposed nominator in era 1
			let exposed = 666;
			create_exposed_nominator(exposed, 1);

			// a few blocks later, we realize they are slashed
			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(exposed, Deposit::get())],
					checked: bounded_vec![3]
				})
			);
			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(exposed, Deposit::get())],
					checked: bounded_vec![3, 2]
				})
			);
			next_block(true);
			assert_eq!(Head::<T>::get(), None);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::BatchChecked { eras: vec![3] },
					Event::BatchChecked { eras: vec![2] },
					Event::Slashed { stash: exposed, amount: Deposit::get() },
					Event::BatchFinished { size: 0 }
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
			CurrentEra::<T>::put(BondingDuration::get());

			// create an exposed nominator in era 0
			let exposed = 666;
			create_exposed_nominator(exposed, 0);

			// a few blocks later, we realize they are slashed
			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(exposed, Deposit::get())],
					checked: bounded_vec![3, 2]
				})
			);
			next_block(true);
			assert_eq!(Head::<T>::get(), None);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				// we slash them
				vec![
					Event::BatchChecked { eras: vec![3, 2] },
					Event::Slashed { stash: exposed, amount: Deposit::get() },
					Event::BatchFinished { size: 0 }
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
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(VALIDATOR_PREFIX)));

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
				vec![
					Event::Slashed { stash: 100, amount: Deposit::get() },
					Event::BatchFinished { size: 0 }
				]
			);
		});
	}

	#[test]
	fn unexposed_validator_can_fast_unstake() {
		ExtBuilder::default().build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(BondingDuration::get() + 1);
			CurrentEra::<T>::put(BondingDuration::get());

			// create a new validator that 100% not exposed.
			Balances::make_free_balance_be(&42, 100 + Deposit::get());
			assert_ok!(Staking::bond(RuntimeOrigin::signed(42), 10, RewardDestination::Staked));
			assert_ok!(Staking::validate(RuntimeOrigin::signed(42), Default::default()));

			// let them register:
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(42)));

			// 2 block's enough to unstake them.
			next_block(true);
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(42, Deposit::get())],
					checked: bounded_vec![3, 2, 1, 0]
				})
			);
			next_block(true);
			assert_eq!(Head::<T>::get(), None);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::BatchChecked { eras: vec![3, 2, 1, 0] },
					Event::Unstaked { stash: 42, result: Ok(()) },
					Event::BatchFinished { size: 1 }
				]
			);
		});
	}
}

mod batched {
	use super::*;

	#[test]
	fn single_block_batched_successful() {
		ExtBuilder::default().batch(3).build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(BondingDuration::get() + 1);
			CurrentEra::<T>::put(BondingDuration::get());

			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(3)));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(5)));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(7)));

			assert_eq!(Queue::<T>::count(), 4);
			assert_eq!(Head::<T>::get(), None);

			// when
			next_block(true);

			// then
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![
						(1, Deposit::get()),
						(5, Deposit::get()),
						(7, Deposit::get())
					],
					checked: bounded_vec![3, 2, 1, 0]
				})
			);
			assert_eq!(Queue::<T>::count(), 1);

			// when
			next_block(true);

			// then
			assert_eq!(Head::<T>::get(), None);
			assert_eq!(Queue::<T>::count(), 1);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::BatchChecked { eras: vec![3, 2, 1, 0] },
					Event::Unstaked { stash: 1, result: Ok(()) },
					Event::Unstaked { stash: 5, result: Ok(()) },
					Event::Unstaked { stash: 7, result: Ok(()) },
					Event::BatchFinished { size: 3 }
				]
			);
		});
	}

	#[test]
	fn multi_block_batched_successful() {
		ExtBuilder::default().batch(3).build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(2);
			CurrentEra::<T>::put(BondingDuration::get());

			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(3)));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(5)));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(7)));

			assert_eq!(Queue::<T>::count(), 4);
			assert_eq!(Head::<T>::get(), None);

			// when
			next_block(true);

			// then
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![
						(1, Deposit::get()),
						(5, Deposit::get()),
						(7, Deposit::get())
					],
					checked: bounded_vec![3, 2]
				})
			);

			// when
			next_block(true);

			// then
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![
						(1, Deposit::get()),
						(5, Deposit::get()),
						(7, Deposit::get())
					],
					checked: bounded_vec![3, 2, 1, 0]
				})
			);

			// when
			next_block(true);

			// then
			assert_eq!(Head::<T>::get(), None);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::BatchChecked { eras: vec![3, 2] },
					Event::BatchChecked { eras: vec![1, 0] },
					Event::Unstaked { stash: 1, result: Ok(()) },
					Event::Unstaked { stash: 5, result: Ok(()) },
					Event::Unstaked { stash: 7, result: Ok(()) },
					Event::BatchFinished { size: 3 }
				]
			);
		});
	}

	#[test]
	fn multi_block_batched_some_fail() {
		ExtBuilder::default().batch(4).build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(2);
			CurrentEra::<T>::put(BondingDuration::get());

			// register two good ones.
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(3)));
			create_exposed_nominator(666, 1);
			create_exposed_nominator(667, 3);

			// then
			assert_eq!(Queue::<T>::count(), 4);
			assert_eq!(Head::<T>::get(), None);

			// when
			next_block(true);

			// then
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![
						(1, Deposit::get()),
						(3, Deposit::get()),
						(666, Deposit::get())
					],
					checked: bounded_vec![3, 2]
				})
			);

			// when
			next_block(true);

			// then
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get()), (3, Deposit::get()),],
					checked: bounded_vec![3, 2, 1, 0]
				})
			);

			// when
			next_block(true);

			// then
			assert_eq!(Head::<T>::get(), None);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::Slashed { stash: 667, amount: 7 },
					Event::BatchChecked { eras: vec![3, 2] },
					Event::Slashed { stash: 666, amount: 7 },
					Event::BatchChecked { eras: vec![1, 0] },
					Event::Unstaked { stash: 1, result: Ok(()) },
					Event::Unstaked { stash: 3, result: Ok(()) },
					Event::BatchFinished { size: 2 }
				]
			);
		});
	}

	#[test]
	fn multi_block_batched_all_fail_early_exit() {
		ExtBuilder::default().batch(2).build_and_execute(|| {
			ErasToCheckPerBlock::<T>::put(1);
			CurrentEra::<T>::put(BondingDuration::get());

			// register two bad ones.
			create_exposed_nominator(666, 3);
			create_exposed_nominator(667, 2);

			// then
			assert_eq!(Queue::<T>::count(), 2);
			assert_eq!(Head::<T>::get(), None);

			// when we progress a block..
			next_block(true);

			// ..and register two good ones.
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(1)));
			assert_ok!(FastUnstake::register_fast_unstake(RuntimeOrigin::signed(3)));

			// then one of the bad ones is reaped.
			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(667, Deposit::get())],
					checked: bounded_vec![3]
				})
			);

			// when we go to next block
			next_block(true);

			// then the head is empty, we early terminate the batch.
			assert_eq!(Head::<T>::get(), None);

			// upon next block, we will assemble a new head.
			next_block(true);

			assert_eq!(
				Head::<T>::get(),
				Some(UnstakeRequest {
					stashes: bounded_vec![(1, Deposit::get()), (3, Deposit::get()),],
					checked: bounded_vec![3]
				})
			);

			assert_eq!(
				fast_unstake_events_since_last_call(),
				vec![
					Event::Slashed { stash: 666, amount: Deposit::get() },
					Event::BatchChecked { eras: vec![3] },
					Event::Slashed { stash: 667, amount: Deposit::get() },
					Event::BatchFinished { size: 0 },
					Event::BatchChecked { eras: vec![3] }
				]
			);
		});
	}
}

#[test]
fn kusama_estimate() {
	use crate::WeightInfo;
	let block_time = frame_support::weights::Weight::from_parts(
		frame_support::weights::constants::WEIGHT_REF_TIME_PER_SECOND * 2,
		0,
	)
	.ref_time() as f32;
	let on_idle = crate::weights::SubstrateWeight::<T>::on_idle_check(1000, 64).ref_time() as f32;
	dbg!(block_time, on_idle, on_idle / block_time);
}

#[test]
fn polkadot_estimate() {
	use crate::WeightInfo;
	let block_time = frame_support::weights::Weight::from_parts(
		frame_support::weights::constants::WEIGHT_REF_TIME_PER_SECOND * 2,
		0,
	)
	.ref_time() as f32;
	let on_idle = crate::weights::SubstrateWeight::<T>::on_idle_check(300, 64).ref_time() as f32;
	dbg!(block_time, on_idle, on_idle / block_time);
}
