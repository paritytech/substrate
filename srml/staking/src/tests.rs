// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Tests for the module.

#![cfg(test)]

use super::*;
use runtime_io::with_externalities;
use srml_support::{assert_ok, assert_noop, EnumerableStorageMap};
use mock::{Balances, Session, Staking, System, Timestamp, Test, ExtBuilder, Origin};
use srml_support::traits::Currency;

#[test]
fn basic_setup_works() {
	// Verifies initial conditions of mock
	with_externalities(&mut ExtBuilder::default().build(),
	|| {
		assert_eq!(Staking::bonded(&11), Some(10)); // Account 11 is stashed and locked, and account 10 is the controller
		assert_eq!(Staking::bonded(&21), Some(20)); // Account 21 is stashed and locked, and account 20 is the controller
		assert_eq!(Staking::bonded(&1), None);		// Account 1 is not a stashed

		// Account 10 controls the stash from account 11, which is 100 * balance_factor units
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1000, active: 1000, unlocking: vec![] }));
		// Account 20 controls the stash from account 21, which is 200 * balance_factor units
		assert_eq!(Staking::ledger(&20), Some(StakingLedger { stash: 21, total: 2000, active: 2000, unlocking: vec![] }));
		// Account 1 does not control any stash
		assert_eq!(Staking::ledger(&1), None);

		// ValidatorPrefs are default, thus unstake_threshold is 3, other values are default for their type
		assert_eq!(<Validators<Test>>::enumerate().collect::<Vec<_>>(), vec![
			(20, ValidatorPrefs { unstake_threshold: 3, validator_payment: 0 }),
			(10, ValidatorPrefs { unstake_threshold: 3, validator_payment: 0 })
		]);

		// Account 10 is exposed by 100 * balance_factor from their own stash in account 11
		assert_eq!(Staking::stakers(10), Exposure { total: 1000, own: 1000, others: vec![] });
		assert_eq!(Staking::stakers(20), Exposure { total: 2000, own: 2000, others: vec![] });
	});
}


#[test]
fn note_null_offline_should_work() {
	// Test the staking module works when no validators are offline
	with_externalities(&mut ExtBuilder::default().build(),
	|| {
		// Slashing begins for validators immediately if found offline
		assert_eq!(Staking::offline_slash_grace(), 0);
		// Account 10 has not been reported offline
		assert_eq!(Staking::slash_count(&10), 0);
		// Account 10 has `balance_factor` free balance
		assert_eq!(Balances::free_balance(&10), 1);
		// Nothing happens to Account 10, as expected
		assert_eq!(Staking::slash_count(&10), 0);
		assert_eq!(Balances::free_balance(&10), 1);
		// New era is not being forced
		assert!(Staking::forcing_new_era().is_none());
	});
}

#[test]
fn invulnerability_should_work() {
	// Test that users can be invulnerable from slashing or being kicked
	with_externalities(&mut ExtBuilder::default().build(),
	|| {
		// Make account 10 invulnerable
		assert_ok!(Staking::set_invulnerables(vec![10]));
		// Give account 10 some funds
		Balances::set_free_balance(&10, 70);
		// There is no slash grade period
		assert_eq!(Staking::offline_slash_grace(), 0);
		// Account 10 has not been slashed
		assert_eq!(Staking::slash_count(&10), 0);
		// Account 10 has the 70 funds we gave it above
		assert_eq!(Balances::free_balance(&10), 70);
		// Set account 10 as an offline validator, should exit early if invulnerable
		Staking::on_offline_validator(10, 1);
		// Show that account 10 has not been touched
		assert_eq!(Staking::slash_count(&10), 0);
		assert_eq!(Balances::free_balance(&10), 70);
		// New era not being forced
		assert!(Staking::forcing_new_era().is_none());
	});
}

#[test]
fn note_offline_should_work() {
	// Test that an offline validator gets slashed
	// TODO: Confirm how much exponential factor should effect
	with_externalities(&mut ExtBuilder::default().build(), || {
		// Give account 10 some balance
		Balances::set_free_balance(&10, 1000);
		println!("Stash Balance: {:?}", Balances::free_balance(&11));
		// Validators get slashed immediately
		assert_eq!(Staking::offline_slash_grace(), 0);
		// Unstake threshold is 3
		assert_eq!(Staking::validators(&10).unstake_threshold, 3);
		// Account 10 has not been slashed before
		assert_eq!(Staking::slash_count(&10), 0);
		// Account 10 has the funds we just gave it
		assert_eq!(Balances::free_balance(&10), 1000);
		// Report account 10 as offline, one greater than unstake threshold
		Staking::on_offline_validator(10, 4);
		// Confirm user has been reported
		assert_eq!(Staking::slash_count(&10), 4);
		// Confirm balance has been reduced by 2^unstake_threshold * current_offline_slash()
		assert_eq!(Balances::free_balance(&10), 1000 - 2_u64.pow(3) * 20);
		// A new era is forced due to slashing
		assert!(Staking::forcing_new_era().is_some());
		println!("Stash Balance After: {:?}", Balances::free_balance(&11));

	});
}

#[test]
fn note_offline_exponent_should_work() {
	// Test that slashing penalty for offline increases exponentially
	with_externalities(&mut ExtBuilder::default().build(), || {
		// Give account 10 some balance
		Balances::set_free_balance(&10, 1000);
		// Confirm initial conditions
		assert_eq!(Staking::offline_slash_grace(), 0);
		assert_eq!(Staking::slash_count(&10), 0);
		assert_eq!(Balances::free_balance(&10), 1000);
		// Have validator be offline < unstake_threshold
		Staking::on_offline_validator(10, 2);
		// No change other than slash_count
		assert_eq!(Staking::slash_count(&10), 2);
		assert_eq!(Balances::free_balance(&10), 1000);
		// Have validator be offline == unstake_threshold
		Staking::on_offline_validator(10, 1);
		// Slashed
		let new_free_balance_1 = 1000 - 2_u64.pow(3) * 20;
		assert_eq!(Balances::free_balance(&10), new_free_balance_1);
		// New era is forced without the validator due to slashing
		assert!(!<Validators<Test>>::exists(&10));
		assert!(Staking::forcing_new_era().is_some());
	});
}

// #[test]
// fn note_offline_grace_should_work() {
// 	with_externalities(&mut new_test_ext(0, 3, 3, 0, true, 10), || {
// 		Balances::set_free_balance(&10, 70);
// 		Balances::set_free_balance(&20, 70);
// 		assert_ok!(Staking::set_offline_slash_grace(1));
// 		assert_eq!(Staking::offline_slash_grace(), 1);

// 		assert_eq!(Staking::slash_count(&10), 0);
// 		assert_eq!(Balances::free_balance(&10), 70);

// 		System::set_extrinsic_index(1);
// 		Staking::on_offline_validator(10, 1);
// 		assert_eq!(Staking::slash_count(&10), 1);
// 		assert_eq!(Balances::free_balance(&10), 70);
// 		assert_eq!(Staking::slash_count(&20), 0);
// 		assert_eq!(Balances::free_balance(&20), 70);

// 		System::set_extrinsic_index(1);
// 		Staking::on_offline_validator(10, 1);
// 		Staking::on_offline_validator(20, 1);
// 		assert_eq!(Staking::slash_count(&10), 2);
// 		assert_eq!(Balances::free_balance(&10), 50);
// 		assert_eq!(Staking::slash_count(&20), 1);
// 		assert_eq!(Balances::free_balance(&20), 70);
// 		assert!(Staking::forcing_new_era().is_none());
// 	});
// }

// #[test]
// fn note_offline_force_unstake_session_change_should_work() {
// 	with_externalities(&mut new_test_ext(0, 3, 3, 0, true, 10), || {
// 		Balances::set_free_balance(&10, 70);
// 		Balances::set_free_balance(&20, 70);
// 		assert_ok!(Staking::stake(Origin::signed(1)));

// 		assert_eq!(Staking::slash_count(&10), 0);
// 		assert_eq!(Balances::free_balance(&10), 70);
// 		assert_eq!(Staking::intentions(), vec![10, 20, 1]);
// 		assert_eq!(Session::validators(), vec![10, 20]);

// 		System::set_extrinsic_index(1);
// 		Staking::on_offline_validator(10, 1);
// 		assert_eq!(Balances::free_balance(&10), 50);
// 		assert_eq!(Staking::slash_count(&10), 1);
// 		assert_eq!(Staking::intentions(), vec![10, 20, 1]);

// 		System::set_extrinsic_index(1);
// 		Staking::on_offline_validator(10, 1);
// 		assert_eq!(Staking::intentions(), vec![1, 20]);
// 		assert_eq!(Balances::free_balance(&10), 10);
// 		assert!(Staking::forcing_new_era().is_some());
// 	});
// }

// #[test]
// fn note_offline_auto_unstake_session_change_should_work() {
// 	with_externalities(&mut new_test_ext(0, 3, 3, 0, true, 10), || {
// 		Balances::set_free_balance(&10, 7000);
// 		Balances::set_free_balance(&20, 7000);
// 		assert_ok!(Staking::register_preferences(Origin::signed(10), 0, ValidatorPrefs { unstake_threshold: 1, validator_payment: 0 }));

// 		assert_eq!(Staking::intentions(), vec![10, 20]);

// 		System::set_extrinsic_index(1);
// 		Staking::on_offline_validator(10, 1);
// 		Staking::on_offline_validator(20, 1);
// 		assert_eq!(Balances::free_balance(&10), 6980);
// 		assert_eq!(Balances::free_balance(&20), 6980);
// 		assert_eq!(Staking::intentions(), vec![10, 20]);
// 		assert!(Staking::forcing_new_era().is_none());

// 		System::set_extrinsic_index(1);
// 		Staking::on_offline_validator(10, 1);
// 		Staking::on_offline_validator(20, 1);
// 		assert_eq!(Balances::free_balance(&10), 6940);
// 		assert_eq!(Balances::free_balance(&20), 6940);
// 		assert_eq!(Staking::intentions(), vec![20]);
// 		assert!(Staking::forcing_new_era().is_some());

// 		System::set_extrinsic_index(1);
// 		Staking::on_offline_validator(20, 1);
// 		assert_eq!(Balances::free_balance(&10), 6940);
// 		assert_eq!(Balances::free_balance(&20), 6860);
// 		assert_eq!(Staking::intentions(), vec![20]);

// 		System::set_extrinsic_index(1);
// 		Staking::on_offline_validator(20, 1);
// 		assert_eq!(Balances::free_balance(&10), 6940);
// 		assert_eq!(Balances::free_balance(&20), 6700);
// 		assert_eq!(Staking::intentions(), vec![0u64; 0]);
// 	});
// }



#[test]
fn multi_era_reward_should_work() {
	// FIXME: possibly either extend this (or make a new test) to at least another cover two eras 
	// (can fast-forward to the end) and test/verify the logic of the new <CurrentSessionReward> value mutated at 
	// the end of the era. e.g:
	unimplemented!();
}

#[test]
fn rewards_should_work() {
	// should check that: 
	// 1)rewards get recorded per session 2)rewards get paid per Era
	with_externalities(&mut ExtBuilder::default().build(), 
	|| {
		// Initial config should be correct
		assert_eq!(Staking::era_length(), 9);
		assert_eq!(Staking::sessions_per_era(), 3);
		assert_eq!(Staking::last_era_length_change(), 0);
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 0);

		// check the balance of a validator accounts.
		assert_eq!(Balances::total_balance(&10), 1); 

		// Block 3 => Session 1 => Era 0
		System::set_block_number(3);
		Timestamp::set_timestamp(15);	// on time.
		Session::check_rotate_session(System::block_number()); // QUESTIONS: why this matters ?
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 1);

		// session triggered: the reward value stashed should be 10 -- defined in ExtBuilder genesis.
		assert_eq!(Staking::current_session_reward(), 10);
		assert_eq!(Staking::current_era_reward(), 10);
		
		// Block 6 => Session 2 => Era 0 
		System::set_block_number(6);
		Timestamp::set_timestamp(32);	// a little late.
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 2);

		// session reward is the same,
		assert_eq!(Staking::current_session_reward(), 10);
		// though 2 will be deducted while stashed in the era reward due to delay
		assert_eq!(Staking::current_era_reward(), 18);

		// Block 6 => Session 3 => Era 1
		System::set_block_number(9);
		Timestamp::set_timestamp(45);  // back to being punktlisch. no delayss
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 1);
		assert_eq!(Session::current_index(), 3);

		// 1 + sum of of the session rewards accumulated
		assert_eq!(Balances::total_balance(&10), 1 + 10 + 10 + 8);
	});
}

#[test]
fn staking_should_work() {
	// should test: 
	// * new validators can be added to the default set
	// * new ones will be chosen per era (+ based on phragmen)
	// * either one can unlock the stash and back-down from being a validator.
	with_externalities(&mut ExtBuilder::default().session_length(1).build(), || {
		assert_eq!(Staking::era_length(), 3);
		assert_eq!(Staking::validator_count(), 2);
		// remember + compare this along with the test.
		assert_eq!(Session::validators(), vec![10, 20]);

		assert_ok!(Staking::set_bonding_duration(2));
		assert_eq!(Staking::bonding_duration(), 2);


		// --- Block 1: 
		System::set_block_number(1);
		// 2 entities will state interest in validating
		// account 1 controlled by 2, account 3 controlled by 4.
		// 4 is stashing a lot more than 2 and even 10, it will become a validator.
		// initial stakers: vec![(11, 10, balance_factor * 100), (21, 20, balance_factor * 200)],
		assert_ok!(Staking::bond(Origin::signed(1), 2, 5, RewardDestination::Stash));  // balance of 1 = 10, stashed = 5 
		assert_ok!(Staking::bond(Origin::signed(3), 4, 150, RewardDestination::Stash)); // balance of 3 = 300, stashed = 150 
		
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 0);
		// No effects will be seen so far.
		assert_eq!(Session::validators(), vec![10, 20]);
		

		// --- Block 2: 
		System::set_block_number(2);
		// Explicitly state the desire to validate for all of them.
		// note that the controller account will state interest as representative of the stash-controller pair.
		assert_ok!(Staking::validate(Origin::signed(2), ValidatorPrefs { unstake_threshold: 3, validator_payment: 0 }));
		assert_ok!(Staking::validate(Origin::signed(4), ValidatorPrefs { unstake_threshold: 3, validator_payment: 0 }));

		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 0);
		// No effects will be seen so far. Era has not been yet triggered.
		assert_eq!(Session::validators(), vec![10, 20]);


		// --- Block 3: the validators will now change. 
		System::set_block_number(3);
		Session::check_rotate_session(System::block_number());

		// FIXME: the assertion in the section should be changed to something in sync with how phragmen works.
		// for now just check that some arbitrary "two validators" have been chosen.
		assert_eq!(Session::validators().len(), 2);
		assert_eq!(Session::validators(), vec![10, 20]); // temporary. sorted by total staked value.
		assert_eq!(Staking::current_era(), 1);


		// --- Block 4: Unstake 4 as a validator, freeing up the balance stashed in 3
		System::set_block_number(4);

		// unlock the entire stashed value.
		Staking::unbond(Origin::signed(4), Staking::ledger(&4).unwrap().active).unwrap();
		
		Session::check_rotate_session(System::block_number());
		// nothing should be changed so far.
		assert_eq!(Session::validators(), vec![10, 20]);
		assert_eq!(Staking::current_era(), 1);
		
		
		// --- Block 5: nothing. 4 is still there. 
		System::set_block_number(5);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::validators(), vec![10, 20]); 
		assert_eq!(Staking::current_era(), 1);


		// --- Block 6: 4 will be not be a validator as it has nothing in stash.
		System::set_block_number(6);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::validators().contains(&4), false); 
		println!("New validators (which should not have 4) are {:?}", Session::validators());
	});
}


// #[test]
// fn nominating_and_rewards_should_work() {
// 	with_externalities(&mut new_test_ext(0, 1, 1, 0, true, 10), || {
// 		assert_eq!(Staking::era_length(), 1);
// 		assert_eq!(Staking::validator_count(), 2);
// 		assert_eq!(Staking::bonding_duration(), 3);
// 		assert_eq!(Session::validators(), vec![10, 20]);

// 		System::set_block_number(1);
// 		assert_ok!(Staking::stake(Origin::signed(1)));
// 		assert_ok!(Staking::stake(Origin::signed(2)));
// 		assert_ok!(Staking::stake(Origin::signed(3)));
// 		assert_ok!(Staking::nominate(Origin::signed(4), 1));
// 		Session::check_rotate_session(System::block_number());
// 		assert_eq!(Staking::current_era(), 1);
// 		assert_eq!(Session::validators(), vec![1, 3]);	// 4 + 1, 3
// 		assert_eq!(Balances::total_balance(&1), 10);
// 		assert_eq!(Balances::total_balance(&2), 20);
// 		assert_eq!(Balances::total_balance(&3), 30);
// 		assert_eq!(Balances::total_balance(&4), 40);

// 		System::set_block_number(2);
// 		assert_ok!(Staking::unnominate(Origin::signed(4), 0));
// 		Session::check_rotate_session(System::block_number());
// 		assert_eq!(Staking::current_era(), 2);
// 		assert_eq!(Session::validators(), vec![3, 2]);
// 		assert_eq!(Balances::total_balance(&1), 16);
// 		assert_eq!(Balances::total_balance(&2), 20);
// 		assert_eq!(Balances::total_balance(&3), 60);
// 		assert_eq!(Balances::total_balance(&4), 64);

// 		System::set_block_number(3);
// 		assert_ok!(Staking::stake(Origin::signed(4)));
// 		assert_ok!(Staking::unstake(Origin::signed(3), (Staking::intentions().iter().position(|&x| x == 3).unwrap() as u32).into()));
// 		assert_ok!(Staking::nominate(Origin::signed(3), 1));
// 		Session::check_rotate_session(System::block_number());
// 		assert_eq!(Session::validators(), vec![1, 4]);
// 		assert_eq!(Balances::total_balance(&1), 16);
// 		assert_eq!(Balances::total_balance(&2), 40);
// 		assert_eq!(Balances::total_balance(&3), 80);
// 		assert_eq!(Balances::total_balance(&4), 64);

// 		System::set_block_number(4);
// 		Session::check_rotate_session(System::block_number());
// 		assert_eq!(Balances::total_balance(&1), 26);
// 		assert_eq!(Balances::total_balance(&2), 40);
// 		assert_eq!(Balances::total_balance(&3), 133);
// 		assert_eq!(Balances::total_balance(&4), 128);
// 	});
// }

// #[test]
// fn rewards_with_off_the_table_should_work() {
// 	with_externalities(&mut new_test_ext(0, 1, 1, 0, true, 10), || {
// 		System::set_block_number(1);
// 		assert_ok!(Staking::stake(Origin::signed(1)));
// 		assert_ok!(Staking::nominate(Origin::signed(2), 1));
// 		assert_ok!(Staking::stake(Origin::signed(3)));
// 		Session::check_rotate_session(System::block_number());
// 		assert_eq!(Session::validators(), vec![1, 3]);	// 1 + 2, 3
// 		assert_eq!(Balances::total_balance(&1), 10);
// 		assert_eq!(Balances::total_balance(&2), 20);
// 		assert_eq!(Balances::total_balance(&3), 30);

// 		System::set_block_number(2);
// 		assert_ok!(Staking::register_preferences(
// 			Origin::signed(1),
// 			(Staking::intentions().into_iter().position(|i| i == 1).unwrap() as u32).into(),
// 			ValidatorPrefs { unstake_threshold: 3, validator_payment: 4 }
// 		));
// 		Session::check_rotate_session(System::block_number());
// 		assert_eq!(Balances::total_balance(&1), 22);
// 		assert_eq!(Balances::total_balance(&2), 37);
// 		assert_eq!(Balances::total_balance(&3), 60);
// 	});
// }

// #[test]
// fn nominating_slashes_should_work() {
// 	with_externalities(&mut new_test_ext(0, 2, 2, 0, true, 10), || {
// 		assert_eq!(Staking::era_length(), 4);
// 		assert_eq!(Staking::validator_count(), 2);
// 		assert_eq!(Staking::bonding_duration(), 12);
// 		assert_eq!(Session::validators(), vec![10, 20]);

// 		System::set_block_number(2);
// 		Session::check_rotate_session(System::block_number());

// 		Timestamp::set_timestamp(15);
// 		System::set_block_number(4);
// 		assert_ok!(Staking::stake(Origin::signed(1)));
// 		assert_ok!(Staking::stake(Origin::signed(3)));
// 		assert_ok!(Staking::nominate(Origin::signed(2), 3));
// 		assert_ok!(Staking::nominate(Origin::signed(4), 1));
// 		Session::check_rotate_session(System::block_number());

// 		assert_eq!(Staking::current_era(), 1);
// 		assert_eq!(Session::validators(), vec![1, 3]);	// 1 + 4, 3 + 2
// 		assert_eq!(Balances::total_balance(&1), 10);
// 		assert_eq!(Balances::total_balance(&2), 20);
// 		assert_eq!(Balances::total_balance(&3), 30);
// 		assert_eq!(Balances::total_balance(&4), 40);

// 		System::set_block_number(5);
// 		System::set_extrinsic_index(1);
// 		Staking::on_offline_validator(1, 1);
// 		Staking::on_offline_validator(3, 1);
// 		assert_eq!(Balances::total_balance(&1), 0);			//slashed
// 		assert_eq!(Balances::total_balance(&2), 20);		//not slashed
// 		assert_eq!(Balances::total_balance(&3), 10);		//slashed
// 		assert_eq!(Balances::total_balance(&4), 30);		//slashed
// 	});
// }

#[test]
fn double_staking_should_fail() {
	// should test (in the same order):
	// * an account already bonded as controller CAN be reused as the controller of another account.
	// * an account already bonded as stash cannot be the controller of another account.
	// * an account already bonded as stash cannot nominate.
	// * an account already bonded as controller can nominate.
	with_externalities(&mut ExtBuilder::default()
		.session_length(1).sessions_per_era(2).build(), 
	|| {
		let arbitrary_value = 5;
		System::set_block_number(1);
		// 2 = controller, 1 stashed => ok
		assert_ok!(Staking::bond(Origin::signed(1), 2, arbitrary_value, RewardDestination::Stash));
		// 2 = controller, 3 stashed (Note that 2 is reused.) => ok
		assert_ok!(Staking::bond(Origin::signed(3), 2, arbitrary_value, RewardDestination::Stash));
		// 4 = not used so far, 1 stashed => not allowed.
		assert_noop!(Staking::bond(Origin::signed(1), 4, arbitrary_value, RewardDestination::Stash), "stash already bonded");
		// 1 = stashed => attempting to nominate should fail.
		assert_noop!(Staking::nominate(Origin::signed(1), vec![1]), "not a controller");
		// 2 = controller  => nominating should work.
		assert_ok!(Staking::nominate(Origin::signed(2), vec![1]));
	});
}

#[test]
fn staking_eras_work() {
	with_externalities(&mut ExtBuilder::default()
		.session_length(1)
		.sessions_per_era(2)
		.reward(10)
		.build(), 
	|| {
		assert_eq!(Staking::era_length(), 2);
		assert_eq!(Staking::sessions_per_era(), 2);
		assert_eq!(Staking::last_era_length_change(), 0);
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 0);

		// Block 1: No change.
		System::set_block_number(1);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::current_index(), 1);
		assert_eq!(Staking::sessions_per_era(), 2);
		assert_eq!(Staking::last_era_length_change(), 0);
		assert_eq!(Staking::current_era(), 0);

		// Block 2: Simple era change.
		System::set_block_number(2);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::current_index(), 2);
		assert_eq!(Staking::sessions_per_era(), 2);
		assert_eq!(Staking::last_era_length_change(), 0);
		assert_eq!(Staking::current_era(), 1);

		// Block 3: Schedule an era length change; no visible changes.
		System::set_block_number(3);
		assert_ok!(Staking::set_sessions_per_era(3));
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::current_index(), 3);
		assert_eq!(Staking::sessions_per_era(), 2);
		assert_eq!(Staking::last_era_length_change(), 0);
		assert_eq!(Staking::current_era(), 1);

		// Block 4: Era change kicks in.
		System::set_block_number(4);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::current_index(), 4);
		assert_eq!(Staking::sessions_per_era(), 3);
		assert_eq!(Staking::last_era_length_change(), 4);
		assert_eq!(Staking::current_era(), 2);

		// Block 5: No change.
		System::set_block_number(5);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::current_index(), 5);
		assert_eq!(Staking::sessions_per_era(), 3);
		assert_eq!(Staking::last_era_length_change(), 4);
		assert_eq!(Staking::current_era(), 2);

		// Block 6: No change.
		System::set_block_number(6);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::current_index(), 6);
		assert_eq!(Staking::sessions_per_era(), 3);
		assert_eq!(Staking::last_era_length_change(), 4);
		assert_eq!(Staking::current_era(), 2);

		// Block 7: Era increment.
		System::set_block_number(7);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::current_index(), 7);
		assert_eq!(Staking::sessions_per_era(), 3);
		assert_eq!(Staking::last_era_length_change(), 4);
		assert_eq!(Staking::current_era(), 3);
	});
}


#[test]
fn balance_transfer_when_bonded_should_not_work() {
	// Tests that a stash account cannot transfer funds
	with_externalities(&mut ExtBuilder::default().build(), || {
		// Confirm account 11 is stashed
		assert_eq!(Staking::bonded(&11), Some(10));
		// Confirm account 11 has some free balance
		assert_eq!(Balances::free_balance(&11), 10);
		Balances::set_free_balance(&11, 100);
		// Confirm that account 11 cannot transfer any balance
		// TODO: Figure out why we dont use the illiquid error 
		assert_noop!(Balances::transfer(Origin::signed(11), 20, 1), "stash with too much under management");
	});
}


#[test]
fn reserving_balance_when_bonded_should_not_work() {
	// Checks that a bonded account cannot reserve balance from free balance
	with_externalities(&mut ExtBuilder::default().build(), || {
		// Check that account 11 is stashed
		assert_eq!(Staking::bonded(&11), Some(10));
		// Confirm account 11 has some free balance
		assert_eq!(Balances::free_balance(&11), 10);
		// Confirm account 11 cannot reserve balance
		// TODO: Figure out why we dont use the illiquid error
		assert_noop!(Balances::reserve(&11, 1), "stash with too much under management");
	});
}


// #[test]
// fn slash_value_calculation_does_not_overflow() {
// 	with_externalities(&mut new_test_ext(0, 3, 3, 0, true, 10), || {
// 		assert_eq!(Staking::era_length(), 9);
// 		assert_eq!(Staking::sessions_per_era(), 3);
// 		assert_eq!(Staking::last_era_length_change(), 0);
// 		assert_eq!(Staking::current_era(), 0);
// 		assert_eq!(Session::current_index(), 0);
// 		assert_eq!(Balances::total_balance(&10), 1);
// 		assert_eq!(Staking::intentions(), vec![10, 20]);
// 		assert_eq!(Staking::offline_slash_grace(), 0);

// 		// set validator preferences so the validator doesn't back down after
// 		// slashing.
// 		<ValidatorPreferences<Test>>::insert(10, ValidatorPrefs {
// 			unstake_threshold: u32::max_value(),
// 			validator_payment: 0,
// 		});

// 		System::set_block_number(3);
// 		Session::check_rotate_session(System::block_number());
// 		assert_eq!(Staking::current_era(), 0);
// 		assert_eq!(Session::current_index(), 1);
// 		assert_eq!(Balances::total_balance(&10), 11);

// 		// the balance type is u64, so after slashing 64 times,
// 		// the slash value should have overflowed. add a couple extra for
// 		// good measure with the slash grace.
// 		trait TypeEq {}
// 		impl<A> TypeEq for (A, A) {}
// 		fn assert_type_eq<A: TypeEq>() {}
// 		assert_type_eq::<(u64, <Test as balances::Trait>::Balance)>();

// 		Staking::on_offline_validator(10, 100);
// 	});
// }

// #[test]
// fn next_slash_value_calculation_does_not_overflow() {
// 	with_externalities(&mut new_test_ext(0, 3, 3, 0, true, 10), || {
// 		assert_eq!(Staking::era_length(), 9);
// 		assert_eq!(Staking::sessions_per_era(), 3);
// 		assert_eq!(Staking::last_era_length_change(), 0);
// 		assert_eq!(Staking::current_era(), 0);
// 		assert_eq!(Session::current_index(), 0);
// 		assert_eq!(Balances::total_balance(&10), 1);
// 		assert_eq!(Staking::intentions(), vec![10, 20]);
// 		assert_eq!(Staking::offline_slash_grace(), 0);

// 		// set validator preferences so the validator doesn't back down after
// 		// slashing.
// 		<ValidatorPreferences<Test>>::insert(10, ValidatorPrefs {
// 			unstake_threshold: u32::max_value(),
// 			validator_payment: 0,
// 		});

// 		// we have enough balance to cover the last slash before overflow
// 		Balances::set_free_balance(&10, u64::max_value());
// 		assert_eq!(Balances::total_balance(&10), u64::max_value());

// 		// the balance type is u64, so after slashing 64 times,
// 		// the slash value should have overflowed. add a couple extra for
// 		// good measure with the slash grace.
// 		trait TypeEq {}
// 		impl<A> TypeEq for (A, A) {}
// 		fn assert_type_eq<A: TypeEq>() {}
// 		assert_type_eq::<(u64, <Test as balances::Trait>::Balance)>();

// 		// the total slash value should overflow the balance type
// 		// therefore the total validator balance should be slashed
// 		Staking::on_offline_validator(10, 100);

// 		assert_eq!(Balances::total_balance(&10), 0);
// 	});
// }
