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
	// TODO: Verify this check is comprehensive
	// - Session Per Era, Session Reward
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
fn no_offline_should_work() {
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
	// Test that users can be invulnerable from slashing and being kicked
	// TODO: Verify user is still in the validators
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
fn offline_should_slash_and_kick() {
	// Test that an offline validator gets slashed
	// TODO: Confirm user is kicked
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
fn offline_grace_should_delay_slashing() {
	// Tests that with grace, slashing is delayed
	with_externalities(&mut ExtBuilder::default().build(), || {
		// Initialize account 10 with balance
		Balances::set_free_balance(&10, 70);
		// Verify account 10 has balance
		assert_eq!(Balances::free_balance(&10), 70);

		// Set offline slash grace
		let offline_slash_grace = 1;
		assert_ok!(Staking::set_offline_slash_grace(offline_slash_grace));
		assert_eq!(Staking::offline_slash_grace(), 1);

		// Check unstaked_threshold is 3 (default)
		let default_unstake_threshold = 3;
		assert_eq!(Staking::validators(&10), ValidatorPrefs { unstake_threshold: default_unstake_threshold, validator_payment: 0 });

		// Check slash count is zero
		assert_eq!(Staking::slash_count(&10), 0);

		// Report account 10 up to the threshold
		Staking::on_offline_validator(10, default_unstake_threshold as usize + offline_slash_grace as usize);
		// Confirm slash count
		assert_eq!(Staking::slash_count(&10), 4);

		// Nothing should happen
		assert_eq!(Balances::free_balance(&10), 70);

		// Report account 10 one more time
		Staking::on_offline_validator(10, 1);
		assert_eq!(Staking::slash_count(&10), 5);
		// User gets slashed
		assert_eq!(Balances::free_balance(&10), 0);
		// New era is forced
		assert!(Staking::forcing_new_era().is_some());
	});
}


#[test]
fn rewards_should_work() {
	// should check that: 
	// 1) rewards get recorded per session
	// 2) rewards get paid per Era
	// TODO: Check that nominators are also rewarded, check with @gav that this is the code
	with_externalities(&mut ExtBuilder::default().build(), 
	|| {
		let delay = 2;
		// this test is only in the scope of one era. Since this variable changes 
		// at the last block/new era, we'll save it.
		let session_reward = 10;

		// Initial config should be correct
		assert_eq!(Staking::era_length(), 9);
		assert_eq!(Staking::sessions_per_era(), 3);
		assert_eq!(Staking::last_era_length_change(), 0);
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 0);

		assert_eq!(Staking::current_session_reward(), 10);

		// check the balance of a validator accounts.
		assert_eq!(Balances::total_balance(&10), 1); 
		// and the nominator (to-be)
		assert_eq!(Balances::total_balance(&2), 20); 

		// add a dummy nominator.
		// NOTE: this nominator is being added 'manually'. a Further test (nomination_and_reward..) will add it via '.nominate()'
		<Stakers<Test>>::insert(&10, Exposure {
			own: 500, // equal division indicates that the reward will be equally divided among validator and nominator.
			total: 1000,
			others: vec![IndividualExposure {who: 2, value: 500 }] 
		}); 
		<Payee<Test>>::insert(&2, RewardDestination::Controller);


		let mut block = 3;
		// Block 3 => Session 1 => Era 0
		System::set_block_number(block);
		Timestamp::set_timestamp(block*5);	// on time.
		Session::check_rotate_session(System::block_number()); // QUESTIONS: why this matters ?
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 1);

		// session triggered: the reward value stashed should be 10 -- defined in ExtBuilder genesis.
		assert_eq!(Staking::current_session_reward(), session_reward);
		assert_eq!(Staking::current_era_reward(), session_reward);
		
		block = 6; // Block 6 => Session 2 => Era 0 
		System::set_block_number(block);
		Timestamp::set_timestamp(block*5 + delay);	// a little late.
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 2);

		// session reward is the same,
		assert_eq!(Staking::current_session_reward(), session_reward);
		// though 2 will be deducted while stashed in the era reward due to delay
		assert_eq!(Staking::current_era_reward(), 2*session_reward - delay);

		block = 9; // Block 9 => Session 3 => Era 1
		System::set_block_number(block);
		Timestamp::set_timestamp(block*5);  // back to being punktlisch. no delayss
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 1);
		assert_eq!(Session::current_index(), 3);

		assert_eq!(Balances::total_balance(&10), 1 + (3*session_reward - delay)/2);
		assert_eq!(Balances::total_balance(&2), 20 + (3*session_reward - delay)/2);
	});
}

#[test]
fn multi_era_reward_should_work() {
	// should check that:
	// The value of current_session_reward is set at the end of each era, based on 
	// slot_stake and session_reward. Check and verify this. 
	with_externalities(&mut ExtBuilder::default().build(), 
	|| {
		let delay = 0;
		let session_reward = 10;

		// This is set by the test config builder.
		assert_eq!(Staking::current_session_reward(), session_reward);

		// check the balance of a validator accounts.
		assert_eq!(Balances::total_balance(&10), 1); 

		let mut block = 3;
		// Block 3 => Session 1 => Era 0
		System::set_block_number(block);
		Timestamp::set_timestamp(block*5);	// on time.
		Session::check_rotate_session(System::block_number()); // QUESTIONS: why this matters ?
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 1);

		// session triggered: the reward value stashed should be 10 -- defined in ExtBuilder genesis.
		assert_eq!(Staking::current_session_reward(), session_reward);
		assert_eq!(Staking::current_era_reward(), session_reward);
		
		block = 6; // Block 6 => Session 2 => Era 0 
		System::set_block_number(block);
		Timestamp::set_timestamp(block*5 + delay);	// a little late.
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 2);

		assert_eq!(Staking::current_session_reward(), session_reward);
		assert_eq!(Staking::current_era_reward(), 2*session_reward - delay);

		block = 9; // Block 9 => Session 3 => Era 1
		System::set_block_number(block);
		Timestamp::set_timestamp(block*5);  // back to being punktlisch. no delayss
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 1);
		assert_eq!(Session::current_index(), 3);

		// 1 + sum of of the session rewards accumulated
		let recorded_balance = 1 + 3*session_reward - delay;
		assert_eq!(Balances::total_balance(&10), recorded_balance);
		
		// the reward for next era will be: session_reward * slot_stake
		let new_session_reward = Staking::session_reward() * Staking::slot_stake();
		assert_eq!(Staking::current_session_reward(), new_session_reward);

		// fast forward to next era:
		block=12;System::set_block_number(block);Timestamp::set_timestamp(block*5);Session::check_rotate_session(System::block_number());
		block=15;System::set_block_number(block);Timestamp::set_timestamp(block*5);Session::check_rotate_session(System::block_number());
		
		// intermediate test.
		assert_eq!(Staking::current_era_reward(), 2*new_session_reward);
		
		block=18;System::set_block_number(block);Timestamp::set_timestamp(block*5);Session::check_rotate_session(System::block_number());
		
		// pay time
		assert_eq!(Balances::total_balance(&10), 3*new_session_reward + recorded_balance);
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
		// give the man some coins 
		Balances::set_free_balance(&3, 3000);
		// initial stakers: vec![(11, 10, balance_factor * 100), (21, 20, balance_factor * 200)],
		// account 3 controlled by 4.
		assert_ok!(Staking::bond(Origin::signed(3), 4, 1500, RewardDestination::default())); // balance of 3 = 3000, stashed = 1500
		
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 0);
		// No effects will be seen so far.s
		assert_eq!(Session::validators(), vec![10, 20]);
		

		// --- Block 2: 
		System::set_block_number(2);
		// Explicitly state the desire to validate for all of them.
		// note that the controller account will state interest as representative of the stash-controller pair.
		assert_ok!(Staking::validate(Origin::signed(4), ValidatorPrefs { unstake_threshold: 3, validator_payment: 0 }));

		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 0);
		// No effects will be seen so far. Era has not been yet triggered.
		assert_eq!(Session::validators(), vec![10, 20]);


		// --- Block 3: the validators will now change. 
		System::set_block_number(3);
		Session::check_rotate_session(System::block_number());

		// TODO: the assertion in the section should be changed to something in sync with how phragmen works.
		// for now just check that some arbitrary "two validators" have been chosen.
		assert_eq!(Session::validators().len(), 2);
		assert_eq!(Session::validators(), vec![4, 20]);
		assert_eq!(Staking::current_era(), 1);


		// --- Block 4: Unstake 4 as a validator, freeing up the balance stashed in 3
		System::set_block_number(4);

		// unlock the entire stashed value.
		Staking::unbond(Origin::signed(4), Staking::ledger(&4).unwrap().active).unwrap();
		
		Session::check_rotate_session(System::block_number());
		// nothing should be changed so far.
		assert_eq!(Session::validators(), vec![4, 20]);
		assert_eq!(Staking::current_era(), 1);
		
		
		// --- Block 5: nothing. 4 is still there. 
		System::set_block_number(5);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::validators(), vec![4, 20]); 
		assert_eq!(Staking::current_era(), 1);


		// --- Block 6: 4 will be not be a validator as it has nothing in stash.
		System::set_block_number(6);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::validators().contains(&4), false); 
	});
}


#[test]
fn nominating_and_rewards_should_work() {
	// TODO: This should be rewritten and tested with the Phragmen algorithm
	// For now it tests a functionality which somehow overlaps with other tests:
	// the fact that the nominator is rewarded properly.
	with_externalities(&mut ExtBuilder::default()
		.session_length(1).sessions_per_era(1).build(), 
	|| {
		let session_reward = 10;
		let initial_balance = 1000;
		assert_eq!(Staking::era_length(), 1);
		assert_eq!(Staking::validator_count(), 2);
		assert_eq!(Staking::bonding_duration(), 3);
		assert_eq!(Session::validators(), vec![10, 20]);

		// default reward for the first session.
		assert_eq!(Staking::current_session_reward(), session_reward);

		// give the man some money
		for i in 1..5 { Balances::set_free_balance(&i, initial_balance); }
		Balances::set_free_balance(&10, initial_balance);
		Balances::set_free_balance(&20, initial_balance);


		System::set_block_number(1);
		// record their balances.
		for i in 1..5 { assert_eq!(Balances::total_balance(&i), initial_balance); }


		// bond two account pairs and state interest in nomination.
		// NOTE: in the current naive version only the first vote matters and will be chosen anyhow.

		// 2 will nominate for 10, 10 has 1000 in stash, 500 will be 1/3 of the total 1500 
		assert_ok!(Staking::bond(Origin::signed(1), 2, 500, RewardDestination::Controller));
		assert_ok!(Staking::nominate(Origin::signed(2), vec![10, 20]));
		// 4 will nominate for 20, 20 has 2000 in stash, 500 will be 1/5 of the total 2500 
		assert_ok!(Staking::bond(Origin::signed(3), 4, 500, RewardDestination::Stash));
		assert_ok!(Staking::nominate(Origin::signed(4), vec![20, 10]));
	

		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 1);
		// validators will not change, since selection currently is actually not dependent on nomination and votes, only stake.
		assert_eq!(Session::validators(), vec![10, 20]);
		// avalidators must have already received some rewards.
		assert_eq!(Balances::total_balance(&10), initial_balance + session_reward);
		assert_eq!(Balances::total_balance(&20), initial_balance + session_reward);
		

		System::set_block_number(2);
		// next session reward.
		let new_session_reward = Staking::session_reward() * Staking::slot_stake();
		// nothing else will happen, era ends and rewards are paid again,
		// it is expected that nominators will also be paid.
		Session::check_rotate_session(System::block_number());


		// Nominator 2: staked 1/3 of the total, gets 1/3 of the reward, chose controller as destination
		assert_eq!(Balances::total_balance(&2), initial_balance + new_session_reward/3);
		// The Associated validator will get the other 2/3
		assert_eq!(Balances::total_balance(&10), initial_balance + session_reward + 2*new_session_reward/3);

		// Nominator 4: staked 1/5 of the total, gets 1/5 of the reward, chose stash as destination
		// This means that the reward will go to 3, which is bonded as the stash of 4.
		assert_eq!(Balances::total_balance(&3), initial_balance + new_session_reward/5);
		// The Associated validator will get the other 4/5
		assert_eq!(Balances::total_balance(&20), initial_balance + session_reward + 4*new_session_reward/5);
	});
}

#[test]
fn nominators_also_get_slashed() {
	// A nominator should be slashed if the validator they nominated is slashed
	with_externalities(&mut ExtBuilder::default()
	.session_length(1).sessions_per_era(1).build(),
	|| {
		assert_eq!(Staking::era_length(), 1);
		assert_eq!(Staking::validator_count(), 2);
		// slash happens immediately.
		assert_eq!(Staking::offline_slash_grace(), 0);
		// Account 10 has not been reported offline
		assert_eq!(Staking::slash_count(&10), 0);
		// initial validators
		assert_eq!(Session::validators(), vec![10, 20]);

		// give the man some money.
		let initial_balance = 1000;
		for i in 1..3 { Balances::set_free_balance(&i, initial_balance); }
		Balances::set_free_balance(&10, initial_balance);

		// 2 will nominate for 10
		let nominator_stake = 500;
		assert_ok!(Staking::bond(Origin::signed(1), 2, nominator_stake, RewardDestination::default()));
		assert_ok!(Staking::nominate(Origin::signed(2), vec![10, 20]));

		// new era, pay rewards,
		System::set_block_number(2);
		Session::check_rotate_session(System::block_number());

		// 10 goes offline
		Staking::on_offline_validator(10, 4);
		let slash_value = Staking::current_offline_slash()*8; 
		let expo = Staking::stakers(10);
		let actual_slash = expo.own.min(slash_value);
		let nominator_actual_slash = nominator_stake.min(expo.total - actual_slash);
		// initial + first era reward + slash
		assert_eq!(Balances::total_balance(&10), initial_balance + 10 - actual_slash);
		assert_eq!(Balances::total_balance(&2), initial_balance - 500);
	});
}

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
		assert_ok!(Staking::bond(Origin::signed(1), 2, arbitrary_value, RewardDestination::default()));
		// 2 = controller, 3 stashed (Note that 2 is reused.) => ok
		assert_ok!(Staking::bond(Origin::signed(3), 2, arbitrary_value, RewardDestination::default()));
		// 4 = not used so far, 1 stashed => not allowed.
		assert_noop!(Staking::bond(Origin::signed(1), 4, arbitrary_value, RewardDestination::default()), "stash already bonded");
		// 1 = stashed => attempting to nominate should fail.
		assert_noop!(Staking::nominate(Origin::signed(1), vec![1]), "not a controller");
		// 2 = controller  => nominating should work.
		assert_ok!(Staking::nominate(Origin::signed(2), vec![1]));
	});
}

#[test]
fn session_and_eras_work() {
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

#[test]
fn max_unstake_threshold_works() {
	// Tests that max_unstake_threshold gets used when prefs.unstake_threshold is large
	// TODO: Why does this test fail?
	with_externalities(&mut ExtBuilder::default().build(), || {
		const MAX_UNSTAKE_THRESHOLD: u32 = 10;
		// Two users with maximum possible balance
		Balances::set_free_balance(&10, u64::max_value());
		Balances::set_free_balance(&20, u64::max_value());

		// Give them full exposer as a staker
		<Stakers<Test>>::insert(&10, Exposure { total: u64::max_value(), own: u64::max_value(), others: vec![]});
		<Stakers<Test>>::insert(&20, Exposure { total: u64::max_value(), own: u64::max_value(), others: vec![]});

		// Check things are initialized correctly
		assert_eq!(Balances::free_balance(&10), u64::max_value());
		assert_eq!(Balances::free_balance(&20), u64::max_value());
		assert_eq!(Balances::free_balance(&10), Balances::free_balance(&20));
		assert_eq!(Staking::offline_slash_grace(), 0);
		assert_eq!(Staking::current_offline_slash(), 20);
		// Account 10 will have unstake_threshold 10
		<Validators<Test>>::insert(10, ValidatorPrefs {
			unstake_threshold: MAX_UNSTAKE_THRESHOLD,
			validator_payment: 0,
		});
		// Account 20 will have unstake_threshold 100, which should be limited to 10
		<Validators<Test>>::insert(20, ValidatorPrefs {
			unstake_threshold: 100,
			validator_payment: 0,
		});

		// Report each user 1 more than the max_unstake_threshold
		Staking::on_offline_validator(10, MAX_UNSTAKE_THRESHOLD as usize + 1);
		Staking::on_offline_validator(20, MAX_UNSTAKE_THRESHOLD as usize + 1);

		// Show that each balance only gets reduced by 2^max_unstake_threshold
		assert_eq!(Balances::free_balance(&10), u64::max_value() - 2_u64.pow(MAX_UNSTAKE_THRESHOLD) * 20);
		assert_eq!(Balances::free_balance(&20), u64::max_value() - 2_u64.pow(MAX_UNSTAKE_THRESHOLD) * 20);
	});
}

#[test]
fn slashing_does_not_cause_underflow() {
	// Tests that slashing more than a user has does not underflow
	with_externalities(&mut ExtBuilder::default().build(), || {
		// One user with less than `max_value` will test underflow does not occur
		Balances::set_free_balance(&10, 1);

		// Verify initial conditions
		assert_eq!(Balances::free_balance(&10), 1);
		assert_eq!(Staking::offline_slash_grace(), 0);

		// Set validator preference so that 2^unstake_threshold would cause overflow (greater than 64)
		<Validators<Test>>::insert(10, ValidatorPrefs {
			unstake_threshold: 10,
			validator_payment: 0,
		});

		// Should not panic
		Staking::on_offline_validator(10, 100);
		// Confirm that underflow has not occurred, and account balance is set to zero
		assert_eq!(Balances::free_balance(&10), 0);
	});
}

/*
#[test]
fn reward_destination_works() {
	// TODO: Test that rewards go to the right place when set
	// Stake, stash, controller
	with_externalities(&mut ExtBuilder::default()
		.sessions_per_era(1)
		.session_length(1)
		.build(),
	|| {
		// Check that account 10 is a validator
		assert!(<Validators<Test>>::exists(10));
		// Check the balance of the validator account
		assert_eq!(Balances::free_balance(&10), 1); 
		// Check the balance of the stash account
		assert_eq!(Balances::free_balance(&11), 10); 
		// Check these two accounts are bonded
		assert_eq!(Staking::bonded(&11), Some(10));
		// Check how much is at stake
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1000, active: 1000, unlocking: vec![] }));


		// Move forward the system for payment
		System::set_block_number(1);
		Timestamp::set_timestamp(5);
		Session::check_rotate_session(System::block_number());

		// Check that RewardDestination is Staked (default)
		assert_eq!(Staking::payee(&10), RewardDestination::Staked);
		// Check that reward went to the stash account
		println!("{:?} {:?}", Balances::free_balance(&10), Balances::free_balance(&11));
		assert_eq!(Balances::free_balance(&11), 10 + 10);
		// Check that amount at stake increased accordingly
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1000 + 10, active: 1000 + 10, unlocking: vec![] }));

		//Change RewardDestination to Stash
		<Payee<Test>>::insert(&10, RewardDestination::Stash);

		// Move forward the system for payment
		System::set_block_number(2);
		Timestamp::set_timestamp(10);
		Session::check_rotate_session(System::block_number());

		// Check that RewardDestination is Stash
		assert_eq!(Staking::payee(&10), RewardDestination::Stash);
		// Check that reward went to the stash account
		println!("{:?} {:?}", Balances::free_balance(&10), Balances::free_balance(&11));
		assert_eq!(Balances::free_balance(&11), 10 + 10 + 10);
		// Check that amount at stake is not increased
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1000 + 10, active: 1000 + 10, unlocking: vec![] }));

		//Change RewardDestination to Controller
		<Payee<Test>>::insert(&10, RewardDestination::Controller);

		// Move forward the system for payment
		System::set_block_number(3);
		Timestamp::set_timestamp(15);
		Session::check_rotate_session(System::block_number());

		// Check that RewardDestination is Controller
		assert_eq!(Staking::payee(&10), RewardDestination::Controller);
		// Check that reward went to the controller account
		println!("{:?} {:?}", Balances::free_balance(&10), Balances::free_balance(&11));
		assert_eq!(Balances::free_balance(&10), 1 + 10);
		// Check that amount at stake is not increased
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1010, active: 1010, unlocking: vec![] }));

	});

}
*/
#[test]
fn validator_prefs_work() {
	// TODO: Test that validator preferences are correctly honored
}

#[test]
fn staking_ledger_grows_and_shrinks() {
	// TODO: Show that staking ledger grows with new events
	// TODO: Show that staking ledger shrinks when user is removed
}

#[test]
fn consolidate_unlocked_works() {
	// TODO: Figure out what it does and then test it
}

#[test]
fn bond_extra_works() {
	// Tests that extra `free_balance` in the stash can be added to stake
	with_externalities(&mut ExtBuilder::default().build(),
	|| {
		// Check that account 10 is a validator
		assert!(<Validators<Test>>::exists(10));
		// Check that account 10 is bonded to account 11
		assert_eq!(Staking::bonded(&11), Some(10));
		// Check how much is at stake
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1000, active: 1000, unlocking: vec![] }));

		// Give account 11 some large free balance greater than total
		Balances::set_free_balance(&11, 1000000);
		// Check the balance of the stash account
		assert_eq!(Balances::free_balance(&11), 1000000);

		// Call the bond_extra function from controller, add only 100
		assert_ok!(Staking::bond_extra(Origin::signed(10), 100));
		// There should be 100 more `total` and `active` in the ledger
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1000 + 100, active: 1000 + 100, unlocking: vec![] }));

		// Call the bond_extra function with a large number, should handle it
		assert_ok!(Staking::bond_extra(Origin::signed(10), u64::max_value()));
		// The full amount of the funds should now be in the total and active
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1000000, active: 1000000, unlocking: vec![] }));

	});
}

#[test]
fn withdraw_unbonded_works() {
	// TODO: Learn what it is and test it
}

#[test]
fn reporting_misbehaviors_work() {
	// TODO: Does this code exist?
}

#[test]
fn correct_number_of_validators_are_chosen() {
	// TODO: Check that number is at least minimum, and at most what is set
	// TODO: Test emergency conditions?
}

#[test]
fn slot_stake_does_something() {
	// TODO: What does it do?
}

#[test]
fn on_free_balance_zero_stash_removes_validator() {
	// Tests that validator storage items are cleaned up when stash is empty
	// Tests that storage items are untouched when controller is empty
	with_externalities(&mut ExtBuilder::default()
		.existential_deposit(10)
		.build(),
	|| {
		// Check that account 10 is a validator
		assert!(<Validators<Test>>::exists(10));
		// Check the balance of the validator account
		assert_eq!(Balances::free_balance(&10), 256); 
		// Check the balance of the stash account
		assert_eq!(Balances::free_balance(&11), 2560); 
		// Check these two accounts are bonded
		assert_eq!(Staking::bonded(&11), Some(10));

		// Set some storage items which we expect to be cleaned up
		// Initiate slash count storage item
		Staking::on_offline_validator(10, 1);
		// Set payee information
		assert_ok!(Staking::set_payee(Origin::signed(10), RewardDestination::Stash));

		// Check storage items that should be cleaned up
		assert!(<Ledger<Test>>::exists(&10));
		assert!(<Validators<Test>>::exists(&10));
		assert!(<SlashCount<Test>>::exists(&10));
		assert!(<Payee<Test>>::exists(&10));

		// Reduce free_balance of controller to 0
		Balances::set_free_balance(&10, 0);
		// Check total balance of account 10
		assert_eq!(Balances::total_balance(&10), 0); 

		// Check the balance of the stash account has not been touched
		assert_eq!(Balances::free_balance(&11), 2560); 
		// Check these two accounts are still bonded
		assert_eq!(Staking::bonded(&11), Some(10));

		// Check storage items have not changed
		assert!(<Ledger<Test>>::exists(&10));
		assert!(<Validators<Test>>::exists(&10));
		assert!(<SlashCount<Test>>::exists(&10));
		assert!(<Payee<Test>>::exists(&10));

		// Reduce free_balance of stash to 0
		Balances::set_free_balance(&11, 0);
		// Check total balance of stash
		assert_eq!(Balances::total_balance(&11), 0); 

		// Check storage items do not exist
		assert!(!<Ledger<Test>>::exists(&10));
		assert!(!<Validators<Test>>::exists(&10));
		assert!(!<Nominators<Test>>::exists(&10));
		assert!(!<SlashCount<Test>>::exists(&10));
		assert!(!<Payee<Test>>::exists(&10));
		assert!(!<Bonded<Test>>::exists(&11));
	});
}

#[test]
fn on_free_balance_zero_stash_removes_nominator() {
	// Tests that nominator storage items are cleaned up when stash is empty
	// Tests that storage items are untouched when controller is empty
	with_externalities(&mut ExtBuilder::default()
		.existential_deposit(10)
		.build(),
	|| {
		// Make 10 a nominator
		assert_ok!(Staking::nominate(Origin::signed(10), vec![20]));
		// Check that account 10 is a nominator
		assert!(<Nominators<Test>>::exists(10));
		// Check the balance of the nominator account
		assert_eq!(Balances::free_balance(&10), 256); 
		// Check the balance of the stash account
		assert_eq!(Balances::free_balance(&11), 2560); 
		// Check these two accounts are bonded
		assert_eq!(Staking::bonded(&11), Some(10));

		// Set payee information
		assert_ok!(Staking::set_payee(Origin::signed(10), RewardDestination::Stash));


		// Check storage items that should be cleaned up
		assert!(<Ledger<Test>>::exists(&10));
		assert!(<Nominators<Test>>::exists(&10));
		assert!(<Payee<Test>>::exists(&10));

		// Reduce free_balance of controller to 0
		Balances::set_free_balance(&10, 0);
		// Check total balance of account 10
		assert_eq!(Balances::total_balance(&10), 0); 

		// Check the balance of the stash account has not been touched
		assert_eq!(Balances::free_balance(&11), 2560); 
		// Check these two accounts are still bonded
		assert_eq!(Staking::bonded(&11), Some(10));

		// Check storage items have not changed
		assert!(<Ledger<Test>>::exists(&10));
		assert!(<Nominators<Test>>::exists(&10));
		assert!(<Payee<Test>>::exists(&10));

		// Reduce free_balance of stash to 0
		Balances::set_free_balance(&11, 0);
		// Check total balance of stash
		assert_eq!(Balances::total_balance(&11), 0); 

		// Check storage items do not exist
		assert!(!<Ledger<Test>>::exists(&10));
		assert!(!<Validators<Test>>::exists(&10));
		assert!(!<Nominators<Test>>::exists(&10));
		assert!(!<SlashCount<Test>>::exists(&10));
		assert!(!<Payee<Test>>::exists(&10));
		assert!(!<Bonded<Test>>::exists(&11));
	});
}