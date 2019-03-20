// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
use phragmen;
use primitives::Perquintill;
use srml_support::{assert_ok, assert_noop, EnumerableStorageMap};
use mock::{Balances, Session, Staking, System, Timestamp, Test, ExtBuilder, Origin};
use srml_support::traits::Currency;

#[test]
fn basic_setup_works() {
	// Verifies initial conditions of mock
	with_externalities(&mut ExtBuilder::default()
		.build(),
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

		// Account 100 is the default nominator
		assert_eq!(Staking::ledger(100), Some(StakingLedger { stash: 101, total: 500, active: 500, unlocking: vec![] }));
		assert_eq!(Staking::nominators(100), vec![10, 20]);

		// Account 10 is exposed by 100 * balance_factor from their own stash in account 11
		assert_eq!(Staking::stakers(10), Exposure { total: 1500, own: 1000, others: vec![ IndividualExposure { who: 100, value: 500 }] });
		assert_eq!(Staking::stakers(20), Exposure { total: 2500, own: 2000, others: vec![ IndividualExposure { who: 100, value: 500 }] });

		// The number of validators required.
		assert_eq!(Staking::validator_count(), 2);

		// Initial Era and session
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 0);

		// initial rewards
		assert_eq!(Staking::current_session_reward(), 10);

		// initial slot_stake
		assert_eq!(Staking::slot_stake(), 1500);

		// initial slash_count of validators 
		assert_eq!(Staking::slash_count(&10), 0);
		assert_eq!(Staking::slash_count(&20), 0);
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
	with_externalities(&mut ExtBuilder::default().build(),
	|| {
		// Make account 10 invulnerable
		assert_ok!(Staking::set_invulnerables(vec![10]));
		// Give account 10 some funds
		let _ = Balances::deposit_creating(&10, 69);
		// There is no slash grace -- slash immediately.
		assert_eq!(Staking::offline_slash_grace(), 0);
		// Account 10 has not been slashed
		assert_eq!(Staking::slash_count(&10), 0);
		// Account 10 has the 70 funds we gave it above
		assert_eq!(Balances::free_balance(&10), 70);
		// Account 10 should be a validator
		assert!(<Validators<Test>>::exists(&10));

		// Set account 10 as an offline validator with a large number of reports
		// Should exit early if invulnerable
		Staking::on_offline_validator(10, 100);

		// Show that account 10 has not been touched
		assert_eq!(Staking::slash_count(&10), 0);
		assert_eq!(Balances::free_balance(&10), 70);
		assert!(<Validators<Test>>::exists(&10));
		// New era not being forced
		// NOTE: new era is always forced once slashing happens -> new validators need to be chosen.
		assert!(Staking::forcing_new_era().is_none());
	});
}

#[test]
fn offline_should_slash_and_kick() {
	// Test that an offline validator gets slashed and kicked
	with_externalities(&mut ExtBuilder::default().build(), || {
		// Give account 10 some balance
		let _ = Balances::deposit_creating(&10, 999);
		// Confirm account 10 is a validator
		assert!(<Validators<Test>>::exists(&10));
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
		// Confirm `slot_stake` is greater than exponential punishment, else math below will be different
		assert!(Staking::slot_stake() > 2_u64.pow(3) * 20);
		// Confirm balance has been reduced by 2^unstake_threshold * current_offline_slash()
		assert_eq!(Balances::free_balance(&10), 1000 - 2_u64.pow(3) * 20);
		// Confirm account 10 has been removed as a validator
		assert!(!<Validators<Test>>::exists(&10));
		// A new era is forced due to slashing
		assert!(Staking::forcing_new_era().is_some());
	});
}

#[test]
fn offline_grace_should_delay_slashing() {
	// Tests that with grace, slashing is delayed
	with_externalities(&mut ExtBuilder::default().build(), || {
		// Initialize account 10 with balance
		let _ = Balances::deposit_creating(&10, 69);
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
fn max_unstake_threshold_works() {
	// Tests that max_unstake_threshold gets used when prefs.unstake_threshold is large
	with_externalities(&mut ExtBuilder::default().build(), || {
		const MAX_UNSTAKE_THRESHOLD: u32 = 10;
		// Two users with maximum possible balance
		let _ = Balances::deposit_creating(&10, u64::max_value() - 1);
		let _ = Balances::deposit_creating(&20, u64::max_value() - 1);

		// Give them full exposer as a staker
		<Stakers<Test>>::insert(&10, Exposure { total: u64::max_value(), own: u64::max_value(), others: vec![]});
		<Stakers<Test>>::insert(&20, Exposure { total: u64::max_value(), own: u64::max_value(), others: vec![]});

		// Check things are initialized correctly
		assert_eq!(Balances::free_balance(&10), u64::max_value());
		assert_eq!(Balances::free_balance(&20), u64::max_value());
		assert_eq!(Balances::free_balance(&10), Balances::free_balance(&20));
		assert_eq!(Staking::offline_slash_grace(), 0);
		assert_eq!(Staking::current_offline_slash(), 20);
		// Account 10 will have max unstake_threshold
		assert_ok!(Staking::validate(Origin::signed(10), ValidatorPrefs {
			unstake_threshold: MAX_UNSTAKE_THRESHOLD,
			validator_payment: 0,
		}));
		// Account 20 could not set their unstake_threshold past 10
		assert_noop!(Staking::validate(Origin::signed(20), ValidatorPrefs {
			unstake_threshold: 11,
			validator_payment: 0}),
			"unstake threshold too large"
		);
		// Give Account 20 unstake_threshold 11 anyway, should still be limited to 10
		<Validators<Test>>::insert(20, ValidatorPrefs {
			unstake_threshold: 11,
			validator_payment: 0,
		});

		// Make slot_stake really large, as to not affect punishment curve
		<SlotStake<Test>>::put(u64::max_value());
		// Confirm `slot_stake` is greater than exponential punishment, else math below will be different
		assert!(Staking::slot_stake() > 2_u64.pow(MAX_UNSTAKE_THRESHOLD) * 20);

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
		// Verify initial conditions
		assert_eq!(Balances::free_balance(&10), 1);
		assert_eq!(Staking::offline_slash_grace(), 0);

		// Set validator preference so that 2^unstake_threshold would cause overflow (greater than 64)
		<Validators<Test>>::insert(10, ValidatorPrefs {
			unstake_threshold: 10,
			validator_payment: 0,
		});

		System::set_block_number(1);
		Session::check_rotate_session(System::block_number());

		// Should not panic
		Staking::on_offline_validator(10, 100);
		// Confirm that underflow has not occurred, and account balance is set to zero
		assert_eq!(Balances::free_balance(&10), 0);
	});
}


#[test]
fn rewards_should_work() {
	// should check that:
	// * rewards get recorded per session
	// * rewards get paid per Era
	// * Check that nominators are also rewarded
	with_externalities(&mut ExtBuilder::default()
		.session_length(3)
		.sessions_per_era(3)
	.build(),
	|| {
		let delay = 2;
		// this test is only in the scope of one era. Since this variable changes
		// at the last block/new era, we'll save it.
		let session_reward = 10;

		// Set payee to controller
		assert_ok!(Staking::set_payee(Origin::signed(10), RewardDestination::Controller));

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
		Session::check_rotate_session(System::block_number()); 
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
	with_externalities(&mut ExtBuilder::default()
		.session_length(3)
		.sessions_per_era(3)
		.nominate(false)
		.build(),
	|| {
		let delay = 0;
		let session_reward = 10;

		// This is set by the test config builder.
		assert_eq!(Staking::current_session_reward(), session_reward);

		// check the balance of a validator accounts.
		assert_eq!(Balances::total_balance(&10), 1);

		// Set payee to controller
		assert_ok!(Staking::set_payee(Origin::signed(10), RewardDestination::Controller));

		let mut block = 3;
		// Block 3 => Session 1 => Era 0
		System::set_block_number(block);
		Timestamp::set_timestamp(block*5);	// on time.
		Session::check_rotate_session(System::block_number());
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
		
		// new era is triggered here.
		block=18;System::set_block_number(block);Timestamp::set_timestamp(block*5);Session::check_rotate_session(System::block_number());
		
		// pay time
		assert_eq!(Balances::total_balance(&10), 3*new_session_reward + recorded_balance);
	});
}

#[test]
fn staking_should_work() {
	// should test:
	// * new validators can be added to the default set
	// * new ones will be chosen per era
	// * either one can unlock the stash and back-down from being a validator via `chill`ing.
	with_externalities(&mut ExtBuilder::default()
		.sessions_per_era(3)
		.nominate(false)
		.build(),
	|| {
		assert_eq!(Staking::era_length(), 3);
		// remember + compare this along with the test.
		assert_eq!(Session::validators(), vec![20, 10]);
		assert_ok!(Staking::set_bonding_duration(2));
		assert_eq!(Staking::bonding_duration(), 2);

		// put some money in account that we'll use.
		for i in 1..5 { let _ = Balances::deposit_creating(&i, 1000); }

		// bond one account pair and state interest in nomination.
		// this is needed to keep 10 and 20 in the validator list with phragmen
		assert_ok!(Staking::bond(Origin::signed(1), 2, 500, RewardDestination::default()));
		assert_ok!(Staking::nominate(Origin::signed(2), vec![20, 4]));

		// --- Block 1:
		System::set_block_number(1);

		// add a new candidate for being a validator. account 3 controlled by 4.
		assert_ok!(Staking::bond(Origin::signed(3), 4, 1500, RewardDestination::Controller)); // balance of 3 = 3000, stashed = 1500
		
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 0);
		// No effects will be seen so far.s
		assert_eq!(Session::validators(), vec![20, 10]);
		

		// --- Block 2:
		System::set_block_number(2);
		// Explicitly state the desire to validate
		// note that the controller account will state interest as representative of the stash-controller pair.
		assert_ok!(Staking::validate(Origin::signed(4), ValidatorPrefs::default()));

		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 0);
		// No effects will be seen so far. Era has not been yet triggered.
		assert_eq!(Session::validators(), vec![20, 10]);


		// --- Block 3: the validators will now change.
		System::set_block_number(3);
		Session::check_rotate_session(System::block_number());

		// 2 only voted for 4 and 20
		assert_eq!(Session::validators().len(), 2);
		assert_eq!(Session::validators(), vec![4, 20]);
		assert_eq!(Staking::current_era(), 1);


		// --- Block 4: Unstake 4 as a validator, freeing up the balance stashed in 3
		System::set_block_number(4);

		// unlock the entire stashed value.
		// Note that this will ne be enough to remove 4 as a validator candidate!
		Staking::unbond(Origin::signed(4), Staking::ledger(&4).unwrap().active).unwrap();
		// explicit chill indicated that 4 no longer wants to be a validator.
		Staking::chill(Origin::signed(4)).unwrap();
		
		// nominator votes for 10
		assert_ok!(Staking::nominate(Origin::signed(2), vec![20, 10]));
		
		Session::check_rotate_session(System::block_number());
		// nothing should be changed so far.
		assert_eq!(Session::validators(), vec![4, 20]);
		assert_eq!(Staking::current_era(), 1);
		
		
		// --- Block 5: nothing. 4 is still there.
		System::set_block_number(5);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::validators(), vec![4, 20]);
		assert_eq!(Staking::current_era(), 1);


		// --- Block 6: 4 will not be a validator.
		System::set_block_number(6);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 2);
		assert_eq!(Session::validators().contains(&4), false);
		assert_eq!(Session::validators(), vec![20, 10]);
	});
}

#[test]
fn less_than_needed_candidates_works() {
	// Test the situation where the number of validators are less than `ValidatorCount` but more than <MinValidators>
	// The expected behavior is to choose all the candidates that have some vote.
	with_externalities(&mut ExtBuilder::default()
		.minimum_validator_count(1)
		.validator_count(3)
		.nominate(false)
		.validator_pool(true)
		.build(), 
	|| {
		assert_eq!(Staking::era_length(), 1);
		assert_eq!(Staking::validator_count(), 3);
		
		assert_eq!(Staking::minimum_validator_count(), 1);
		assert_eq!(Staking::validator_count(), 3);

		// initial validators 
		assert_eq!(Session::validators(), vec![40, 30, 20, 10]);

		// only one nominator will exist and it will 
		assert_ok!(Staking::bond(Origin::signed(1), 2, 500, RewardDestination::default()));
		assert_ok!(Staking::nominate(Origin::signed(2), vec![10, 20]));

		// 10 and 20 are now valid candidates.
		// trigger era
		System::set_block_number(1);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 1);

		// both validators will be chosen again. NO election algorithm is even executed.
		assert_eq!(Session::validators(), vec![20, 10]);

		// But the exposure is updated in a simple way. Each nominators vote is applied
		assert_eq!(Staking::stakers(10).others.iter().map(|e| e.who).collect::<Vec<BalanceOf<Test>>>(), vec![2]);
		assert_eq!(Staking::stakers(20).others.iter().map(|e| e.who).collect::<Vec<BalanceOf<Test>>>(), vec![2]);
	});
}

#[test]
fn no_candidate_emergency_condition() {
	// Test the situation where the number of validators are less than `ValidatorCount` and less than <MinValidators>
	// The expected behavior is to choose all candidates from the previous era.
	with_externalities(&mut ExtBuilder::default()
		.minimum_validator_count(1)
		.validator_count(3)
		.nominate(false)
		.validator_pool(true)
		.build(), 
	|| {
		assert_eq!(Staking::era_length(), 1);
		assert_eq!(Staking::validator_count(), 3);
		
		assert_eq!(Staking::minimum_validator_count(), 1);
		assert_eq!(Staking::validator_count(), 3);

		// initial validators 
		assert_eq!(Session::validators(), vec![40, 30, 20, 10]);

		// trigger era
		System::set_block_number(1);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 1);

		// No one nominates => no one has a proper vote => no change
		assert_eq!(Session::validators(), vec![40, 30, 20, 10]);
	});
}

#[test]
fn nominating_and_rewards_should_work() {
	// For now it tests a functionality which somehow overlaps with other tests:
	// the fact that the nominator is rewarded properly.
	//
	// PHRAGMEN OUTPUT: running this test with the reference impl gives:
	//
	// Votes  [('2', 500, ['10', '20', '30']), ('4', 500, ['10', '20', '40'])]
	// Sequential Phragmén gives
	// 10  is elected with stake  500.0 and score  0.001
	// 20  is elected with stake  500.0 and score  0.002
	//
	// 2  has load  0.002 and supported
	// 10  with stake  250.0 20  with stake  250.0 30  with stake  0.0
	// 4  has load  0.002 and supported
	// 10  with stake  250.0 20  with stake  250.0 40  with stake  0.0

	with_externalities(&mut ExtBuilder::default()
		.nominate(false)
		.validator_pool(true)
		.build(),
	|| {
		// initial validators 
		assert_eq!(Session::validators(), vec![40, 30, 20, 10]);

		// Set payee to controller
		assert_ok!(Staking::set_payee(Origin::signed(10), RewardDestination::Controller));
		assert_ok!(Staking::set_payee(Origin::signed(20), RewardDestination::Controller));

		// default reward for the first session.
		let session_reward = 10;
		assert_eq!(Staking::current_session_reward(), session_reward);

		// give the man some money
		let initial_balance = 1000;
		for i in [1, 2, 3, 4, 5, 10, 20].iter() {
			let _ = Balances::deposit_creating(i, initial_balance - Balances::total_balance(i));
		}

		// record their balances.
		for i in 1..5 { assert_eq!(Balances::total_balance(&i), initial_balance); }

		// bond two account pairs and state interest in nomination.
		// 2 will nominate for 10, 20, 30
		assert_ok!(Staking::bond(Origin::signed(1), 2, 500, RewardDestination::Controller));
		assert_ok!(Staking::nominate(Origin::signed(2), vec![10, 20, 30]));
		// 4 will nominate for 10, 20, 40
		assert_ok!(Staking::bond(Origin::signed(3), 4, 500, RewardDestination::Stash));
		assert_ok!(Staking::nominate(Origin::signed(4), vec![10, 20, 40]));
	
		System::set_block_number(1);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 1);
		// 10 and 20 have more votes, they will be chosen by phragmen.
		assert_eq!(Session::validators(), vec![20, 10]);
		// validators must have already received some rewards.
		assert_eq!(Balances::total_balance(&10), initial_balance + session_reward);
		assert_eq!(Balances::total_balance(&20), initial_balance + session_reward);

		// ------ check the staked value of all parties.
		// total expo of 10, with 500 coming from nominators (externals), according to phragmen.
		assert_eq!(Staking::stakers(10).own, 1000);
		assert_eq!(Staking::stakers(10).total, 1000 + 500);
		// 2 and 4 supported 10, each with stake 250, according to phragmen.
		assert_eq!(Staking::stakers(10).others.iter().map(|e| e.value).collect::<Vec<BalanceOf<Test>>>(), vec![250, 250]);
		assert_eq!(Staking::stakers(10).others.iter().map(|e| e.who).collect::<Vec<BalanceOf<Test>>>(), vec![4, 2]);
		// total expo of 20, with 500 coming from nominators (externals), according to phragmen.
		assert_eq!(Staking::stakers(20).own, 2000);
		assert_eq!(Staking::stakers(20).total, 2000 + 500);
		// 2 and 4 supported 20, each with stake 250, according to phragmen.
		assert_eq!(Staking::stakers(20).others.iter().map(|e| e.value).collect::<Vec<BalanceOf<Test>>>(), vec![250, 250]);
		assert_eq!(Staking::stakers(20).others.iter().map(|e| e.who).collect::<Vec<BalanceOf<Test>>>(), vec![4, 2]);
		

		System::set_block_number(2);
		// next session reward.
		let new_session_reward = Staking::session_reward() * Staking::slot_stake();
		// nothing else will happen, era ends and rewards are paid again,
		// it is expected that nominators will also be paid. See below
		Session::check_rotate_session(System::block_number());

		// Nominator 2: has [250/1500 ~ 1/6 from 10] + [250/2500 ~ 1/10 from 20]'s reward. ==> 1/6 + 1/10
		assert_eq!(Balances::total_balance(&2), initial_balance + (new_session_reward/6 + new_session_reward/10));
		// The Associated validator will get the other 4/6 --> 1500(total) minus 1/6(250) by each nominator -> 6/6 - 1/6 - 1/6
		assert_eq!(Balances::total_balance(&10), initial_balance + session_reward + 4*new_session_reward/6) ;

		// Nominator 4: has [250/1500 ~ 1/6 from 10] + [250/2500 ~ 1/10 from 20]'s reward. ==> 1/6 + 1/10
		// This nominator chose stash as the reward destination. This means that the reward will go to 3, which is bonded as the stash of 4.
		assert_eq!(Balances::total_balance(&3), initial_balance + (new_session_reward/6 + new_session_reward/10));
		// The Associated validator will get the other 8/10 --> 2500(total) minus 1/10(250) by each nominator -> 10/10 - 1/10 - 1/10
		assert_eq!(Balances::total_balance(&20), initial_balance + session_reward + 8*new_session_reward/10);
	});
}

#[test]
fn nominators_also_get_slashed() {
	// A nominator should be slashed if the validator they nominated is slashed
	with_externalities(&mut ExtBuilder::default().nominate(false).build(), || {
		assert_eq!(Staking::era_length(), 1);
		assert_eq!(Staking::validator_count(), 2);
		// slash happens immediately.
		assert_eq!(Staking::offline_slash_grace(), 0);
		// Account 10 has not been reported offline
		assert_eq!(Staking::slash_count(&10), 0);
		// initial validators
		assert_eq!(Session::validators(), vec![20, 10]);

		// Set payee to controller
		assert_ok!(Staking::set_payee(Origin::signed(10), RewardDestination::Controller));

		// give the man some money.
		let initial_balance = 1000;
		for i in [1, 2, 3, 10].iter() {
			let _ = Balances::deposit_creating(i, initial_balance - Balances::total_balance(i));
		}

		// 2 will nominate for 10
		let nominator_stake = 500;
		assert_ok!(Staking::bond(Origin::signed(1), 2, nominator_stake, RewardDestination::default()));
		assert_ok!(Staking::nominate(Origin::signed(2), vec![20, 10]));

		// new era, pay rewards,
		System::set_block_number(2);
		Session::check_rotate_session(System::block_number());

		// 10 goes offline
		Staking::on_offline_validator(10, 4);
		let slash_value = 2_u64.pow(3) * Staking::current_offline_slash();
		let expo = Staking::stakers(10);
		let actual_slash = expo.own.min(slash_value);
		let nominator_actual_slash = nominator_stake.min(expo.total - actual_slash);
		// initial + first era reward + slash
		assert_eq!(Balances::total_balance(&10), initial_balance + 10 - actual_slash);
		assert_eq!(Balances::total_balance(&2), initial_balance - nominator_actual_slash);
		// Because slashing happened.
		assert!(Staking::forcing_new_era().is_some());
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
		.sessions_per_era(2)
		.build(),
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
fn cannot_transfer_staked_balance() {
	// Tests that a stash account cannot transfer funds
	with_externalities(&mut ExtBuilder::default().build(), || {
		// Confirm account 11 is stashed
		assert_eq!(Staking::bonded(&11), Some(10));
		// Confirm account 11 has some free balance
		assert_eq!(Balances::free_balance(&11), 1000);
		// Confirm account 11 (via controller 10) is totally staked
		assert_eq!(Staking::stakers(&10).total, 1000 + 500);
		// Confirm account 11 cannot transfer as a result
		assert_noop!(Balances::transfer(Origin::signed(11), 20, 1), "account liquidity restrictions prevent withdrawal");

		// Give account 11 extra free balance
		let _ = Balances::deposit_creating(&11, 9999);
		// Confirm that account 11 can now transfer some balance
		assert_ok!(Balances::transfer(Origin::signed(11), 20, 1));
	});
}

#[test]
fn cannot_reserve_staked_balance() {
	// Checks that a bonded account cannot reserve balance from free balance
	with_externalities(&mut ExtBuilder::default().build(), || {
		// Confirm account 11 is stashed
		assert_eq!(Staking::bonded(&11), Some(10));
		// Confirm account 11 has some free balance
		assert_eq!(Balances::free_balance(&11), 1000);
		// Confirm account 11 (via controller 10) is totally staked
		assert_eq!(Staking::stakers(&10).total, 1000 + 500);
		// Confirm account 11 cannot transfer as a result
		assert_noop!(Balances::reserve(&11, 1), "account liquidity restrictions prevent withdrawal");

		// Give account 11 extra free balance
		let _ = Balances::deposit_creating(&11, 9990);
		// Confirm account 11 can now reserve balance
		assert_ok!(Balances::reserve(&11, 1));
	});
}

#[test]
fn reward_destination_works() {
	// Rewards go to the correct destination as determined in Payee
	with_externalities(&mut ExtBuilder::default().build(), || {
		// Check that account 10 is a validator
		assert!(<Validators<Test>>::exists(10));
		// Check the balance of the validator account
		assert_eq!(Balances::free_balance(&10), 1);
		// Check the balance of the stash account
		assert_eq!(Balances::free_balance(&11), 1000);
		// Check these two accounts are bonded
		assert_eq!(Staking::bonded(&11), Some(10));
		// Check how much is at stake
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1000, active: 1000, unlocking: vec![] }));
		// Track current session reward
		let mut current_session_reward = Staking::current_session_reward();

		// Move forward the system for payment
		System::set_block_number(1);
		Timestamp::set_timestamp(5);
		Session::check_rotate_session(System::block_number());

		// Check that RewardDestination is Staked (default)
		assert_eq!(Staking::payee(&10), RewardDestination::Staked);
		// Check current session reward is 10
		assert_eq!(current_session_reward, 10);
		// Check that reward went to the stash account of validator
		// 1/3 of the reward is for the nominator.
		let validator_reward = (10. * (2./3.)) as u64; // = 6
		assert_eq!(Balances::free_balance(&11), 1000 + validator_reward);
		// Check that amount at stake increased accordingly
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1000 + 6, active: 1000 + 6, unlocking: vec![] }));
		// Update current session reward
		current_session_reward = Staking::current_session_reward();

		//Change RewardDestination to Stash
		<Payee<Test>>::insert(&10, RewardDestination::Stash);

		// Move forward the system for payment
		System::set_block_number(2);
		Timestamp::set_timestamp(10);
		Session::check_rotate_session(System::block_number());

		// Check that RewardDestination is Stash
		assert_eq!(Staking::payee(&10), RewardDestination::Stash);
		// Check that reward went to the stash account
		let new_validator_reward = ((1000 + 6) as f64 / ( (1000 + 6) + (500 + 4) ) as f64) * current_session_reward as f64;
		assert_eq!(Balances::free_balance(&11), 1000 + validator_reward + new_validator_reward as u64);
		// Check that amount at stake is not increased
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1006, active: 1006, unlocking: vec![] }));

		//Change RewardDestination to Controller
		<Payee<Test>>::insert(&10, RewardDestination::Controller);

		// Check controller balance
		assert_eq!(Balances::free_balance(&10), 1);


		// Move forward the system for payment
		System::set_block_number(3);
		Timestamp::set_timestamp(15);
		Session::check_rotate_session(System::block_number());

		// Check that RewardDestination is Controller
		assert_eq!(Staking::payee(&10), RewardDestination::Controller);
		// Check that reward went to the controller account
		let reward_of = |w| Staking::stakers(w).own * Staking::current_session_reward() / Staking::stakers(w).total;
		assert_eq!(Balances::free_balance(&10), 1 + reward_of(&10));
		// Check that amount at stake is not increased
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1006, active: 1006, unlocking: vec![] }));
	});
}

#[test]
fn validator_payment_prefs_work() {
	// Test that validator preferences are correctly honored
	// Note: unstake threshold is being directly tested in slashing tests.
	// This test will focus on validator payment.
	with_externalities(&mut ExtBuilder::default()
		.session_length(3)
		.sessions_per_era(3)
		.build(),
	|| {
		let session_reward = 10;
		let validator_cut = 5;
		let validator_initial_balance = Balances::total_balance(&11);
		// Initial config should be correct
		assert_eq!(Staking::era_length(), 9);
		assert_eq!(Staking::sessions_per_era(), 3);
		assert_eq!(Staking::last_era_length_change(), 0);
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 0);

		assert_eq!(Staking::current_session_reward(), session_reward);

		// check the balance of a validator accounts.
		assert_eq!(Balances::total_balance(&10), 1);
		// check the balance of a validator's stash accounts.
		assert_eq!(Balances::total_balance(&11), validator_initial_balance);
		// and the nominator (to-be)
		assert_eq!(Balances::total_balance(&2), 20);

		// add a dummy nominator.
		// NOTE: this nominator is being added 'manually', use '.nominate()' to do it realistically.
		<Stakers<Test>>::insert(&10, Exposure {
			own: 500, // equal division indicates that the reward will be equally divided among validator and nominator.
			total: 1000,
			others: vec![IndividualExposure {who: 2, value: 500 }]
		});
		<Payee<Test>>::insert(&2, RewardDestination::Controller);
		<Validators<Test>>::insert(&10, ValidatorPrefs {
			unstake_threshold: 3,
			validator_payment: validator_cut
		});

		// ------------ Fast forward
		let mut block = 3;
		// Block 3 => Session 1 => Era 0
		System::set_block_number(block);
		Timestamp::set_timestamp(block*5);	// on time.
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 1);

		// session triggered: the reward value stashed should be 10 -- defined in ExtBuilder genesis.
		assert_eq!(Staking::current_session_reward(), session_reward);
		assert_eq!(Staking::current_era_reward(), session_reward);
		
		block = 6; // Block 6 => Session 2 => Era 0
		System::set_block_number(block);
		Timestamp::set_timestamp(block*5);	// a little late.
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 2);

		assert_eq!(Staking::current_session_reward(), session_reward);
		assert_eq!(Staking::current_era_reward(), 2*session_reward);

		block = 9; // Block 9 => Session 3 => Era 1
		System::set_block_number(block);
		Timestamp::set_timestamp(block*5);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 1);
		assert_eq!(Session::current_index(), 3);

		// whats left to be shared is the sum of 3 rounds minus the validator's cut.
		let shared_cut = 3 * session_reward - validator_cut;
		// Validator's payee is Staked account, 11, reward will be paid here.
		assert_eq!(Balances::total_balance(&11), validator_initial_balance + shared_cut/2 + validator_cut);
		// Controller account will not get any reward.
		assert_eq!(Balances::total_balance(&10), 1);
		// Rest of the reward will be shared and paid to the nominator in stake.
		assert_eq!(Balances::total_balance(&2), 20 + shared_cut/2);
	});

}

#[test]
fn bond_extra_works() {
	// Tests that extra `free_balance` in the stash can be added to stake
	// NOTE: this tests only verifies `StakingLedger` for correct updates. 
	// See `bond_extra_and_withdraw_unbonded_works` for more details and updates on `Exposure`.
	with_externalities(&mut ExtBuilder::default().build(),
	|| {
		// Check that account 10 is a validator
		assert!(<Validators<Test>>::exists(10));
		// Check that account 10 is bonded to account 11
		assert_eq!(Staking::bonded(&11), Some(10));
		// Check how much is at stake
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1000, active: 1000, unlocking: vec![] }));

		// Give account 11 some large free balance greater than total
		let _ = Balances::deposit_creating(&11, 999000);
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
fn bond_extra_and_withdraw_unbonded_works() {
	// * Should test
	// * Given an account being bonded [and chosen as a validator](not mandatory)
	// * It can add extra funds to the bonded account.
	// * it can unbond a portion of its funds from the stash account.
	// * Once the unbonding period is done, it can actually take the funds out of the stash.
	with_externalities(&mut ExtBuilder::default()
		.reward(10) // it is the default, just for verbosity
		.nominate(false)
		.build(), 
	|| {
		// Set payee to controller. avoids confusion
		assert_ok!(Staking::set_payee(Origin::signed(10), RewardDestination::Controller));

		// Set unbonding era (bonding_duration) to 2
		assert_ok!(Staking::set_bonding_duration(2));

		// Give account 11 some large free balance greater than total
		let _ = Balances::deposit_creating(&11, 999000);
		// Check the balance of the stash account
		assert_eq!(Balances::free_balance(&11), 1000000);

		// Initial config should be correct
		assert_eq!(Staking::sessions_per_era(), 1);
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 0);

		assert_eq!(Staking::current_session_reward(), 10);

		// check the balance of a validator accounts.
		assert_eq!(Balances::total_balance(&10), 1);

		// confirm that 10 is a normal validator and gets paid at the end of the era.
		System::set_block_number(1);
		Timestamp::set_timestamp(5);
		Session::check_rotate_session(System::block_number()); 
		assert_eq!(Staking::current_era(), 1);
		assert_eq!(Session::current_index(), 1);

		// NOTE: despite having .nominate() in extBuilder, 20 doesn't have a share since
		// rewards are paid before election in new_era()
		assert_eq!(Balances::total_balance(&10), 1 + 10);

		// Initial state of 10
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1000, active: 1000, unlocking: vec![] }));
		assert_eq!(Staking::stakers(&10), Exposure { total: 1000, own: 1000, others: vec![] });


		// deposit the extra 100 units 
		Staking::bond_extra(Origin::signed(10), 100).unwrap();

		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1000 + 100, active: 1000 + 100, unlocking: vec![] }));
		// Exposure is a snapshot! only updated after the next era update.
		assert_ne!(Staking::stakers(&10), Exposure { total: 1000 + 100, own: 1000 + 100, others: vec![] });

		// trigger next era.
		System::set_block_number(2);Timestamp::set_timestamp(10);Session::check_rotate_session(System::block_number()); 
		assert_eq!(Staking::current_era(), 2);
		assert_eq!(Session::current_index(), 2);

		// ledger should be the same.
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1000 + 100, active: 1000 + 100, unlocking: vec![] }));
		// Exposure is now updated.
		assert_eq!(Staking::stakers(&10), Exposure { total: 1000 + 100, own: 1000 + 100, others: vec![] });
		// Note that by this point 10 also have received more rewards, but we don't care now.
		// assert_eq!(Balances::total_balance(&10), 1 + 10 + MORE_REWARD);

		// Unbond almost all of the funds in stash.
		Staking::unbond(Origin::signed(10), 1000).unwrap();
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { 
			stash: 11, total: 1000 + 100, active: 100, unlocking: vec![UnlockChunk{ value: 1000, era: 2 + 2}] }));

		// Attempting to free the balances now will fail. 2 eras need to pass.
		Staking::withdraw_unbonded(Origin::signed(10)).unwrap();
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { 
			stash: 11, total: 1000 + 100, active: 100, unlocking: vec![UnlockChunk{ value: 1000, era: 2 + 2}] }));

		// trigger next era.
		System::set_block_number(3);Timestamp::set_timestamp(15);Session::check_rotate_session(System::block_number()); 
		assert_eq!(Staking::current_era(), 3);
		assert_eq!(Session::current_index(), 3);

		// nothing yet
		Staking::withdraw_unbonded(Origin::signed(10)).unwrap();
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { 
			stash: 11, total: 1000 + 100, active: 100, unlocking: vec![UnlockChunk{ value: 1000, era: 2 + 2}] }));

		// trigger next era.
		System::set_block_number(4);Timestamp::set_timestamp(20);Session::check_rotate_session(System::block_number()); 
		assert_eq!(Staking::current_era(), 4);
		assert_eq!(Session::current_index(), 4);
		
		Staking::withdraw_unbonded(Origin::signed(10)).unwrap();
		// Now the value is free and the staking ledger is updated.
		assert_eq!(Staking::ledger(&10), Some(StakingLedger { 
			stash: 11, total: 100, active: 100, unlocking: vec![] }));
	})
}

#[test]
fn slot_stake_is_least_staked_validator_and_limits_maximum_punishment() {
	// Test that slot_stake is determined by the least staked validator
	// Test that slot_stake is the maximum punishment that can happen to a validator
	// Note that rewardDestination is the stash account by default
	// Note that unlike reward slash will affect free_balance, not the stash account.
	with_externalities(&mut ExtBuilder::default().nominate(false).build(), || {
		// Confirm validator count is 2
		assert_eq!(Staking::validator_count(), 2);
		// Confirm account 10 and 20 are validators
		assert!(<Validators<Test>>::exists(&10) && <Validators<Test>>::exists(&20));
		// Confirm 10 has less stake than 20
		assert!(Staking::stakers(&10).total < Staking::stakers(&20).total);
		assert_eq!(Staking::stakers(&10).total, 1000);
		assert_eq!(Staking::stakers(&20).total, 2000);

		// Give the man some money.
		let _ = Balances::deposit_creating(&10, 999);
		let _ = Balances::deposit_creating(&20, 999);

		// Confirm initial free balance.
		assert_eq!(Balances::free_balance(&10), 1000);
		assert_eq!(Balances::free_balance(&20), 1000);

		// We confirm initialized slot_stake is this value
		assert_eq!(Staking::slot_stake(), Staking::stakers(&10).total);
		
		// Now lets lower account 20 stake
		<Stakers<Test>>::insert(&20, Exposure { total: 69, own: 69, others: vec![] });
		assert_eq!(Staking::stakers(&20).total, 69);
		<Ledger<Test>>::insert(&20, StakingLedger { stash: 22, total: 69, active: 69, unlocking: vec![] });

		// New era --> rewards are paid --> stakes are changed
		System::set_block_number(1);
		Timestamp::set_timestamp(5);
		Session::check_rotate_session(System::block_number());

		assert_eq!(Staking::current_era(), 1);
		// -- new balances + reward
		assert_eq!(Staking::stakers(&10).total, 1000 + 10);
		assert_eq!(Staking::stakers(&20).total, 69 + 10);

		// -- Note that rewards are going directly to stash, not as free balance.
		assert_eq!(Balances::free_balance(&10), 1000);
		assert_eq!(Balances::free_balance(&20), 1000);

		// -- slot stake should also be updated.
		assert_eq!(Staking::slot_stake(), 79);

		// // If 10 gets slashed now, despite having +1000 in stash, it will be slashed byt 79, which is the slot stake
		Staking::on_offline_validator(10, 4);
		// // Confirm user has been reported
		assert_eq!(Staking::slash_count(&10), 4);
		// // check the balance of 10 (slash will be deducted from free balance.)
		assert_eq!(Balances::free_balance(&10), 1000 - 79);
		
	});
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
		assert_eq!(Balances::free_balance(&11), 256000);
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
		Balances::slash(&10, u64::max_value());
		// Check total balance of account 10
		assert_eq!(Balances::total_balance(&10), 0);

		// Check the balance of the stash account has not been touched
		assert_eq!(Balances::free_balance(&11), 256000);
		// Check these two accounts are still bonded
		assert_eq!(Staking::bonded(&11), Some(10));

		// Check storage items have not changed
		assert!(<Ledger<Test>>::exists(&10));
		assert!(<Validators<Test>>::exists(&10));
		assert!(<SlashCount<Test>>::exists(&10));
		assert!(<Payee<Test>>::exists(&10));

		// Reduce free_balance of stash to 0
		Balances::slash(&11, u64::max_value());
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
		assert_eq!(Balances::free_balance(&11), 256000);
		// Check these two accounts are bonded
		assert_eq!(Staking::bonded(&11), Some(10));

		// Set payee information
		assert_ok!(Staking::set_payee(Origin::signed(10), RewardDestination::Stash));


		// Check storage items that should be cleaned up
		assert!(<Ledger<Test>>::exists(&10));
		assert!(<Nominators<Test>>::exists(&10));
		assert!(<Payee<Test>>::exists(&10));

		// Reduce free_balance of controller to 0
		Balances::slash(&10, u64::max_value());
		// Check total balance of account 10
		assert_eq!(Balances::total_balance(&10), 0);

		// Check the balance of the stash account has not been touched
		assert_eq!(Balances::free_balance(&11), 256000);
		// Check these two accounts are still bonded
		assert_eq!(Staking::bonded(&11), Some(10));

		// Check storage items have not changed
		assert!(<Ledger<Test>>::exists(&10));
		assert!(<Nominators<Test>>::exists(&10));
		assert!(<Payee<Test>>::exists(&10));

		// Reduce free_balance of stash to 0
		Balances::slash(&11, u64::max_value());
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
fn phragmen_poc_works() {
	// Tests the POC test of the phragmen, mentioned in the paper and reference implementation.
	// Initial votes:
	// vote_list = [
	// 		("A", 10.0, ["X", "Y"]),
	// 		("B", 20.0, ["X", "Z"]),
	// 		("C", 30.0, ["Y", "Z"])
	// ]
	//
	// Sequential Phragmén gives
	// Z  is elected with stake  35.0 and score  0.02
	// Y  is elected with stake  25.0 and score  0.04
	//
	// A  has load  0.04 and supported 
	// X  with stake  0.0 Y  with stake  10.0 
	// B  has load  0.02 and supported 
	// X  with stake  0.0 Z  with stake  20.0 
	// C  has load  0.04 and supported 
	// Y  with stake  15.0 Z  with stake  15.0 
	// 
	// NOTE: doesn't X/Y/Z's stash value make a difference here in phragmen? 
	with_externalities(&mut ExtBuilder::default()
		.nominate(false)
		.build(),
	|| {
		// initial setup of 10 and 20, both validators.
		assert_eq!(Session::validators(), vec![20, 10]);

		assert_eq!(Staking::ledger(&10), Some(StakingLedger { stash: 11, total: 1000, active: 1000, unlocking: vec![] }));
		assert_eq!(Staking::ledger(&20), Some(StakingLedger { stash: 21, total: 2000, active: 2000, unlocking: vec![] }));

		assert_eq!(Staking::validators(10), ValidatorPrefs::default());
		assert_eq!(Staking::validators(20), ValidatorPrefs::default());

		assert_eq!(Balances::free_balance(10), 1);
		assert_eq!(Balances::free_balance(20), 1);
		
		// no one is a nominator
		assert_eq!(<Nominators<Test>>::enumerate().count(), 0 as usize);

		// Bond [30, 31] as the third validator
		assert_ok!(Staking::bond(Origin::signed(31), 30, 1000, RewardDestination::default()));
		assert_ok!(Staking::validate(Origin::signed(30), ValidatorPrefs::default()));

		// bond [2,1](A), [4,3](B), [6,5](C) as the 3 nominators
		// Give all of them some balance to be able to bond properly.
		for i in &[1, 3, 5] { let _ = Balances::deposit_creating(i, 50); }
		// Linking names to the above test:
		// 10 => X
		// 20 => Y
		// 30 => Z
		assert_ok!(Staking::bond(Origin::signed(1), 2, 10, RewardDestination::default()));
		assert_ok!(Staking::nominate(Origin::signed(2), vec![10, 20]));

		assert_ok!(Staking::bond(Origin::signed(3), 4, 20, RewardDestination::default()));
		assert_ok!(Staking::nominate(Origin::signed(4), vec![10, 30]));

		assert_ok!(Staking::bond(Origin::signed(5), 6, 30, RewardDestination::default()));
		assert_ok!(Staking::nominate(Origin::signed(6), vec![20, 30]));

		// New era => election algorithm will trigger
		System::set_block_number(1);
		Session::check_rotate_session(System::block_number());

		// Z and Y are chosen 
		assert_eq!(Session::validators(), vec![30, 20]);

		// with stake 35 and 25 respectively

		// This is only because 30 has been bonded on the fly, exposures are stored at the very end of the era. 
		// 35 is the point, not 'own' Exposure.
		assert_eq!(Staking::stakers(30).own, 0); 
		assert_eq!(Staking::stakers(30).total, 0 + 35);
		// same as above. +25 is the point
		assert_eq!(Staking::stakers(20).own, 2010);
		assert_eq!(Staking::stakers(20).total, 2010 + 25);  

		// 30(Z) was supported by B-4 and C-6 with stake 20 and 15 respectively.
		assert_eq!(Staking::stakers(30).others.iter().map(|e| e.value).collect::<Vec<BalanceOf<Test>>>(), vec![15, 20]);
		assert_eq!(Staking::stakers(30).others.iter().map(|e| e.who).collect::<Vec<BalanceOf<Test>>>(), vec![6, 4]);
		
		// 20(Y) was supported by A-2 and C-6 with stake 10 and 15 respectively.
		assert_eq!(Staking::stakers(20).others.iter().map(|e| e.value).collect::<Vec<BalanceOf<Test>>>(), vec![15, 10]);
		assert_eq!(Staking::stakers(20).others.iter().map(|e| e.who).collect::<Vec<BalanceOf<Test>>>(), vec![6, 2]);
	});
}

#[test]
fn phragmen_election_works() {
	// tests the encapsulated phragmen::elect function.
	with_externalities(&mut ExtBuilder::default().nominate(false).build(), || {
		// initial setup of 10 and 20, both validators
		assert_eq!(Session::validators(), vec![20, 10]);

		// no one is a nominator
		assert_eq!(<Nominators<Test>>::enumerate().count(), 0 as usize);

		// Bond [30, 31] as the third validator
		assert_ok!(Staking::bond(Origin::signed(31), 30, 1000, RewardDestination::default()));
		assert_ok!(Staking::validate(Origin::signed(30), ValidatorPrefs::default()));

		// bond [2,1](A), [4,3](B), as 2 nominators
		// Give all of them some balance to be able to bond properly.
		for i in &[1, 3] { let _ = Balances::deposit_creating(i, 50); }
		assert_ok!(Staking::bond(Origin::signed(1), 2, 5, RewardDestination::default()));
		assert_ok!(Staking::nominate(Origin::signed(2), vec![10, 20]));

		assert_ok!(Staking::bond(Origin::signed(3), 4, 45, RewardDestination::default()));
		assert_ok!(Staking::nominate(Origin::signed(4), vec![10, 30]));

		let rounds =     || 2 as usize;
		let validators = || <Validators<Test>>::enumerate();
		let nominators = || <Nominators<Test>>::enumerate();
		let stash_of =  |w| Staking::stash_balance(&w);
		let min_validator_count = Staking::minimum_validator_count() as usize;

		let winners = phragmen::elect::<Test, _, _, _, _>(
			rounds,
			validators,
			nominators,
			stash_of,
			min_validator_count
		);

		// 10 and 30 must be the winners
		assert_eq!(winners.iter().map(|w| w.who).collect::<Vec<BalanceOf<Test>>>(), vec![10, 30]);

		let winner_10 = winners.iter().filter(|w| w.who == 10).nth(0).unwrap();
		let winner_30 = winners.iter().filter(|w| w.who == 30).nth(0).unwrap();

		// python implementation output:
		/*
		10  is elected with stake  26.31578947368421 and score  0.02
		30  is elected with stake  23.684210526315788 and score  0.042222222222222223

		2  has load  0.02 and supported 
		10  with stake  5.0 20  with stake  0.0 
		4  has load  0.042222222222222223 and supported 
		10  with stake  21.31578947368421 30  with stake  23.684210526315788 
		*/

		assert_eq!(winner_10.exposure.total, 1000 + 26);
		assert_eq!(winner_10.score, Perquintill::from_fraction(0.02));
		assert_eq!(winner_10.exposure.others[0].value, 21);
		assert_eq!(winner_10.exposure.others[1].value, 5);

		assert_eq!(winner_30.exposure.total, 23);
		assert_eq!(winner_30.score, Perquintill::from_quintillionths(42222222222222222));
		assert_eq!(winner_30.exposure.others[0].value, 23);
	})
}

#[test]
fn switching_roles() {
	// Show: It should be possible to switch between roles (nominator, validator, idle) with minimal overhead.
	with_externalities(&mut ExtBuilder::default()
		.nominate(false)
		.sessions_per_era(3)
		.build(),
	|| {
		assert_eq!(Session::validators(), vec![20, 10]);

		// put some money in account that we'll use.
		for i in 1..7 { let _ = Balances::deposit_creating(&i, 5000); }

		// add 2 nominators
		assert_ok!(Staking::bond(Origin::signed(1), 2, 2000, RewardDestination::default()));
		assert_ok!(Staking::nominate(Origin::signed(2), vec![10, 6]));

		assert_ok!(Staking::bond(Origin::signed(3), 4, 500, RewardDestination::default()));
		assert_ok!(Staking::nominate(Origin::signed(4), vec![20, 2]));
		
		// add a new validator candidate
		assert_ok!(Staking::bond(Origin::signed(5), 6, 1500, RewardDestination::Controller));
		assert_ok!(Staking::validate(Origin::signed(6), ValidatorPrefs::default()));

		// new block 
		System::set_block_number(1);
		Session::check_rotate_session(System::block_number());

		// no change 
		assert_eq!(Session::validators(), vec![20, 10]);

		// new block 
		System::set_block_number(2);
		Session::check_rotate_session(System::block_number());

		// no change 
		assert_eq!(Session::validators(), vec![20, 10]);

		// new block --> ne era --> new validators
		System::set_block_number(3);
		Session::check_rotate_session(System::block_number());

		// with current nominators 10 and 4 have the most stake
		assert_eq!(Session::validators(), vec![6, 10]);

		// 2 decides to be a validator. Consequences: 
		// 6 will not be chosen in the next round (no votes)
		// 2 itself will be chosen + 20 who now has the higher votes
		// 10 wil have no votes.
		assert_ok!(Staking::validate(Origin::signed(2), ValidatorPrefs::default()));

		System::set_block_number(4);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::validators(), vec![6, 10]);

		System::set_block_number(5);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::validators(), vec![6, 10]);

		// ne era 
		System::set_block_number(6);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::validators(), vec![2, 20]);
	});
}

#[test]
fn wrong_vote_is_null() {
	with_externalities(&mut ExtBuilder::default()
		.session_length(1)
		.sessions_per_era(1)
		.nominate(false)
		.validator_pool(true)
	.build(),
	|| {
		// from the first era onward, only two will be chosen
		assert_eq!(Session::validators(), vec![40, 30, 20, 10]);

		// put some money in account that we'll use.
		for i in 1..3 { let _ = Balances::deposit_creating(&i, 5000); }

		// add 1 nominators
		assert_ok!(Staking::bond(Origin::signed(1), 2, 2000, RewardDestination::default()));
		assert_ok!(Staking::nominate(Origin::signed(2), vec![
			10, 20, 			// good votes 
			1, 2, 15, 1000, 25  // crap votes. No effect.
		]));

		// new block 
		System::set_block_number(1);
		Session::check_rotate_session(System::block_number());

		assert_eq!(Session::validators(), vec![20, 10]);
	});
}
