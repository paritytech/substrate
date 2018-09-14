// Copyright 2017 Parity Technologies (UK) Ltd.
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
use consensus::OnOfflineValidator;
use runtime_io::with_externalities;
use mock::{Balances, Session, Staking, System, Timestamp, Test, new_test_ext, Origin};

#[test]
fn note_null_offline_should_work() {
	with_externalities(&mut new_test_ext(0, 3, 3, 0, true, 10), || {
		assert_eq!(Staking::offline_slash_grace(), 0);
		assert_eq!(Staking::slash_count(&10), 0);
		assert_eq!(Balances::free_balance(&10), 1);
		System::set_extrinsic_index(1);
		assert_eq!(Staking::slash_count(&10), 0);
		assert_eq!(Balances::free_balance(&10), 1);
		assert!(Staking::forcing_new_era().is_none());
	});
}

#[test]
fn note_offline_should_work() {
	with_externalities(&mut new_test_ext(0, 3, 3, 0, true, 10), || {
		Balances::set_free_balance(&10, 70);
		assert_eq!(Staking::offline_slash_grace(), 0);
		assert_eq!(Staking::slash_count(&10), 0);
		assert_eq!(Balances::free_balance(&10), 70);
		System::set_extrinsic_index(1);
		Staking::on_offline_validator(0);
		assert_eq!(Staking::slash_count(&10), 1);
		assert_eq!(Balances::free_balance(&10), 50);
		assert!(Staking::forcing_new_era().is_none());
	});
}

#[test]
fn note_offline_exponent_should_work() {
	with_externalities(&mut new_test_ext(0, 3, 3, 0, true, 10), || {
		Balances::set_free_balance(&10, 150);
		assert_eq!(Staking::offline_slash_grace(), 0);
		assert_eq!(Staking::slash_count(&10), 0);
		assert_eq!(Balances::free_balance(&10), 150);
		System::set_extrinsic_index(1);
		Staking::on_offline_validator(0);
		assert_eq!(Staking::slash_count(&10), 1);
		assert_eq!(Balances::free_balance(&10), 130);
		System::set_extrinsic_index(1);
		Staking::on_offline_validator(0);
		assert_eq!(Staking::slash_count(&10), 2);
		assert_eq!(Balances::free_balance(&10), 90);
		assert!(Staking::forcing_new_era().is_none());
	});
}

#[test]
fn note_offline_grace_should_work() {
	with_externalities(&mut new_test_ext(0, 3, 3, 0, true, 10), || {
		Balances::set_free_balance(&10, 70);
		Balances::set_free_balance(&20, 70);
		assert_ok!(Staking::set_offline_slash_grace(1));
		assert_eq!(Staking::offline_slash_grace(), 1);

		assert_eq!(Staking::slash_count(&10), 0);
		assert_eq!(Balances::free_balance(&10), 70);

		System::set_extrinsic_index(1);
		Staking::on_offline_validator(0);
		assert_eq!(Staking::slash_count(&10), 1);
		assert_eq!(Balances::free_balance(&10), 70);
		assert_eq!(Staking::slash_count(&20), 0);
		assert_eq!(Balances::free_balance(&20), 70);

		System::set_extrinsic_index(1);
		Staking::on_offline_validator(0);
		Staking::on_offline_validator(1);
		assert_eq!(Staking::slash_count(&10), 2);
		assert_eq!(Balances::free_balance(&10), 50);
		assert_eq!(Staking::slash_count(&20), 1);
		assert_eq!(Balances::free_balance(&20), 70);
		assert!(Staking::forcing_new_era().is_none());
	});
}

#[test]
fn note_offline_force_unstake_session_change_should_work() {
	with_externalities(&mut new_test_ext(0, 3, 3, 0, true, 10), || {
		Balances::set_free_balance(&10, 70);
		Balances::set_free_balance(&20, 70);
		assert_ok!(Staking::stake(Origin::signed(1)));
		
		assert_eq!(Staking::slash_count(&10), 0);
		assert_eq!(Balances::free_balance(&10), 70);
		assert_eq!(Staking::intentions(), vec![10, 20, 1]);
		assert_eq!(Session::validators(), vec![10, 20]);

		System::set_extrinsic_index(1);
		Staking::on_offline_validator(0);
		assert_eq!(Balances::free_balance(&10), 50);
		assert_eq!(Staking::slash_count(&10), 1);
		assert_eq!(Staking::intentions(), vec![10, 20, 1]);

		System::set_extrinsic_index(1);
		Staking::on_offline_validator(0);
		assert_eq!(Staking::intentions(), vec![1, 20]);
		assert_eq!(Balances::free_balance(&10), 10);
		assert!(Staking::forcing_new_era().is_some());
	});
}

#[test]
fn note_offline_auto_unstake_session_change_should_work() {
	with_externalities(&mut new_test_ext(0, 3, 3, 0, true, 10), || {
		Balances::set_free_balance(&10, 7000);
		Balances::set_free_balance(&20, 7000);
		assert_ok!(Staking::register_preferences(Origin::signed(10), 0, ValidatorPrefs { unstake_threshold: 1, validator_payment: 0 }));
		
		assert_eq!(Staking::intentions(), vec![10, 20]);

		System::set_extrinsic_index(1);
		Staking::on_offline_validator(0);
		Staking::on_offline_validator(1);
		assert_eq!(Balances::free_balance(&10), 6980);
		assert_eq!(Balances::free_balance(&20), 6980);
		assert_eq!(Staking::intentions(), vec![10, 20]);
		assert!(Staking::forcing_new_era().is_none());

		System::set_extrinsic_index(1);
		Staking::on_offline_validator(0);
		Staking::on_offline_validator(1);
		assert_eq!(Balances::free_balance(&10), 6940);
		assert_eq!(Balances::free_balance(&20), 6940);
		assert_eq!(Staking::intentions(), vec![20]);
		assert!(Staking::forcing_new_era().is_some());

		System::set_extrinsic_index(1);
		Staking::on_offline_validator(1);
		assert_eq!(Balances::free_balance(&10), 6940);
		assert_eq!(Balances::free_balance(&20), 6860);
		assert_eq!(Staking::intentions(), vec![20]);

		System::set_extrinsic_index(1);
		Staking::on_offline_validator(1);
		assert_eq!(Balances::free_balance(&10), 6940);
		assert_eq!(Balances::free_balance(&20), 6700);
		assert_eq!(Staking::intentions(), vec![0u64; 0]);
	});
}


#[test]
fn rewards_should_work() {
	with_externalities(&mut new_test_ext(0, 3, 3, 0, true, 10), || {
		assert_eq!(Staking::era_length(), 9);
		assert_eq!(Staking::sessions_per_era(), 3);
		assert_eq!(Staking::last_era_length_change(), 0);
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 0);
		assert_eq!(Balances::total_balance(&10), 1);

		System::set_block_number(3);
		Timestamp::set_timestamp(15);	// on time.
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 1);
		assert_eq!(Balances::total_balance(&10), 11);
		System::set_block_number(6);
		Timestamp::set_timestamp(31);	// a little late
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 2);
		assert_eq!(Balances::total_balance(&10), 20);	// less reward
		System::set_block_number(9);
		Timestamp::set_timestamp(50);	// very late
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 1);
		assert_eq!(Session::current_index(), 3);
		assert_eq!(Balances::total_balance(&10), 27);	// much less reward
	});
}

#[test]
fn slashing_should_work() {
	with_externalities(&mut new_test_ext(0, 3, 3, 0, true, 10), || {
		assert_eq!(Staking::era_length(), 9);
		assert_eq!(Staking::sessions_per_era(), 3);
		assert_eq!(Staking::last_era_length_change(), 0);
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 0);
		assert_eq!(Balances::total_balance(&10), 1);

		System::set_block_number(3);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 1);
		assert_eq!(Balances::total_balance(&10), 11);

		System::set_block_number(6);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::current_index(), 2);
		assert_eq!(Balances::total_balance(&10), 21);

		System::set_block_number(7);
		System::set_extrinsic_index(1);
		Staking::on_offline_validator(0);
		Staking::on_offline_validator(1);
		assert_eq!(Balances::total_balance(&10), 1);
	});
}



#[test]
fn staking_should_work() {
	with_externalities(&mut new_test_ext(0, 1, 2, 0, true, 0), || {

		assert_eq!(Staking::era_length(), 2);
		assert_eq!(Staking::validator_count(), 2);
		assert_eq!(Session::validators(), vec![10, 20]);
		
		assert_ok!(Staking::set_bonding_duration(2));
		assert_eq!(Staking::bonding_duration(), 2);

		// Block 1: Add three validators. No obvious change.
		System::set_block_number(1);
		assert_ok!(Staking::stake(Origin::signed(1)));
		assert_ok!(Staking::stake(Origin::signed(2)));
		assert_ok!(Staking::stake(Origin::signed(4)));
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 0);
		assert_eq!(Session::validators(), vec![10, 20]);

		// Block 2: New validator set now.
		System::set_block_number(2);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 1);
		assert_eq!(Session::validators(), vec![4, 2]);

		// Block 3: Unstake highest, introduce another staker. No change yet.
		System::set_block_number(3);
		assert_ok!(Staking::stake(Origin::signed(3)));
		assert_ok!(Staking::unstake(Origin::signed(4), Staking::intentions().iter().position(|&x| x == 4).unwrap() as u32));
		assert_eq!(Staking::current_era(), 1);
		Session::check_rotate_session(System::block_number());

		// Block 4: New era - validators change.
		System::set_block_number(4);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 2);
		assert_eq!(Session::validators(), vec![3, 2]);

		// Block 5: Transfer stake from highest to lowest. No change yet.
		System::set_block_number(5);
		assert_ok!(Balances::transfer(Origin::signed(4), 1.into(), 40));
		Session::check_rotate_session(System::block_number());

		// Block 6: Lowest now validator.
		System::set_block_number(6);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::validators(), vec![1, 3]);

		// Block 7: Unstake three. No change yet.
		System::set_block_number(7);
		assert_ok!(Staking::unstake(Origin::signed(3), Staking::intentions().iter().position(|&x| x == 3).unwrap() as u32));
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::validators(), vec![1, 3]);

		// Block 8: Back to one and two.
		System::set_block_number(8);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::validators(), vec![1, 2]);
	});
}

#[test]
fn nominating_and_rewards_should_work() {
	with_externalities(&mut new_test_ext(0, 1, 1, 0, true, 10), || {
		assert_eq!(Staking::era_length(), 1);
		assert_eq!(Staking::validator_count(), 2);
		assert_eq!(Staking::bonding_duration(), 3);
		assert_eq!(Session::validators(), vec![10, 20]);

		System::set_block_number(1);
		assert_ok!(Staking::stake(Origin::signed(1)));
		assert_ok!(Staking::stake(Origin::signed(2)));
		assert_ok!(Staking::stake(Origin::signed(3)));
		assert_ok!(Staking::nominate(Origin::signed(4), 1.into()));
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 1);
		assert_eq!(Session::validators(), vec![1, 3]);	// 4 + 1, 3
		assert_eq!(Balances::total_balance(&1), 10);
		assert_eq!(Balances::total_balance(&2), 20);
		assert_eq!(Balances::total_balance(&3), 30);
		assert_eq!(Balances::total_balance(&4), 40);

		System::set_block_number(2);
		assert_ok!(Staking::unnominate(Origin::signed(4), 0));
		Session::check_rotate_session(System::block_number());
		assert_eq!(Staking::current_era(), 2);
		assert_eq!(Session::validators(), vec![3, 2]);
		assert_eq!(Balances::total_balance(&1), 12);
		assert_eq!(Balances::total_balance(&2), 20);
		assert_eq!(Balances::total_balance(&3), 40);
		assert_eq!(Balances::total_balance(&4), 48);

		System::set_block_number(3);
		assert_ok!(Staking::stake(Origin::signed(4)));
		assert_ok!(Staking::unstake(Origin::signed(3), Staking::intentions().iter().position(|&x| x == 3).unwrap() as u32));
		assert_ok!(Staking::nominate(Origin::signed(3), 1.into()));
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::validators(), vec![1, 4]);
		assert_eq!(Balances::total_balance(&1), 12);
		assert_eq!(Balances::total_balance(&2), 30);
		assert_eq!(Balances::total_balance(&3), 50);
		assert_eq!(Balances::total_balance(&4), 48);

		System::set_block_number(4);
		Session::check_rotate_session(System::block_number());
		assert_eq!(Balances::total_balance(&1), 13);
		assert_eq!(Balances::total_balance(&2), 30);
		assert_eq!(Balances::total_balance(&3), 58);
		assert_eq!(Balances::total_balance(&4), 58);
	});
}

#[test]
fn rewards_with_off_the_table_should_work() {
	with_externalities(&mut new_test_ext(0, 1, 1, 0, true, 10), || {
		System::set_block_number(1);
		assert_ok!(Staking::stake(Origin::signed(1)));
		assert_ok!(Staking::nominate(Origin::signed(2), 1.into()));
		assert_ok!(Staking::stake(Origin::signed(3)));
		Session::check_rotate_session(System::block_number());
		assert_eq!(Session::validators(), vec![1, 3]);	// 1 + 2, 3
		assert_eq!(Balances::total_balance(&1), 10);
		assert_eq!(Balances::total_balance(&2), 20);
		assert_eq!(Balances::total_balance(&3), 30);

		System::set_block_number(2);
		assert_ok!(Staking::register_preferences(Origin::signed(1), Staking::intentions().into_iter().position(|i| i == 1).unwrap() as u32, ValidatorPrefs { unstake_threshold: 3, validator_payment: 4 }));
		Session::check_rotate_session(System::block_number());
		assert_eq!(Balances::total_balance(&1), 16);
		assert_eq!(Balances::total_balance(&2), 24);
		assert_eq!(Balances::total_balance(&3), 40);
	});
}

#[test]
fn nominating_slashes_should_work() {
	with_externalities(&mut new_test_ext(0, 2, 2, 0, true, 10), || {
		assert_eq!(Staking::era_length(), 4);
		assert_eq!(Staking::validator_count(), 2);
		assert_eq!(Staking::bonding_duration(), 12);
		assert_eq!(Session::validators(), vec![10, 20]);

		System::set_block_number(2);
		Session::check_rotate_session(System::block_number());

		Timestamp::set_timestamp(15);
		System::set_block_number(4);
		assert_ok!(Staking::stake(Origin::signed(1)));
		assert_ok!(Staking::stake(Origin::signed(3)));
		assert_ok!(Staking::nominate(Origin::signed(2), 3.into()));
		assert_ok!(Staking::nominate(Origin::signed(4), 1.into()));
		Session::check_rotate_session(System::block_number());

		assert_eq!(Staking::current_era(), 1);
		assert_eq!(Session::validators(), vec![1, 3]);	// 1 + 4, 3 + 2
		assert_eq!(Balances::total_balance(&1), 10);
		assert_eq!(Balances::total_balance(&2), 20);
		assert_eq!(Balances::total_balance(&3), 30);
		assert_eq!(Balances::total_balance(&4), 40);

		System::set_block_number(5);
		System::set_extrinsic_index(1);
		Staking::on_offline_validator(0);
		Staking::on_offline_validator(1);
		assert_eq!(Balances::total_balance(&1), 0);
		assert_eq!(Balances::total_balance(&2), 20);
		assert_eq!(Balances::total_balance(&3), 10);
		assert_eq!(Balances::total_balance(&4), 30);
	});
}

#[test]
fn double_staking_should_fail() {
	with_externalities(&mut new_test_ext(0, 1, 2, 0, true, 0), || {
		System::set_block_number(1);
		assert_ok!(Staking::stake(Origin::signed(1)));
		assert_noop!(Staking::stake(Origin::signed(1)), "Cannot stake if already staked.");
		assert_noop!(Staking::nominate(Origin::signed(1), 1.into()), "Cannot nominate if already staked.");
		assert_ok!(Staking::nominate(Origin::signed(2), 1.into()));
		assert_noop!(Staking::stake(Origin::signed(2)), "Cannot stake if already nominating.");
		assert_noop!(Staking::nominate(Origin::signed(2), 1.into()), "Cannot nominate if already nominating.");
	});
}

#[test]
fn staking_eras_work() {
	with_externalities(&mut new_test_ext(0, 1, 2, 0, true, 0), || {
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
fn staking_balance_transfer_when_bonded_should_not_work() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false, 0), || {
		Balances::set_free_balance(&1, 111);
		assert_ok!(Staking::stake(Origin::signed(1)));
		assert_noop!(Balances::transfer(Origin::signed(1), 2.into(), 69), "cannot transfer illiquid funds");
	});
}

#[test]
fn deducting_balance_when_bonded_should_not_work() {
	with_externalities(&mut new_test_ext(0, 1, 3, 1, false, 0), || {
		Balances::set_free_balance(&1, 111);
		<Bondage<Test>>::insert(1, 2);
		System::set_block_number(1);
		assert_eq!(Staking::unlock_block(&1), LockStatus::LockedUntil(2));
		assert_noop!(Balances::reserve(&1, 69), "cannot transfer illiquid funds");
	});
}
