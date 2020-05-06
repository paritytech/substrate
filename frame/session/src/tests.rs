// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

// Tests for the Session Pallet

use super::*;
use frame_support::{traits::OnInitialize, assert_ok};
use sp_core::crypto::key_types::DUMMY;
use sp_runtime::testing::UintAuthorityId;
use mock::{
	SESSION_CHANGED, TEST_SESSION_CHANGED, authorities, force_new_session,
	set_next_validators, set_session_length, session_changed, Origin, System, Session,
	reset_before_session_end_called, before_session_end_called, new_test_ext,
};

fn initialize_block(block: u64) {
	SESSION_CHANGED.with(|l| *l.borrow_mut() = false);
	System::set_block_number(block);
	Session::on_initialize(block);
}

#[test]
fn simple_setup_should_work() {
	new_test_ext().execute_with(|| {
		assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);
		assert_eq!(Session::validators(), vec![1, 2, 3]);
	});
}

#[test]
fn put_get_keys() {
	new_test_ext().execute_with(|| {
		Session::put_keys(&10, &UintAuthorityId(10).into());
		assert_eq!(Session::load_keys(&10), Some(UintAuthorityId(10).into()));
	})
}

#[test]
fn keys_cleared_on_kill() {
	let mut ext = new_test_ext();
	ext.execute_with(|| {
		assert_eq!(Session::validators(), vec![1, 2, 3]);
		assert_eq!(Session::load_keys(&1), Some(UintAuthorityId(1).into()));

		let id = DUMMY;
		assert_eq!(Session::key_owner(id, UintAuthorityId(1).get_raw(id)), Some(1));

		assert!(!System::allow_death(&1));
		assert_ok!(Session::purge_keys(Origin::signed(1)));
		assert!(System::allow_death(&1));

		assert_eq!(Session::load_keys(&1), None);
		assert_eq!(Session::key_owner(id, UintAuthorityId(1).get_raw(id)), None);
	})
}

#[test]
fn authorities_should_track_validators() {
	reset_before_session_end_called();

	new_test_ext().execute_with(|| {
		set_next_validators(vec![1, 2]);
		force_new_session();
		initialize_block(1);
		assert_eq!(Session::queued_keys(), vec![
			(1, UintAuthorityId(1).into()),
			(2, UintAuthorityId(2).into()),
		]);
		assert_eq!(Session::validators(), vec![1, 2, 3]);
		assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);
		assert!(before_session_end_called());
		reset_before_session_end_called();

		force_new_session();
		initialize_block(2);
		assert_eq!(Session::queued_keys(), vec![
			(1, UintAuthorityId(1).into()),
			(2, UintAuthorityId(2).into()),
		]);
		assert_eq!(Session::validators(), vec![1, 2]);
		assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2)]);
		assert!(before_session_end_called());
		reset_before_session_end_called();

		set_next_validators(vec![1, 2, 4]);
		assert_ok!(Session::set_keys(Origin::signed(4), UintAuthorityId(4).into(), vec![]));
		force_new_session();
		initialize_block(3);
		assert_eq!(Session::queued_keys(), vec![
			(1, UintAuthorityId(1).into()),
			(2, UintAuthorityId(2).into()),
			(4, UintAuthorityId(4).into()),
		]);
		assert_eq!(Session::validators(), vec![1, 2]);
		assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2)]);
		assert!(before_session_end_called());

		force_new_session();
		initialize_block(4);
		assert_eq!(Session::queued_keys(), vec![
			(1, UintAuthorityId(1).into()),
			(2, UintAuthorityId(2).into()),
			(4, UintAuthorityId(4).into()),
		]);
		assert_eq!(Session::validators(), vec![1, 2, 4]);
		assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(4)]);
	});
}

#[test]
fn should_work_with_early_exit() {
	new_test_ext().execute_with(|| {
		set_session_length(10);

		initialize_block(1);
		assert_eq!(Session::current_index(), 0);

		initialize_block(2);
		assert_eq!(Session::current_index(), 0);

		force_new_session();
		initialize_block(3);
		assert_eq!(Session::current_index(), 1);

		initialize_block(9);
		assert_eq!(Session::current_index(), 1);

		initialize_block(10);
		assert_eq!(Session::current_index(), 2);
	});
}

#[test]
fn session_change_should_work() {
	new_test_ext().execute_with(|| {
		// Block 1: No change
		initialize_block(1);
		assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);

		// Block 2: Session rollover, but no change.
		initialize_block(2);
		assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);

		// Block 3: Set new key for validator 2; no visible change.
		initialize_block(3);
		assert_ok!(Session::set_keys(Origin::signed(2), UintAuthorityId(5).into(), vec![]));
		assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);

		// Block 4: Session rollover; no visible change.
		initialize_block(4);
		assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);

		// Block 5: No change.
		initialize_block(5);
		assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);

		// Block 6: Session rollover; authority 2 changes.
		initialize_block(6);
		assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(5), UintAuthorityId(3)]);
	});
}

#[test]
fn duplicates_are_not_allowed() {
	new_test_ext().execute_with(|| {
		System::set_block_number(1);
		Session::on_initialize(1);
		assert!(Session::set_keys(Origin::signed(4), UintAuthorityId(1).into(), vec![]).is_err());
		assert!(Session::set_keys(Origin::signed(1), UintAuthorityId(10).into(), vec![]).is_ok());

		// is fine now that 1 has migrated off.
		assert!(Session::set_keys(Origin::signed(4), UintAuthorityId(1).into(), vec![]).is_ok());
	});
}

#[test]
fn session_changed_flag_works() {
	reset_before_session_end_called();

	new_test_ext().execute_with(|| {
		TEST_SESSION_CHANGED.with(|l| *l.borrow_mut() = true);

		force_new_session();
		initialize_block(1);
		assert!(!session_changed());
		assert!(before_session_end_called());
		reset_before_session_end_called();

		force_new_session();
		initialize_block(2);
		assert!(!session_changed());
		assert!(before_session_end_called());
		reset_before_session_end_called();

		Session::disable_index(0);
		force_new_session();
		initialize_block(3);
		assert!(!session_changed());
		assert!(before_session_end_called());
		reset_before_session_end_called();

		force_new_session();
		initialize_block(4);
		assert!(session_changed());
		assert!(before_session_end_called());
		reset_before_session_end_called();

		force_new_session();
		initialize_block(5);
		assert!(!session_changed());
		assert!(before_session_end_called());
		reset_before_session_end_called();

		assert_ok!(Session::set_keys(Origin::signed(2), UintAuthorityId(5).into(), vec![]));
		force_new_session();
		initialize_block(6);
		assert!(!session_changed());
		assert!(before_session_end_called());
		reset_before_session_end_called();

		// changing the keys of a validator leads to change.
		assert_ok!(Session::set_keys(Origin::signed(69), UintAuthorityId(69).into(), vec![]));
		force_new_session();
		initialize_block(7);
		assert!(session_changed());
		assert!(before_session_end_called());
		reset_before_session_end_called();

		// while changing the keys of a non-validator does not.
		force_new_session();
		initialize_block(7);
		assert!(!session_changed());
		assert!(before_session_end_called());
		reset_before_session_end_called();
	});
}

#[test]
fn periodic_session_works() {
	struct Period;
	struct Offset;

	impl Get<u64> for Period {
		fn get() -> u64 { 10 }
	}

	impl Get<u64> for Offset {
		fn get() -> u64 { 3 }
	}


	type P = PeriodicSessions<Period, Offset>;

	for i in 0..3 {
		assert!(!P::should_end_session(i));
	}

	assert!(P::should_end_session(3));

	for i in (1..10).map(|i| 3 + i) {
		assert!(!P::should_end_session(i));
	}

	assert!(P::should_end_session(13));
}

#[test]
fn session_keys_generate_output_works_as_set_keys_input() {
	new_test_ext().execute_with(|| {
		let new_keys = mock::MockSessionKeys::generate(None);
		assert_ok!(
			Session::set_keys(
				Origin::signed(2),
				<mock::Test as Trait>::Keys::decode(&mut &new_keys[..]).expect("Decode keys"),
				vec![],
			)
		);
	});
}

#[test]
fn return_true_if_more_than_third_is_disabled() {
	new_test_ext().execute_with(|| {
		set_next_validators(vec![1, 2, 3, 4, 5, 6, 7]);
		force_new_session();
		initialize_block(1);
		// apply the new validator set
		force_new_session();
		initialize_block(2);

		assert_eq!(Session::disable_index(0), false);
		assert_eq!(Session::disable_index(1), false);
		assert_eq!(Session::disable_index(2), true);
		assert_eq!(Session::disable_index(3), true);
	});
}
