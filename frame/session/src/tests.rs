// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

// Tests for the Session Pallet

use super::*;
use crate::mock::{
	authorities, before_session_end_called, force_new_session, new_test_ext,
	reset_before_session_end_called, session_changed, set_next_validators, set_session_length,
	Origin, PreUpgradeMockSessionKeys, Session, System, Test, TestValidatorIdOf, SESSION_CHANGED,
	TEST_SESSION_CHANGED,
};

use codec::Decode;
use sp_core::crypto::key_types::DUMMY;
use sp_runtime::testing::UintAuthorityId;

use frame_support::{
	assert_noop, assert_ok,
	traits::{ConstU64, OnInitialize},
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

		assert!(System::is_provider_required(&1));
		assert_ok!(Session::purge_keys(Origin::signed(1)));
		assert!(!System::is_provider_required(&1));

		assert_eq!(Session::load_keys(&1), None);
		assert_eq!(Session::key_owner(id, UintAuthorityId(1).get_raw(id)), None);
	})
}

#[test]
fn purge_keys_works_for_stash_id() {
	let mut ext = new_test_ext();
	ext.execute_with(|| {
		assert_eq!(Session::validators(), vec![1, 2, 3]);
		TestValidatorIdOf::set(vec![(10, 1), (20, 2), (3, 3)].into_iter().collect());
		assert_eq!(Session::load_keys(&1), Some(UintAuthorityId(1).into()));
		assert_eq!(Session::load_keys(&2), Some(UintAuthorityId(2).into()));

		let id = DUMMY;
		assert_eq!(Session::key_owner(id, UintAuthorityId(1).get_raw(id)), Some(1));

		assert_ok!(Session::purge_keys(Origin::signed(10)));
		assert_ok!(Session::purge_keys(Origin::signed(2)));

		assert_eq!(Session::load_keys(&10), None);
		assert_eq!(Session::load_keys(&20), None);
		assert_eq!(Session::key_owner(id, UintAuthorityId(10).get_raw(id)), None);
		assert_eq!(Session::key_owner(id, UintAuthorityId(20).get_raw(id)), None);
	})
}

#[test]
fn authorities_should_track_validators() {
	reset_before_session_end_called();

	new_test_ext().execute_with(|| {
		TestValidatorIdOf::set(vec![(1, 1), (2, 2), (3, 3), (4, 4)].into_iter().collect());

		set_next_validators(vec![1, 2]);
		force_new_session();
		initialize_block(1);
		assert_eq!(
			Session::queued_keys(),
			vec![(1, UintAuthorityId(1).into()), (2, UintAuthorityId(2).into()),]
		);
		assert_eq!(Session::validators(), vec![1, 2, 3]);
		assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);
		assert!(before_session_end_called());
		reset_before_session_end_called();

		force_new_session();
		initialize_block(2);
		assert_eq!(
			Session::queued_keys(),
			vec![(1, UintAuthorityId(1).into()), (2, UintAuthorityId(2).into()),]
		);
		assert_eq!(Session::validators(), vec![1, 2]);
		assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2)]);
		assert!(before_session_end_called());
		reset_before_session_end_called();

		set_next_validators(vec![1, 2, 4]);
		assert_ok!(Session::set_keys(Origin::signed(4), UintAuthorityId(4).into(), vec![]));
		force_new_session();
		initialize_block(3);
		assert_eq!(
			Session::queued_keys(),
			vec![
				(1, UintAuthorityId(1).into()),
				(2, UintAuthorityId(2).into()),
				(4, UintAuthorityId(4).into()),
			]
		);
		assert_eq!(Session::validators(), vec![1, 2]);
		assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2)]);
		assert!(before_session_end_called());

		force_new_session();
		initialize_block(4);
		assert_eq!(
			Session::queued_keys(),
			vec![
				(1, UintAuthorityId(1).into()),
				(2, UintAuthorityId(2).into()),
				(4, UintAuthorityId(4).into()),
			]
		);
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
		TestValidatorIdOf::set(vec![(1, 1), (2, 2), (3, 3), (4, 4)].into_iter().collect());

		System::set_block_number(1);
		Session::on_initialize(1);
		assert_noop!(
			Session::set_keys(Origin::signed(4), UintAuthorityId(1).into(), vec![]),
			Error::<Test>::DuplicatedKey,
		);
		assert_ok!(Session::set_keys(Origin::signed(1), UintAuthorityId(10).into(), vec![]));

		// is fine now that 1 has migrated off.
		assert_ok!(Session::set_keys(Origin::signed(4), UintAuthorityId(1).into(), vec![]));
	});
}

#[test]
fn session_changed_flag_works() {
	reset_before_session_end_called();

	new_test_ext().execute_with(|| {
		TestValidatorIdOf::set(vec![(1, 1), (2, 2), (3, 3), (69, 69)].into_iter().collect());
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
	type P = PeriodicSessions<ConstU64<10>, ConstU64<3>>;

	// make sure that offset phase behaves correctly
	for i in 0u64..3 {
		assert!(!P::should_end_session(i));
		assert_eq!(P::estimate_next_session_rotation(i).0.unwrap(), 3);

		// the last block of the session (i.e. the one before session rotation)
		// should have progress 100%.
		if P::estimate_next_session_rotation(i).0.unwrap() - 1 == i {
			assert_eq!(
				P::estimate_current_session_progress(i).0.unwrap(),
				Permill::from_percent(100)
			);
		} else {
			assert!(
				P::estimate_current_session_progress(i).0.unwrap() < Permill::from_percent(100)
			);
		}
	}

	// we end the session at block #3 and we consider this block the first one
	// from the next session. since we're past the offset phase it represents
	// 1/10 of progress.
	assert!(P::should_end_session(3u64));
	assert_eq!(P::estimate_next_session_rotation(3u64).0.unwrap(), 3);
	assert_eq!(P::estimate_current_session_progress(3u64).0.unwrap(), Permill::from_percent(10));

	for i in (1u64..10).map(|i| 3 + i) {
		assert!(!P::should_end_session(i));
		assert_eq!(P::estimate_next_session_rotation(i).0.unwrap(), 13);

		// as with the offset phase the last block of the session must have 100%
		// progress.
		if P::estimate_next_session_rotation(i).0.unwrap() - 1 == i {
			assert_eq!(
				P::estimate_current_session_progress(i).0.unwrap(),
				Permill::from_percent(100)
			);
		} else {
			assert!(
				P::estimate_current_session_progress(i).0.unwrap() < Permill::from_percent(100)
			);
		}
	}

	// the new session starts and we proceed in 1/10 increments.
	assert!(P::should_end_session(13u64));
	assert_eq!(P::estimate_next_session_rotation(13u64).0.unwrap(), 23);
	assert_eq!(P::estimate_current_session_progress(13u64).0.unwrap(), Permill::from_percent(10));

	assert!(!P::should_end_session(14u64));
	assert_eq!(P::estimate_next_session_rotation(14u64).0.unwrap(), 23);
	assert_eq!(P::estimate_current_session_progress(14u64).0.unwrap(), Permill::from_percent(20));
}

#[test]
fn session_keys_generate_output_works_as_set_keys_input() {
	new_test_ext().execute_with(|| {
		let new_keys = mock::MockSessionKeys::generate(None);
		assert_ok!(Session::set_keys(
			Origin::signed(2),
			<mock::Test as Config>::Keys::decode(&mut &new_keys[..]).expect("Decode keys"),
			vec![],
		));
	});
}

#[test]
fn disable_index_returns_false_if_already_disabled() {
	new_test_ext().execute_with(|| {
		set_next_validators(vec![1, 2, 3, 4, 5, 6, 7]);
		force_new_session();
		initialize_block(1);
		// apply the new validator set
		force_new_session();
		initialize_block(2);

		assert_eq!(Session::disable_index(0), true);
		assert_eq!(Session::disable_index(0), false);
		assert_eq!(Session::disable_index(1), true);
	});
}

#[test]
fn upgrade_keys() {
	use frame_support::storage;
	use sp_core::crypto::key_types::DUMMY;

	// This test assumes certain mocks.
	assert_eq!(mock::NEXT_VALIDATORS.with(|l| l.borrow().clone()), vec![1, 2, 3]);
	assert_eq!(mock::VALIDATORS.with(|l| l.borrow().clone()), vec![1, 2, 3]);

	new_test_ext().execute_with(|| {
		let pre_one = PreUpgradeMockSessionKeys { a: [1u8; 32], b: [1u8; 64] };

		let pre_two = PreUpgradeMockSessionKeys { a: [2u8; 32], b: [2u8; 64] };

		let pre_three = PreUpgradeMockSessionKeys { a: [3u8; 32], b: [3u8; 64] };

		let val_keys = vec![(1u64, pre_one), (2u64, pre_two), (3u64, pre_three)];

		// Set `QueuedKeys`.
		{
			let storage_key = <super::QueuedKeys<Test>>::hashed_key();
			assert!(storage::unhashed::exists(&storage_key));
			storage::unhashed::put(&storage_key, &val_keys);
		}

		// Set `NextKeys`.
		{
			for &(i, ref keys) in val_keys.iter() {
				let storage_key = <super::NextKeys<Test>>::hashed_key_for(i);
				assert!(storage::unhashed::exists(&storage_key));
				storage::unhashed::put(&storage_key, keys);
			}
		}

		// Set `KeyOwner`.
		{
			for &(i, ref keys) in val_keys.iter() {
				// clear key owner for `UintAuthorityId` keys set in genesis.
				let presumed = UintAuthorityId(i);
				let raw_prev = presumed.as_ref();

				assert_eq!(Session::key_owner(DUMMY, raw_prev), Some(i));
				Session::clear_key_owner(DUMMY, raw_prev);

				Session::put_key_owner(mock::KEY_ID_A, keys.get_raw(mock::KEY_ID_A), &i);
				Session::put_key_owner(mock::KEY_ID_B, keys.get_raw(mock::KEY_ID_B), &i);
			}
		}

		// Do the upgrade and check sanity.
		let mock_keys_for = |val| mock::MockSessionKeys { dummy: UintAuthorityId(val) };
		Session::upgrade_keys::<PreUpgradeMockSessionKeys, _>(|val, _old_keys| mock_keys_for(val));

		// Check key ownership.
		for (i, ref keys) in val_keys.iter() {
			assert!(Session::key_owner(mock::KEY_ID_A, keys.get_raw(mock::KEY_ID_A)).is_none());
			assert!(Session::key_owner(mock::KEY_ID_B, keys.get_raw(mock::KEY_ID_B)).is_none());

			let migrated_key = UintAuthorityId(*i);
			assert_eq!(Session::key_owner(DUMMY, migrated_key.as_ref()), Some(*i));
		}

		// Check queued keys.
		assert_eq!(
			Session::queued_keys(),
			vec![(1, mock_keys_for(1)), (2, mock_keys_for(2)), (3, mock_keys_for(3)),],
		);

		for i in 1u64..4 {
			assert_eq!(<super::NextKeys<Test>>::get(&i), Some(mock_keys_for(i)));
		}
	})
}

#[cfg(feature = "historical")]
#[test]
fn test_migration_v1() {
	use crate::{
		historical::{HistoricalSessions, StoredRange},
		mock::Historical,
	};
	use frame_support::traits::PalletInfoAccess;

	new_test_ext().execute_with(|| {
		assert!(<HistoricalSessions<Test>>::iter_values().count() > 0);
		assert!(<StoredRange<Test>>::exists());

		let old_pallet = "Session";
		let new_pallet = <Historical as PalletInfoAccess>::name();
		frame_support::storage::migration::move_pallet(
			new_pallet.as_bytes(),
			old_pallet.as_bytes(),
		);
		StorageVersion::new(0).put::<Historical>();

		crate::migrations::v1::pre_migrate::<Test, Historical>();
		crate::migrations::v1::migrate::<Test, Historical>();
		crate::migrations::v1::post_migrate::<Test, Historical>();
	});
}
