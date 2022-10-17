// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! # Scheduler tests.

use super::*;
use crate::mock::*;

use frame_support::{assert_noop, assert_ok};
use pallet_balances::Error as BalancesError;

#[test]
fn user_note_preimage_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::note_preimage(Origin::signed(2), vec![1]));
		assert_eq!(Balances::reserved_balance(2), 3);
		assert_eq!(Balances::free_balance(2), 97);

		let h = hashed([1]);
		assert!(Preimage::have_preimage(&h));
		assert_eq!(Preimage::get_preimage(&h), Some(vec![1]));

		assert_noop!(
			Preimage::note_preimage(Origin::signed(2), vec![1]),
			Error::<Test>::AlreadyNoted
		);
		assert_noop!(
			Preimage::note_preimage(Origin::signed(0), vec![2]),
			BalancesError::<Test>::InsufficientBalance
		);
	});
}

#[test]
fn manager_note_preimage_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::note_preimage(Origin::signed(1), vec![1]));
		assert_eq!(Balances::reserved_balance(1), 0);
		assert_eq!(Balances::free_balance(1), 100);

		let h = hashed([1]);
		assert!(Preimage::have_preimage(&h));
		assert_eq!(Preimage::get_preimage(&h), Some(vec![1]));

		assert_noop!(
			Preimage::note_preimage(Origin::signed(1), vec![1]),
			Error::<Test>::AlreadyNoted
		);
	});
}

#[test]
fn user_unnote_preimage_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::note_preimage(Origin::signed(2), vec![1]));
		assert_noop!(
			Preimage::unnote_preimage(Origin::signed(3), hashed([1])),
			Error::<Test>::NotAuthorized
		);
		assert_noop!(
			Preimage::unnote_preimage(Origin::signed(2), hashed([2])),
			Error::<Test>::NotNoted
		);

		assert_ok!(Preimage::unnote_preimage(Origin::signed(2), hashed([1])));
		assert_noop!(
			Preimage::unnote_preimage(Origin::signed(2), hashed([1])),
			Error::<Test>::NotNoted
		);

		let h = hashed([1]);
		assert!(!Preimage::have_preimage(&h));
		assert_eq!(Preimage::get_preimage(&h), None);
	});
}

#[test]
fn manager_unnote_preimage_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::note_preimage(Origin::signed(1), vec![1]));
		assert_ok!(Preimage::unnote_preimage(Origin::signed(1), hashed([1])));
		assert_noop!(
			Preimage::unnote_preimage(Origin::signed(1), hashed([1])),
			Error::<Test>::NotNoted
		);

		let h = hashed([1]);
		assert!(!Preimage::have_preimage(&h));
		assert_eq!(Preimage::get_preimage(&h), None);
	});
}

#[test]
fn manager_unnote_user_preimage_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::note_preimage(Origin::signed(2), vec![1]));
		assert_noop!(
			Preimage::unnote_preimage(Origin::signed(3), hashed([1])),
			Error::<Test>::NotAuthorized
		);
		assert_noop!(
			Preimage::unnote_preimage(Origin::signed(2), hashed([2])),
			Error::<Test>::NotNoted
		);

		assert_ok!(Preimage::unnote_preimage(Origin::signed(1), hashed([1])));

		let h = hashed([1]);
		assert!(!Preimage::have_preimage(&h));
		assert_eq!(Preimage::get_preimage(&h), None);
	});
}

#[test]
fn requested_then_noted_preimage_cannot_be_unnoted() {
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::note_preimage(Origin::signed(1), vec![1]));
		assert_ok!(Preimage::request_preimage(Origin::signed(1), hashed([1])));
		assert_noop!(
			Preimage::unnote_preimage(Origin::signed(1), hashed([1])),
			Error::<Test>::Requested
		);

		let h = hashed([1]);
		assert!(Preimage::have_preimage(&h));
		assert_eq!(Preimage::get_preimage(&h), Some(vec![1]));
	});
}

#[test]
fn request_note_order_makes_no_difference() {
	let one_way = new_test_ext().execute_with(|| {
		assert_ok!(Preimage::request_preimage(Origin::signed(1), hashed([1])));
		assert_ok!(Preimage::note_preimage(Origin::signed(1), vec![1]));
		(
			StatusFor::<Test>::iter().collect::<Vec<_>>(),
			PreimageFor::<Test>::iter().collect::<Vec<_>>(),
		)
	});
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::note_preimage(Origin::signed(1), vec![1]));
		assert_ok!(Preimage::request_preimage(Origin::signed(1), hashed([1])));
		let other_way = (
			StatusFor::<Test>::iter().collect::<Vec<_>>(),
			PreimageFor::<Test>::iter().collect::<Vec<_>>(),
		);
		assert_eq!(one_way, other_way);
	});
}

#[test]
fn requested_then_user_noted_preimage_is_free() {
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::request_preimage(Origin::signed(1), hashed([1])));
		assert_ok!(Preimage::note_preimage(Origin::signed(2), vec![1]));
		assert_eq!(Balances::reserved_balance(2), 0);
		assert_eq!(Balances::free_balance(2), 100);

		let h = hashed([1]);
		assert!(Preimage::have_preimage(&h));
		assert_eq!(Preimage::get_preimage(&h), Some(vec![1]));
	});
}

#[test]
fn request_user_note_order_makes_no_difference() {
	let one_way = new_test_ext().execute_with(|| {
		assert_ok!(Preimage::request_preimage(Origin::signed(1), hashed([1])));
		assert_ok!(Preimage::note_preimage(Origin::signed(2), vec![1]));
		(
			StatusFor::<Test>::iter().collect::<Vec<_>>(),
			PreimageFor::<Test>::iter().collect::<Vec<_>>(),
		)
	});
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::note_preimage(Origin::signed(2), vec![1]));
		assert_ok!(Preimage::request_preimage(Origin::signed(1), hashed([1])));
		let other_way = (
			StatusFor::<Test>::iter().collect::<Vec<_>>(),
			PreimageFor::<Test>::iter().collect::<Vec<_>>(),
		);
		assert_eq!(one_way, other_way);
	});
}

#[test]
fn unrequest_preimage_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::request_preimage(Origin::signed(1), hashed([1])));
		assert_ok!(Preimage::request_preimage(Origin::signed(1), hashed([1])));
		assert_ok!(Preimage::note_preimage(Origin::signed(2), vec![1]));
		assert_noop!(
			Preimage::unrequest_preimage(Origin::signed(1), hashed([2])),
			Error::<Test>::NotRequested
		);

		assert_ok!(Preimage::unrequest_preimage(Origin::signed(1), hashed([1])));
		assert!(Preimage::have_preimage(&hashed([1])));

		assert_ok!(Preimage::unrequest_preimage(Origin::signed(1), hashed([1])));
		assert_noop!(
			Preimage::unrequest_preimage(Origin::signed(1), hashed([1])),
			Error::<Test>::NotRequested
		);
	});
}

#[test]
fn user_noted_then_requested_preimage_is_refunded_once_only() {
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::note_preimage(Origin::signed(2), vec![1; 3]));
		assert_ok!(Preimage::note_preimage(Origin::signed(2), vec![1]));
		assert_ok!(Preimage::request_preimage(Origin::signed(1), hashed([1])));
		assert_ok!(Preimage::unrequest_preimage(Origin::signed(1), hashed([1])));
		// Still have reserve from `vec[1; 3]`.
		assert_eq!(Balances::reserved_balance(2), 5);
		assert_eq!(Balances::free_balance(2), 95);
	});
}
