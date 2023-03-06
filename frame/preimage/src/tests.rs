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

//! # Scheduler tests.

#![cfg(test)]

use super::*;
use crate::mock::*;

use frame_support::{
	assert_err, assert_noop, assert_ok, assert_storage_noop, bounded_vec,
	traits::{Bounded, BoundedInline, Hash as PreimageHash},
	StorageNoopGuard,
};
use pallet_balances::Error as BalancesError;
use sp_core::{blake2_256, H256};

/// Returns one `Inline`, `Lookup` and `Legacy` item each with different data and hash.
pub fn make_bounded_values() -> (Bounded<Vec<u8>>, Bounded<Vec<u8>>, Bounded<Vec<u8>>) {
	let data: BoundedInline = bounded_vec![1];
	let inline = Bounded::<Vec<u8>>::Inline(data);

	let data = vec![1, 2];
	let hash: H256 = blake2_256(&data[..]).into();
	let len = data.len() as u32;
	let lookup = Bounded::<Vec<u8>>::unrequested(hash, len);

	let data = vec![1, 2, 3];
	let hash: H256 = blake2_256(&data[..]).into();
	let legacy = Bounded::<Vec<u8>>::Legacy { hash, dummy: Default::default() };

	(inline, lookup, legacy)
}

#[test]
fn user_note_preimage_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(2), vec![1]));
		assert_eq!(Balances::reserved_balance(2), 3);
		assert_eq!(Balances::free_balance(2), 97);

		let h = hashed([1]);
		assert!(Preimage::have_preimage(&h));
		assert_eq!(Preimage::get_preimage(&h), Some(vec![1]));

		assert_noop!(
			Preimage::note_preimage(RuntimeOrigin::signed(2), vec![1]),
			Error::<Test>::AlreadyNoted
		);
		assert_noop!(
			Preimage::note_preimage(RuntimeOrigin::signed(0), vec![2]),
			BalancesError::<Test>::InsufficientBalance
		);
	});
}

#[test]
fn manager_note_preimage_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(1), vec![1]));
		assert_eq!(Balances::reserved_balance(1), 0);
		assert_eq!(Balances::free_balance(1), 100);

		let h = hashed([1]);
		assert!(Preimage::have_preimage(&h));
		assert_eq!(Preimage::get_preimage(&h), Some(vec![1]));

		assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(1), vec![1]));
	});
}

#[test]
fn user_unnote_preimage_works() {
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(2), vec![1]));
		assert_noop!(
			Preimage::unnote_preimage(RuntimeOrigin::signed(3), hashed([1])),
			Error::<Test>::NotAuthorized
		);
		assert_noop!(
			Preimage::unnote_preimage(RuntimeOrigin::signed(2), hashed([2])),
			Error::<Test>::NotNoted
		);

		assert_ok!(Preimage::unnote_preimage(RuntimeOrigin::signed(2), hashed([1])));
		assert_noop!(
			Preimage::unnote_preimage(RuntimeOrigin::signed(2), hashed([1])),
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
		assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(1), vec![1]));
		assert_ok!(Preimage::unnote_preimage(RuntimeOrigin::signed(1), hashed([1])));
		assert_noop!(
			Preimage::unnote_preimage(RuntimeOrigin::signed(1), hashed([1])),
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
		assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(2), vec![1]));
		assert_noop!(
			Preimage::unnote_preimage(RuntimeOrigin::signed(3), hashed([1])),
			Error::<Test>::NotAuthorized
		);
		assert_noop!(
			Preimage::unnote_preimage(RuntimeOrigin::signed(2), hashed([2])),
			Error::<Test>::NotNoted
		);

		assert_ok!(Preimage::unnote_preimage(RuntimeOrigin::signed(1), hashed([1])));

		let h = hashed([1]);
		assert!(!Preimage::have_preimage(&h));
		assert_eq!(Preimage::get_preimage(&h), None);
	});
}

#[test]
fn requested_then_noted_preimage_cannot_be_unnoted() {
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(1), vec![1]));
		assert_ok!(Preimage::request_preimage(RuntimeOrigin::signed(1), hashed([1])));
		assert_ok!(Preimage::unnote_preimage(RuntimeOrigin::signed(1), hashed([1])));
		// it's still here.

		let h = hashed([1]);
		assert!(Preimage::have_preimage(&h));
		assert_eq!(Preimage::get_preimage(&h), Some(vec![1]));

		// now it's gone
		assert_ok!(Preimage::unrequest_preimage(RuntimeOrigin::signed(1), hashed([1])));
		assert!(!Preimage::have_preimage(&hashed([1])));
	});
}

#[test]
fn request_note_order_makes_no_difference() {
	let one_way = new_test_ext().execute_with(|| {
		assert_ok!(Preimage::request_preimage(RuntimeOrigin::signed(1), hashed([1])));
		assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(2), vec![1]));
		(
			StatusFor::<Test>::iter().collect::<Vec<_>>(),
			PreimageFor::<Test>::iter().collect::<Vec<_>>(),
		)
	});
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(2), vec![1]));
		assert_ok!(Preimage::request_preimage(RuntimeOrigin::signed(1), hashed([1])));
		assert_ok!(Preimage::unnote_preimage(RuntimeOrigin::signed(2), hashed([1])));
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
		assert_ok!(Preimage::request_preimage(RuntimeOrigin::signed(1), hashed([1])));
		assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(2), vec![1]));
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
		assert_ok!(Preimage::request_preimage(RuntimeOrigin::signed(1), hashed([1])));
		assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(2), vec![1]));
		(
			StatusFor::<Test>::iter().collect::<Vec<_>>(),
			PreimageFor::<Test>::iter().collect::<Vec<_>>(),
		)
	});
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(2), vec![1]));
		assert_ok!(Preimage::request_preimage(RuntimeOrigin::signed(1), hashed([1])));
		assert_ok!(Preimage::unnote_preimage(RuntimeOrigin::signed(2), hashed([1])));
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
		assert_ok!(Preimage::request_preimage(RuntimeOrigin::signed(1), hashed([1])));
		assert_ok!(Preimage::request_preimage(RuntimeOrigin::signed(1), hashed([1])));
		assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(2), vec![1]));
		assert_noop!(
			Preimage::unrequest_preimage(RuntimeOrigin::signed(1), hashed([2])),
			Error::<Test>::NotRequested
		);

		assert_ok!(Preimage::unrequest_preimage(RuntimeOrigin::signed(1), hashed([1])));
		assert!(Preimage::have_preimage(&hashed([1])));

		assert_ok!(Preimage::unrequest_preimage(RuntimeOrigin::signed(1), hashed([1])));
		assert_noop!(
			Preimage::unrequest_preimage(RuntimeOrigin::signed(1), hashed([1])),
			Error::<Test>::NotRequested
		);
	});
}

#[test]
fn user_noted_then_requested_preimage_is_refunded_once_only() {
	new_test_ext().execute_with(|| {
		assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(2), vec![1; 3]));
		assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(2), vec![1]));
		assert_ok!(Preimage::request_preimage(RuntimeOrigin::signed(1), hashed([1])));
		assert_ok!(Preimage::unrequest_preimage(RuntimeOrigin::signed(1), hashed([1])));
		assert_ok!(Preimage::unnote_preimage(RuntimeOrigin::signed(2), hashed([1])));
		// Still have reserve from `vec[1; 3]`.
		assert_eq!(Balances::reserved_balance(2), 5);
		assert_eq!(Balances::free_balance(2), 95);
	});
}

#[test]
fn noted_preimage_use_correct_map() {
	new_test_ext().execute_with(|| {
		// Add one preimage per bucket...
		for i in 0..7 {
			assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(1), vec![0; 128 << (i * 2)]));
		}
		assert_ok!(Preimage::note_preimage(RuntimeOrigin::signed(1), vec![0; MAX_SIZE as usize]));
		assert_eq!(PreimageFor::<Test>::iter().count(), 8);

		// All are present
		assert_eq!(StatusFor::<Test>::iter().count(), 8);

		// Now start removing them again...
		for i in 0..7 {
			assert_ok!(Preimage::unnote_preimage(
				RuntimeOrigin::signed(1),
				hashed(vec![0; 128 << (i * 2)])
			));
		}
		assert_eq!(PreimageFor::<Test>::iter().count(), 1);
		assert_ok!(Preimage::unnote_preimage(
			RuntimeOrigin::signed(1),
			hashed(vec![0; MAX_SIZE as usize])
		));
		assert_eq!(PreimageFor::<Test>::iter().count(), 0);

		// All are gone
		assert_eq!(StatusFor::<Test>::iter().count(), 0);
	});
}

/// The `StorePreimage` and `QueryPreimage` traits work together.
#[test]
fn query_and_store_preimage_workflow() {
	new_test_ext().execute_with(|| {
		let _guard = StorageNoopGuard::default();
		let data: Vec<u8> = vec![1; 512];
		let encoded = data.encode();

		// Bound an unbound value.
		let bound = Preimage::bound(data.clone()).unwrap();
		let (len, hash) = (bound.len().unwrap(), bound.hash());

		assert_eq!(hash, blake2_256(&encoded).into());
		assert_eq!(bound.len(), Some(len));
		assert!(bound.lookup_needed(), "Should not be Inlined");
		assert_eq!(bound.lookup_len(), Some(len));

		// The value is requested and available.
		assert!(Preimage::is_requested(&hash));
		assert!(<Preimage as QueryPreimage>::have(&bound));
		assert_eq!(Preimage::len(&hash), Some(len));

		// It can be fetched with length.
		assert_eq!(Preimage::fetch(&hash, Some(len)).unwrap(), encoded);
		// ... and without length.
		assert_eq!(Preimage::fetch(&hash, None).unwrap(), encoded);
		// ... but not with wrong length.
		assert_err!(Preimage::fetch(&hash, Some(0)), DispatchError::Unavailable);

		// It can be peeked and decoded correctly.
		assert_eq!(Preimage::peek::<Vec<u8>>(&bound).unwrap(), (data.clone(), Some(len)));
		// Request it two more times.
		assert_eq!(Preimage::pick::<Vec<u8>>(hash, len), bound);
		Preimage::request(&hash);
		// It is requested thrice.
		assert!(matches!(
			StatusFor::<Test>::get(&hash).unwrap(),
			RequestStatus::Requested { count: 3, .. }
		));

		// It can be realized and decoded correctly.
		assert_eq!(Preimage::realize::<Vec<u8>>(&bound).unwrap(), (data.clone(), Some(len)));
		assert!(matches!(
			StatusFor::<Test>::get(&hash).unwrap(),
			RequestStatus::Requested { count: 2, .. }
		));
		// Dropping should unrequest.
		Preimage::drop(&bound);
		assert!(matches!(
			StatusFor::<Test>::get(&hash).unwrap(),
			RequestStatus::Requested { count: 1, .. }
		));

		// Is still available.
		assert!(<Preimage as QueryPreimage>::have(&bound));
		// Manually unnote it.
		Preimage::unnote(&hash);
		// Is not available anymore.
		assert!(!<Preimage as QueryPreimage>::have(&bound));
		assert_err!(Preimage::fetch(&hash, Some(len)), DispatchError::Unavailable);
		// And not requested since the traits assume permissioned origin.
		assert!(!Preimage::is_requested(&hash));

		// No storage changes remain. Checked by `StorageNoopGuard`.
	});
}

/// The request function behaves as expected.
#[test]
fn query_preimage_request_works() {
	new_test_ext().execute_with(|| {
		let _guard = StorageNoopGuard::default();
		let data: Vec<u8> = vec![1; 10];
		let hash: PreimageHash = blake2_256(&data[..]).into();

		// Request the preimage.
		<Preimage as QueryPreimage>::request(&hash);

		// The preimage is requested with unknown length and cannot be fetched.
		assert!(<Preimage as QueryPreimage>::is_requested(&hash));
		assert!(<Preimage as QueryPreimage>::len(&hash).is_none());
		assert_noop!(<Preimage as QueryPreimage>::fetch(&hash, None), DispatchError::Unavailable);

		// Request again.
		<Preimage as QueryPreimage>::request(&hash);
		// The preimage is still requested.
		assert!(<Preimage as QueryPreimage>::is_requested(&hash));
		assert!(<Preimage as QueryPreimage>::len(&hash).is_none());
		assert_noop!(<Preimage as QueryPreimage>::fetch(&hash, None), DispatchError::Unavailable);
		// But there is only one entry in the map.
		assert_eq!(StatusFor::<Test>::iter().count(), 1);

		// Un-request the preimage.
		<Preimage as QueryPreimage>::unrequest(&hash);
		// It is still requested.
		assert!(<Preimage as QueryPreimage>::is_requested(&hash));
		// Un-request twice.
		<Preimage as QueryPreimage>::unrequest(&hash);
		// It is not requested anymore.
		assert!(!<Preimage as QueryPreimage>::is_requested(&hash));
		// And there is no entry in the map.
		assert_eq!(StatusFor::<Test>::iter().count(), 0);
	});
}

/// The `QueryPreimage` functions can be used together with `Bounded` values.
#[test]
fn query_preimage_hold_and_drop_work() {
	new_test_ext().execute_with(|| {
		let _guard = StorageNoopGuard::default();
		let (inline, lookup, legacy) = make_bounded_values();

		// `hold` does nothing for `Inline` values.
		assert_storage_noop!(<Preimage as QueryPreimage>::hold(&inline));
		// `hold` requests `Lookup` values.
		<Preimage as QueryPreimage>::hold(&lookup);
		assert!(<Preimage as QueryPreimage>::is_requested(&lookup.hash()));
		// `hold` requests `Legacy` values.
		<Preimage as QueryPreimage>::hold(&legacy);
		assert!(<Preimage as QueryPreimage>::is_requested(&legacy.hash()));

		// There are two values requested in total.
		assert_eq!(StatusFor::<Test>::iter().count(), 2);

		// Cleanup by dropping both.
		<Preimage as QueryPreimage>::drop(&lookup);
		assert!(!<Preimage as QueryPreimage>::is_requested(&lookup.hash()));
		<Preimage as QueryPreimage>::drop(&legacy);
		assert!(!<Preimage as QueryPreimage>::is_requested(&legacy.hash()));

		// There are no values requested anymore.
		assert_eq!(StatusFor::<Test>::iter().count(), 0);
	});
}

/// The `StorePreimage` trait works as expected.
#[test]
fn store_preimage_basic_works() {
	new_test_ext().execute_with(|| {
		let _guard = StorageNoopGuard::default();
		let data: Vec<u8> = vec![1; 512]; // Too large to inline.
		let encoded = Cow::from(data.encode());

		// Bound the data.
		let bound = <Preimage as StorePreimage>::bound(data.clone()).unwrap();
		// The preimage can be peeked.
		assert_ok!(<Preimage as QueryPreimage>::peek(&bound));
		// Un-note the preimage.
		<Preimage as StorePreimage>::unnote(&bound.hash());
		// The preimage cannot be peeked anymore.
		assert_err!(<Preimage as QueryPreimage>::peek(&bound), DispatchError::Unavailable);
		// Noting the wrong pre-image does not make it peek-able.
		assert_ok!(<Preimage as StorePreimage>::note(Cow::Borrowed(&data)));
		assert_err!(<Preimage as QueryPreimage>::peek(&bound), DispatchError::Unavailable);

		// Manually note the preimage makes it peek-able again.
		assert_ok!(<Preimage as StorePreimage>::note(encoded.clone()));
		// Noting again works.
		assert_ok!(<Preimage as StorePreimage>::note(encoded));
		assert_ok!(<Preimage as QueryPreimage>::peek(&bound));

		// Cleanup.
		<Preimage as StorePreimage>::unnote(&bound.hash());
		let data_hash = blake2_256(&data);
		<Preimage as StorePreimage>::unnote(&data_hash.into());

		// No storage changes remain. Checked by `StorageNoopGuard`.
	});
}

#[test]
fn store_preimage_note_too_large_errors() {
	new_test_ext().execute_with(|| {
		// Works with `MAX_LENGTH`.
		let len = <Preimage as StorePreimage>::MAX_LENGTH;
		let data = vec![0u8; len];
		assert_ok!(<Preimage as StorePreimage>::note(data.into()));

		// Errors with `MAX_LENGTH+1`.
		let data = vec![0u8; len + 1];
		assert_err!(<Preimage as StorePreimage>::note(data.into()), DispatchError::Exhausted);
	});
}

#[test]
fn store_preimage_bound_too_large_errors() {
	new_test_ext().execute_with(|| {
		// Using `MAX_LENGTH` number of bytes in a vector does not work
		// since SCALE prepends the length.
		let len = <Preimage as StorePreimage>::MAX_LENGTH;
		let data: Vec<u8> = vec![0; len];
		assert_err!(<Preimage as StorePreimage>::bound(data.clone()), DispatchError::Exhausted);

		// Works with `MAX_LENGTH-4`.
		let data: Vec<u8> = vec![0; len - 4];
		assert_ok!(<Preimage as StorePreimage>::bound(data.clone()));
	});
}
