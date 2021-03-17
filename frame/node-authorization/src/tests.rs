// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Tests for node-authorization pallet.

use super::*;
use crate::mock::*;
use frame_support::{assert_ok, assert_noop};
use sp_runtime::traits::BadOrigin;

#[test]
fn add_well_known_node_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			NodeAuthorization::add_well_known_node(Origin::signed(2), test_node(15), 15),
			BadOrigin
		);
		assert_noop!(
			NodeAuthorization::add_well_known_node(Origin::signed(1), PeerId(vec![1, 2, 3]), 15),
			Error::<Test>::PeerIdTooLong
		);
		assert_noop!(
			NodeAuthorization::add_well_known_node(Origin::signed(1), test_node(20), 20),
			Error::<Test>::AlreadyJoined
		);

		assert_ok!(
			NodeAuthorization::add_well_known_node(Origin::signed(1), test_node(15), 15)
		);
		assert_eq!(
			WellKnownNodes::<Test>::get(),
			BTreeSet::from_iter(vec![test_node(10), test_node(15), test_node(20), test_node(30)])
		);
		assert_eq!(Owners::<Test>::get(test_node(10)), Some(10));
		assert_eq!(Owners::<Test>::get(test_node(20)), Some(20));
		assert_eq!(Owners::<Test>::get(test_node(30)), Some(30));
		assert_eq!(Owners::<Test>::get(test_node(15)), Some(15));

		assert_noop!(
			NodeAuthorization::add_well_known_node(Origin::signed(1), test_node(25), 25),
			Error::<Test>::TooManyNodes
		);
	});
}

#[test]
fn remove_well_known_node_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			NodeAuthorization::remove_well_known_node(Origin::signed(3), test_node(20)),
			BadOrigin
		);
		assert_noop!(
			NodeAuthorization::remove_well_known_node(Origin::signed(2), PeerId(vec![1, 2, 3])),
			Error::<Test>::PeerIdTooLong
		);
		assert_noop!(
			NodeAuthorization::remove_well_known_node(Origin::signed(2), test_node(40)),
			Error::<Test>::NotExist
		);

		AdditionalConnections::<Test>::insert(
			test_node(20),
			BTreeSet::from_iter(vec![test_node(40)])
		);
		assert!(AdditionalConnections::<Test>::contains_key(test_node(20)));

		assert_ok!(
			NodeAuthorization::remove_well_known_node(Origin::signed(2), test_node(20))
		);
		assert_eq!(
			WellKnownNodes::<Test>::get(),
			BTreeSet::from_iter(vec![test_node(10), test_node(30)])
		);
		assert!(!Owners::<Test>::contains_key(test_node(20)));
		assert!(!AdditionalConnections::<Test>::contains_key(test_node(20)));
	});
}

#[test]
fn swap_well_known_node_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			NodeAuthorization::swap_well_known_node(
				Origin::signed(4), test_node(20), test_node(5)
			),
			BadOrigin
		);
		assert_noop!(
			NodeAuthorization::swap_well_known_node(
				Origin::signed(3), PeerId(vec![1, 2, 3]), test_node(20)
			),
			Error::<Test>::PeerIdTooLong
		);
		assert_noop!(
			NodeAuthorization::swap_well_known_node(
				Origin::signed(3), test_node(20), PeerId(vec![1, 2, 3])
			),
			Error::<Test>::PeerIdTooLong
		);

		assert_ok!(
			NodeAuthorization::swap_well_known_node(
				Origin::signed(3), test_node(20), test_node(20)
			)
		);
		assert_eq!(
			WellKnownNodes::<Test>::get(),
			BTreeSet::from_iter(vec![test_node(10), test_node(20), test_node(30)])
		);

		assert_noop!(
			NodeAuthorization::swap_well_known_node(
				Origin::signed(3), test_node(15), test_node(5)
			),
			Error::<Test>::NotExist
		);
		assert_noop!(
			NodeAuthorization::swap_well_known_node(
				Origin::signed(3), test_node(20), test_node(30)
			),
			Error::<Test>::AlreadyJoined
		);

		AdditionalConnections::<Test>::insert(
			test_node(20),
			BTreeSet::from_iter(vec![test_node(15)])
		);
		assert_ok!(
			NodeAuthorization::swap_well_known_node(
				Origin::signed(3), test_node(20), test_node(5)
			)
		);
		assert_eq!(
			WellKnownNodes::<Test>::get(),
			BTreeSet::from_iter(vec![test_node(5), test_node(10), test_node(30)])
		);
		assert!(!Owners::<Test>::contains_key(test_node(20)));
		assert_eq!(Owners::<Test>::get(test_node(5)), Some(20));
		assert!(!AdditionalConnections::<Test>::contains_key(test_node(20)));
		assert_eq!(
			AdditionalConnections::<Test>::get(test_node(5)),
			BTreeSet::from_iter(vec![test_node(15)])
		);
	});
}

#[test]
fn reset_well_known_nodes_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			NodeAuthorization::reset_well_known_nodes(
				Origin::signed(3),
				vec![(test_node(15), 15), (test_node(5), 5), (test_node(20), 20)]
			),
			BadOrigin
		);
		assert_noop!(
			NodeAuthorization::reset_well_known_nodes(
				Origin::signed(4),
				vec![
					(test_node(15), 15),
					(test_node(5), 5),
					(test_node(20), 20),
					(test_node(25), 25),
				]
			),
			Error::<Test>::TooManyNodes
		);

		assert_ok!(
			NodeAuthorization::reset_well_known_nodes(
				Origin::signed(4),
				vec![(test_node(15), 15), (test_node(5), 5), (test_node(20), 20)]
			)
		);
		assert_eq!(
			WellKnownNodes::<Test>::get(),
			BTreeSet::from_iter(vec![test_node(5), test_node(15), test_node(20)])
		);
		assert_eq!(Owners::<Test>::get(test_node(5)), Some(5));
		assert_eq!(Owners::<Test>::get(test_node(15)), Some(15));
		assert_eq!(Owners::<Test>::get(test_node(20)), Some(20));
	});
}

#[test]
fn claim_node_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			NodeAuthorization::claim_node(Origin::signed(1), PeerId(vec![1, 2, 3])),
			Error::<Test>::PeerIdTooLong
		);
		assert_noop!(
			NodeAuthorization::claim_node(Origin::signed(1), test_node(20)),
			Error::<Test>::AlreadyClaimed
		);

		assert_ok!(NodeAuthorization::claim_node(Origin::signed(15), test_node(15)));
		assert_eq!(Owners::<Test>::get(test_node(15)), Some(15));
	});
}

#[test]
fn remove_claim_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			NodeAuthorization::remove_claim(Origin::signed(15), PeerId(vec![1, 2, 3])),
			Error::<Test>::PeerIdTooLong
		);
		assert_noop!(
			NodeAuthorization::remove_claim(Origin::signed(15), test_node(15)),
			Error::<Test>::NotClaimed
		);

		assert_noop!(
			NodeAuthorization::remove_claim(Origin::signed(15), test_node(20)),
			Error::<Test>::NotOwner
		);

		assert_noop!(
			NodeAuthorization::remove_claim(Origin::signed(20), test_node(20)),
			Error::<Test>::PermissionDenied
		);

		Owners::<Test>::insert(test_node(15), 15);
		AdditionalConnections::<Test>::insert(
			test_node(15),
			BTreeSet::from_iter(vec![test_node(20)])
		);
		assert_ok!(NodeAuthorization::remove_claim(Origin::signed(15), test_node(15)));
		assert!(!Owners::<Test>::contains_key(test_node(15)));
		assert!(!AdditionalConnections::<Test>::contains_key(test_node(15)));
	});
}

#[test]
fn transfer_node_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			NodeAuthorization::transfer_node(Origin::signed(15), PeerId(vec![1, 2, 3]), 10),
			Error::<Test>::PeerIdTooLong
		);
		assert_noop!(
			NodeAuthorization::transfer_node(Origin::signed(15), test_node(15), 10),
			Error::<Test>::NotClaimed
		);

		assert_noop!(
			NodeAuthorization::transfer_node(Origin::signed(15), test_node(20), 10),
			Error::<Test>::NotOwner
		);

		assert_ok!(NodeAuthorization::transfer_node(Origin::signed(20), test_node(20), 15));
		assert_eq!(Owners::<Test>::get(test_node(20)), Some(15));
	});
}

#[test]
fn add_connections_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			NodeAuthorization::add_connections(
				Origin::signed(15), PeerId(vec![1, 2, 3]), vec![test_node(5)]
			),
			Error::<Test>::PeerIdTooLong
		);
		assert_noop!(
			NodeAuthorization::add_connections(
				Origin::signed(15), test_node(15), vec![test_node(5)]
			),
			Error::<Test>::NotClaimed
		);

		assert_noop!(
			NodeAuthorization::add_connections(
				Origin::signed(15), test_node(20), vec![test_node(5)]
			),
			Error::<Test>::NotOwner
		);

		assert_ok!(
			NodeAuthorization::add_connections(
				Origin::signed(20),
				test_node(20),
				vec![test_node(15), test_node(5), test_node(25), test_node(20)]
			)
		);
		assert_eq!(
			AdditionalConnections::<Test>::get(test_node(20)),
			BTreeSet::from_iter(vec![test_node(5), test_node(15), test_node(25)])
		);
	});
}

#[test]
fn remove_connections_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			NodeAuthorization::remove_connections(
				Origin::signed(15), PeerId(vec![1, 2, 3]), vec![test_node(5)]
			),
			Error::<Test>::PeerIdTooLong
		);
		assert_noop!(
			NodeAuthorization::remove_connections(
				Origin::signed(15), test_node(15), vec![test_node(5)]
			),
			Error::<Test>::NotClaimed
		);

		assert_noop!(
			NodeAuthorization::remove_connections(
				Origin::signed(15), test_node(20), vec![test_node(5)]
			),
			Error::<Test>::NotOwner
		);

		AdditionalConnections::<Test>::insert(
			test_node(20),
			BTreeSet::from_iter(vec![test_node(5), test_node(15), test_node(25)])
		);
		assert_ok!(
			NodeAuthorization::remove_connections(
				Origin::signed(20),
				test_node(20),
				vec![test_node(15), test_node(5)]
			)
		);
		assert_eq!(
			AdditionalConnections::<Test>::get(test_node(20)),
			BTreeSet::from_iter(vec![test_node(25)])
		);
	});
}

#[test]
fn get_authorized_nodes_works() {
	new_test_ext().execute_with(|| {
		AdditionalConnections::<Test>::insert(
			test_node(20),
			BTreeSet::from_iter(vec![test_node(5), test_node(15), test_node(25)])
		);

		let mut authorized_nodes = Module::<Test>::get_authorized_nodes(&test_node(20));
		authorized_nodes.sort();
		assert_eq!(
			authorized_nodes,
			vec![test_node(5), test_node(10), test_node(15), test_node(25), test_node(30)]
		);
	});
}
