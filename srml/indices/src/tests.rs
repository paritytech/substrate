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
use crate::mock::{Indices, new_test_ext, make_account, kill_account, TestIsDeadAccount};
use runtime_io::with_externalities;

#[test]
fn indexing_lookup_should_work() {
	with_externalities(
		&mut new_test_ext(),
		|| {
			assert_eq!(Indices::lookup_index(0), Some(1));
			assert_eq!(Indices::lookup_index(1), Some(2));
			assert_eq!(Indices::lookup_index(2), Some(3));
			assert_eq!(Indices::lookup_index(3), Some(4));
			assert_eq!(Indices::lookup_index(4), None);
		},
	);
}

#[test]
fn default_indexing_on_new_accounts_should_work() {
	with_externalities(
		&mut new_test_ext(),
		|| {
			assert_eq!(Indices::lookup_index(4), None);
			make_account(5);
			assert_eq!(Indices::lookup_index(4), Some(5));
		},
	);
}

#[test]
fn reclaim_indexing_on_new_accounts_should_work() {
	with_externalities(
		&mut new_test_ext(),
		|| {
			assert_eq!(Indices::lookup_index(1), Some(2));
			assert_eq!(Indices::lookup_index(4), None);

			kill_account(2);					// index 1 no longer locked to id 2

			make_account(1 + 256);				// id 257 takes index 1.
			assert_eq!(Indices::lookup_index(1), Some(257));
		},
	);
}

#[test]
fn alive_account_should_prevent_reclaim() {
	with_externalities(
		&mut new_test_ext(),
		|| {
			assert!(!TestIsDeadAccount::is_dead_account(&2));
			assert_eq!(Indices::lookup_index(1), Some(2));
			assert_eq!(Indices::lookup_index(4), None);

			make_account(1 + 256);				// id 257 takes index 1.
			assert_eq!(Indices::lookup_index(4), Some(257));
		},
	);
}
