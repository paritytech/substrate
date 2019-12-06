// Copyright 2019 Parity Technologies (UK) Ltd.
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

use super::*;
use mock::*;

use support::{assert_ok, assert_noop};

#[test]
fn founding_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(Society::found(Origin::signed(5), 2), "Invalid origin");
		assert_ok!(Society::found(Origin::signed(1), 2));
		assert_eq!(Society::members(), vec![2]);
		assert_eq!(Society::head(), Some(2));
		assert_noop!(Society::found(Origin::signed(1), 3), "already founded");
	});
}
