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

//! Consensus extension module tests for BABE consensus.
#![allow(unused_imports)]
use super::*;
use runtime_io::with_externalities;
use mock::{new_test_ext, Babe, Test};
use sr_primitives::traits::Header;
use session::ShouldEndSession;

#[test]
fn empty_randomness_is_correct() {
	let s = compute_randomness([0; RANDOMNESS_LENGTH], 0, std::iter::empty(), None);
	assert_eq!(s, [74, 25, 49, 128, 53, 97, 244, 49, 222, 202, 176, 2, 231, 66, 95, 10, 133, 49, 213, 228, 86, 161, 164, 127, 217, 153, 138, 37, 48, 192, 248, 0]);
}

#[test]
fn initial_values() {
	with_externalities(&mut new_test_ext(vec![0, 1, 2, 3]), || {
		assert_eq!(Babe::authorities().len(), 4)
	})
}

#[test]
fn check_module() {
	with_externalities(&mut new_test_ext(vec![0, 1, 2, 3]), || {
		assert!(!Babe::should_end_session(0), "Genesis does not change sessions");
		assert!(!Babe::should_end_session(200000),
			"BABE does not include the block number in epoch calculations");
	})
}

#[test]
fn check_epoch_change() {
	with_externalities(&mut new_test_ext(vec![0, 1, 2, 3]), || {
		system::Module::<Test>::initialize(&1, &Default::default(), &Default::default(), &Default::default());
		assert!(!Babe::should_end_session(0), "Genesis does not change sessions");
		assert!(!Babe::should_end_session(200000),
			"BABE does not include the block number in epoch calculations");
		EpochStartSlot::put(1);
		CurrentSlot::put(3);
		assert!(!Babe::should_end_session(0));
		CurrentSlot::put(4);
		assert!(Babe::should_end_session(0));
		Babe::randomness_change_epoch(1);
	})
}

#[test]
fn authority_index() {
	with_externalities(&mut new_test_ext(vec![0, 1, 2, 3]), || {
		assert_eq!(Babe::find_author((&[(BABE_ENGINE_ID, &[][..])]).into_iter().cloned()), None,
			"Trivially invalid authorities are ignored");
		assert_eq!(Babe::find_author((&[(BABE_ENGINE_ID, &[][..])]).into_iter().cloned()), None,
			"Trivially invalid authorities are ignored")
	})
}
