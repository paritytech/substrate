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

use super::*;
use runtime_io::with_externalities;
use mock::{new_test_ext, System, Babe};
use sr_primitives::traits::Header;
#[test]
fn empty_randomness_is_correct() {
	let s = compute_randomness([0; RANDOMNESS_LENGTH], 0, std::iter::empty(), None);
	assert_eq!(s, [74, 25, 49, 128, 53, 97, 244, 49, 222, 202, 176, 2, 231, 66, 95, 10, 133, 49, 213, 228, 86, 161, 164, 127, 217, 153, 138, 37, 48, 192, 248, 0]);
}

#[test]
fn check_module() {
	with_externalities(&mut new_test_ext(vec![0, 1, 2, 3]), || {
		System::initialize(&1, &Default::default(), &Default::default(), &Default::default());
		assert_eq!(Babe::current_slot(), 0);
		let mut header = System::finalize();
		System::initialize(&2, &header.hash(), &Default::default(), &Default::default());
		assert_eq!(Babe::current_slot(), 0);
		header = System::finalize();
		System::initialize(&3, &header.hash(), &Default::default(), &Default::default());
		assert_eq!(Babe::current_slot(), 1);
		header = System::finalize();
		System::initialize(&4, &header.hash(), &Default::default(), &Default::default());
		header = System::finalize();
		System::initialize(&5, &header.hash(), &Default::default(), &Default::default());
		header = System::finalize();
		System::initialize(&6, &header.hash(), &Default::default(), &Default::default());
		header = System::finalize();
		System::initialize(&7, &header.hash(), &Default::default(), &Default::default());
		System::finalize();
		let _slot_duration = Babe::slot_duration();

		Babe::randomness_change_epoch(1);
	})
}
