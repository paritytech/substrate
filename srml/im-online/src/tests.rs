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

//! Tests for the offences module.

#![cfg(test)]

use super::*;
use crate::mock::{
	ImOnline, new_test_ext,
};
use runtime_io::with_externalities;


#[test]
fn test_unresponsiveness_slash_fraction() {
	// A single case of unresponsiveness is not slashed.
	assert_eq!(
		UnresponsivenessOffence::<()>::slash_fraction(1, 50),
		Perbill::zero(),
	);

	assert_eq!(
		UnresponsivenessOffence::<()>::slash_fraction(3, 50),
		Perbill::from_parts(6000000), // 0.6%
	);

	// One third offline should be punished around 5%.
	assert_eq!(
		UnresponsivenessOffence::<()>::slash_fraction(17, 50),
		Perbill::from_parts(48000000), // 4.8%
	);
}

#[test]
fn should_correctly_report_offline_validators() {
	with_externalities(&mut new_test_ext(), || {
		// given

		// when

		// then
		assert!(ImOnline::is_online_in_current_session(1));
		assert!(ImOnline::is_online_in_current_session(2));
		assert!(ImOnline::is_online_in_current_session(3));
	});
}
