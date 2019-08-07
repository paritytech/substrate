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
use crate::mock::{Offences, Offence, KIND, new_test_ext, ON_OFFENCE_PERBILL};
use runtime_io::with_externalities;

#[test]
fn should_report_an_authority_and_trigger_on_offence() {
	with_externalities(&mut new_test_ext(), || {
		let session_index = 5;
		let time_slot = 42;
		assert_eq!(Offences::offence_reports(&KIND, &(session_index, time_slot)), vec![]);

		let offence = Offence {
			validators_count: 5,
			session_index,
			time_slot,
			offenders: vec![5],
		};

		Offences::report_offence(None, offence);

		ON_OFFENCE_PERBILL.with(|f| {
			assert_eq!(f.borrow().clone(), vec![Perbill::from_percent(20)]);
		});
	});
}
