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
use crate::mock::{Offences, Offence, KIND, new_test_ext, ON_OFFENCE_PERBILL};
use runtime_io::with_externalities;

#[test]
fn should_report_an_authority_and_trigger_on_offence() {
	with_externalities(&mut new_test_ext(), || {
		// given
		let session_index = 5;
		let time_slot = 42;
		assert_eq!(Offences::offence_reports(&KIND, &(session_index, time_slot)), vec![]);

		let offence = Offence {
			validators_count: 5,
			session_index,
			time_slot,
			offenders: vec![5],
		};

		// when
		Offences::report_offence(None, offence);

		// then
		ON_OFFENCE_PERBILL.with(|f| {
			assert_eq!(f.borrow().clone(), vec![Perbill::from_percent(25)]);
		});
	});
}

#[test]
fn should_calculate_the_fraction_corectly() {
	with_externalities(&mut new_test_ext(), || {
		// given
		let session_index = 5;
		let time_slot = 42;
		assert_eq!(Offences::offence_reports(&KIND, &(session_index, time_slot)), vec![]);
		let offence1 = Offence {
			validators_count: 5,
			session_index,
			time_slot,
			offenders: vec![5],
		};
		let offence2 = Offence {
			validators_count: 5,
			session_index,
			time_slot,
			offenders: vec![4],
		};

		// when
		Offences::report_offence(None, offence1);
		ON_OFFENCE_PERBILL.with(|f| {
			assert_eq!(f.borrow().clone(), vec![Perbill::from_percent(25)]);
		});

		Offences::report_offence(None, offence2);

		// then
		ON_OFFENCE_PERBILL.with(|f| {
			assert_eq!(f.borrow().clone(), vec![Perbill::from_percent(20), Perbill::from_percent(45)]);
		});
	});
}

#[test]
fn should_not_report_the_same_authority_twice_in_the_same_slot() {
	with_externalities(&mut new_test_ext(), || {
		// given
		let session_index = 5;
		let time_slot = 42;
		assert_eq!(Offences::offence_reports(&KIND, &(session_index, time_slot)), vec![]);

		let offence = Offence {
			validators_count: 5,
			session_index,
			time_slot,
			offenders: vec![5],
		};
		Offences::report_offence(None, offence.clone());
		ON_OFFENCE_PERBILL.with(|f| {
			assert_eq!(f.borrow().clone(), vec![Perbill::from_percent(25)]);
			*f.borrow_mut() = vec![];
		});

		// when
		// reportfor the second time
		Offences::report_offence(None, offence);

		// then
		ON_OFFENCE_PERBILL.with(|f| {
			assert_eq!(f.borrow().clone(), vec![]);
		});
	});
}


#[test]
fn should_report_in_different_time_slot() {
	with_externalities(&mut new_test_ext(), || {
		// given
		let session_index = 5;
		let time_slot = 42;
		assert_eq!(Offences::offence_reports(&KIND, &(session_index, time_slot)), vec![]);

		let mut offence = Offence {
			validators_count: 5,
			session_index,
			time_slot,
			offenders: vec![5],
		};
		Offences::report_offence(None, offence.clone());
		ON_OFFENCE_PERBILL.with(|f| {
			assert_eq!(f.borrow().clone(), vec![Perbill::from_percent(25)]);
			*f.borrow_mut() = vec![];
		});

		// when
		// reportfor the second time
		offence.time_slot += 1;
		Offences::report_offence(None, offence);

		// then
		ON_OFFENCE_PERBILL.with(|f| {
			assert_eq!(f.borrow().clone(), vec![Perbill::from_percent(25)]);
		});
	});
}

