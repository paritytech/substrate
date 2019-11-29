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
	Offences, System, Offence, TestEvent, KIND, new_test_ext, with_on_offence_fractions,
	offence_reports,
};
use sr_primitives::Perbill;
use system::{EventRecord, Phase};

#[test]
fn should_report_an_authority_and_trigger_on_offence() {
	new_test_ext().execute_with(|| {
		// given
		let time_slot = 42;
		assert_eq!(offence_reports(KIND, time_slot), vec![]);

		let offence = Offence {
			validator_set_count: 5,
			time_slot,
			offenders: vec![5],
		};

		// when
		Offences::report_offence(vec![], offence);

		// then
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
		});
	});
}

#[test]
fn should_not_report_the_same_authority_twice_in_the_same_slot() {
	new_test_ext().execute_with(|| {
		// given
		let time_slot = 42;
		assert_eq!(offence_reports(KIND, time_slot), vec![]);

		let offence = Offence {
			validator_set_count: 5,
			time_slot,
			offenders: vec![5],
		};
		Offences::report_offence(vec![], offence.clone());
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
			f.clear();
		});

		// when
		// report for the second time
		Offences::report_offence(vec![], offence);

		// then
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![]);
		});
	});
}


#[test]
fn should_report_in_different_time_slot() {
	new_test_ext().execute_with(|| {
		// given
		let time_slot = 42;
		assert_eq!(offence_reports(KIND, time_slot), vec![]);

		let mut offence = Offence {
			validator_set_count: 5,
			time_slot,
			offenders: vec![5],
		};
		Offences::report_offence(vec![], offence.clone());
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
			f.clear();
		});

		// when
		// reportfor the second time
		offence.time_slot += 1;
		Offences::report_offence(vec![], offence);

		// then
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
		});
	});
}

#[test]
fn should_deposit_event() {
	new_test_ext().execute_with(|| {
		// given
		let time_slot = 42;
		assert_eq!(offence_reports(KIND, time_slot), vec![]);

		let offence = Offence {
			validator_set_count: 5,
			time_slot,
			offenders: vec![5],
		};

		// when
		Offences::report_offence(vec![], offence);

		// then
		assert_eq!(
			System::events(),
			vec![EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: TestEvent::offences(crate::Event::Offence(KIND, time_slot.encode())),
				topics: vec![],
			}]
		);
	});
}

#[test]
fn doesnt_deposit_event_for_dups() {
	new_test_ext().execute_with(|| {
		// given
		let time_slot = 42;
		assert_eq!(offence_reports(KIND, time_slot), vec![]);

		let offence = Offence {
			validator_set_count: 5,
			time_slot,
			offenders: vec![5],
		};
		Offences::report_offence(vec![], offence.clone());
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
			f.clear();
		});

		// when
		// report for the second time
		Offences::report_offence(vec![], offence);

		// then
		// there is only one event.
		assert_eq!(
			System::events(),
			vec![EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: TestEvent::offences(crate::Event::Offence(KIND, time_slot.encode())),
				topics: vec![],
			}]
		);
	});
}

#[test]
fn should_properly_count_offences() {
	// We report two different authorities for the same issue. Ultimately, the 1st authority
	// should have `count` equal 2 and the count of the 2nd one should be equal to 1.
	new_test_ext().execute_with(|| {
		// given
		let time_slot = 42;
		assert_eq!(offence_reports(KIND, time_slot), vec![]);

		let offence1 = Offence {
			validator_set_count: 5,
			time_slot,
			offenders: vec![5],
		};
		let offence2 = Offence {
			validator_set_count: 5,
			time_slot,
			offenders: vec![4],
		};
		Offences::report_offence(vec![], offence1);
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
			f.clear();
		});

		// when
		// report for the second time
		Offences::report_offence(vec![], offence2);

		// then
		// the 1st authority should have count 2 and the 2nd one should be reported only once.
		assert_eq!(
			offence_reports(KIND, time_slot),
			vec![
				OffenceDetails { offender: 5, reporters: vec![] },
				OffenceDetails { offender: 4, reporters: vec![] },
			]
		);
	});
}
