// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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
	offence_reports, set_can_report,
};
use sp_runtime::Perbill;
use frame_support::traits::OnInitialize;
use frame_system::{EventRecord, Phase};

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
		Offences::report_offence(vec![], offence).unwrap();

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
		Offences::report_offence(vec![], offence.clone()).unwrap();
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
			f.clear();
		});

		// when
		// report for the second time
		assert_eq!(Offences::report_offence(vec![], offence), Err(OffenceError::DuplicateReport));

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
		Offences::report_offence(vec![], offence.clone()).unwrap();
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
			f.clear();
		});

		// when
		// report for the second time
		offence.time_slot += 1;
		Offences::report_offence(vec![], offence).unwrap();

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
		Offences::report_offence(vec![], offence).unwrap();

		// then
		assert_eq!(
			System::events(),
			vec![EventRecord {
				phase: Phase::Initialization,
				event: TestEvent::offences(crate::Event::Offence(KIND, time_slot.encode(), true)),
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
		Offences::report_offence(vec![], offence.clone()).unwrap();
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
			f.clear();
		});

		// when
		// report for the second time
		assert_eq!(Offences::report_offence(vec![], offence), Err(OffenceError::DuplicateReport));

		// then
		// there is only one event.
		assert_eq!(
			System::events(),
			vec![EventRecord {
				phase: Phase::Initialization,
				event: TestEvent::offences(crate::Event::Offence(KIND, time_slot.encode(), true)),
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
		Offences::report_offence(vec![], offence1).unwrap();
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
			f.clear();
		});

		// when
		// report for the second time
		Offences::report_offence(vec![], offence2).unwrap();

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

#[test]
fn should_queue_and_resubmit_rejected_offence() {
	new_test_ext().execute_with(|| {
		set_can_report(false);

		// will get deferred
		let offence = Offence {
			validator_set_count: 5,
			time_slot: 42,
			offenders: vec![5],
		};
		Offences::report_offence(vec![], offence).unwrap();
		assert_eq!(Offences::deferred_offences().len(), 1);
		// event also indicates unapplied.
		assert_eq!(
			System::events(),
			vec![EventRecord {
				phase: Phase::Initialization,
				event: TestEvent::offences(crate::Event::Offence(KIND, 42u128.encode(), false)),
				topics: vec![],
			}]
		);

		// will not dequeue
		Offences::on_initialize(2);

		// again
		let offence = Offence {
			validator_set_count: 5,
			time_slot: 62,
			offenders: vec![5],
		};
		Offences::report_offence(vec![], offence).unwrap();
		assert_eq!(Offences::deferred_offences().len(), 2);

		set_can_report(true);

		// can be submitted
		let offence = Offence {
			validator_set_count: 5,
			time_slot: 72,
			offenders: vec![5],
		};
		Offences::report_offence(vec![], offence).unwrap();
		assert_eq!(Offences::deferred_offences().len(), 2);

		Offences::on_initialize(3);
		assert_eq!(Offences::deferred_offences().len(), 0);
	})
}
