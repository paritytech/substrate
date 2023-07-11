// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Tests for the offences module.

#![cfg(test)]

use super::*;
use crate::mock::{
	new_test_ext, offence_reports, report_id, with_on_offence_fractions, Offence, Offences,
	Runtime, RuntimeEvent, System, KIND,
};
use frame_support::assert_noop;
use frame_system::{EventRecord, Phase};
use sp_runtime::Perbill;

static SESSION_INDEX: u32 = 10;

#[test]
fn should_report_an_authority_and_trigger_on_offence() {
	new_test_ext().execute_with(|| {
		// given
		let time_slot = 42;
		assert_eq!(offence_reports(KIND, time_slot), vec![]);

		let offence = Offence {
			validator_set_count: 5,
			session_index: SESSION_INDEX,
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
			session_index: SESSION_INDEX,
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
fn should_not_report_an_obsolete_offence() {
	new_test_ext().execute_with(|| {
		// given
		let time_slot = 42;
		assert_eq!(offence_reports(KIND, time_slot), vec![]);

		let offence = Offence {
			validator_set_count: 5,
			session_index: SESSION_INDEX - 7,
			time_slot,
			offenders: vec![5],
		};
		assert_noop!(Offences::report_offence(vec![], offence), OffenceError::ObsoleteReport);

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
			session_index: SESSION_INDEX,
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
			session_index: SESSION_INDEX,
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
				event: RuntimeEvent::Offences(crate::Event::Offence {
					kind: KIND,
					timeslot: time_slot.encode()
				}),
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
			session_index: SESSION_INDEX,
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
				event: RuntimeEvent::Offences(crate::Event::Offence {
					kind: KIND,
					timeslot: time_slot.encode()
				}),
				topics: vec![],
			}]
		);
	});
}

#[test]
fn reports_if_an_offence_is_dup() {
	new_test_ext().execute_with(|| {
		let time_slot = 42;
		assert_eq!(offence_reports(KIND, time_slot), vec![]);

		let offence = |time_slot, offenders| Offence {
			validator_set_count: 5,
			session_index: SESSION_INDEX,
			time_slot,
			offenders,
		};

		let mut test_offence = offence(time_slot, vec![0]);

		// the report for authority 0 at time slot 42 should not be a known
		// offence
		assert!(!<Offences as ReportOffence<_, _, Offence>>::is_known_offence(
			&test_offence.offenders,
			&test_offence.time_slot
		));

		// we report an offence for authority 0 at time slot 42
		Offences::report_offence(vec![], test_offence.clone()).unwrap();

		// the same report should be a known offence now
		assert!(<Offences as ReportOffence<_, _, Offence>>::is_known_offence(
			&test_offence.offenders,
			&test_offence.time_slot
		));

		// and reporting it again should yield a duplicate report error
		assert_eq!(
			Offences::report_offence(vec![], test_offence.clone()),
			Err(OffenceError::DuplicateReport)
		);

		// after adding a new offender to the offence report
		test_offence.offenders.push(1);

		// it should not be a known offence anymore
		assert!(!<Offences as ReportOffence<_, _, Offence>>::is_known_offence(
			&test_offence.offenders,
			&test_offence.time_slot
		));

		// and reporting it again should work without any error
		assert_eq!(Offences::report_offence(vec![], test_offence.clone()), Ok(()));

		// creating a new offence for the same authorities on the next slot
		// should be considered a new offence and thefore not known
		let test_offence_next_slot = offence(time_slot + 1, vec![0, 1]);
		assert!(!<Offences as ReportOffence<_, _, Offence>>::is_known_offence(
			&test_offence_next_slot.offenders,
			&test_offence_next_slot.time_slot
		));
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
			session_index: SESSION_INDEX,
			time_slot,
			offenders: vec![5],
		};
		let offence2 = Offence {
			validator_set_count: 5,
			session_index: SESSION_INDEX,
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
fn should_properly_store_offences() {
	new_test_ext().execute_with(|| {
		// given
		let time_slot = 42;
		assert_eq!(offence_reports(KIND, time_slot), vec![]);

		let offence1 = Offence {
			validator_set_count: 5,
			session_index: SESSION_INDEX,
			time_slot,
			offenders: vec![5],
		};
		let offence2 = Offence {
			validator_set_count: 5,
			session_index: SESSION_INDEX,
			time_slot: time_slot + 1,
			offenders: vec![4],
		};
		let offence3 = Offence {
			validator_set_count: 5,
			session_index: SESSION_INDEX + 1,
			time_slot: time_slot + 1,
			offenders: vec![6, 7],
		};
		let offence4 = Offence {
			validator_set_count: 5,
			session_index: SESSION_INDEX - 1,
			time_slot: time_slot - 1,
			offenders: vec![3],
		};

		// when
		Offences::report_offence(vec![], offence1).unwrap();

		// then
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
			f.clear();
		});

		// when
		// report for the second time
		Offences::report_offence(vec![], offence2).unwrap();
		Offences::report_offence(vec![], offence3).unwrap();
		Offences::report_offence(vec![], offence4).unwrap();

		// then
		let prev_session_reports = SessionReports::<Runtime>::get(SESSION_INDEX - 1);
		assert_eq!(
			prev_session_reports,
			vec![(KIND, (time_slot - 1).encode(), report_id(time_slot - 1, 3)),]
		);

		let session_reports = SessionReports::<Runtime>::get(SESSION_INDEX);
		assert_eq!(
			session_reports,
			vec![
				(KIND, time_slot.encode(), report_id(time_slot, 5)),
				(KIND, (time_slot + 1).encode(), report_id(time_slot + 1, 4)),
			]
		);

		let next_session_reports = SessionReports::<Runtime>::get(SESSION_INDEX + 1);
		assert_eq!(
			next_session_reports,
			vec![
				(KIND, (time_slot + 1).encode(), report_id(time_slot + 1, 6)),
				(KIND, (time_slot + 1).encode(), report_id(time_slot + 1, 7)),
			]
		);
	});
}

#[test]
fn should_properly_clear_obsolete_offences() {
	new_test_ext().execute_with(|| {
		// given
		let time_slot = 42;
		assert_eq!(offence_reports(KIND, time_slot), vec![]);

		let offence1 = Offence {
			validator_set_count: 5,
			session_index: SESSION_INDEX,
			time_slot,
			offenders: vec![5],
		};
		let offence2 = Offence {
			validator_set_count: 5,
			session_index: SESSION_INDEX,
			time_slot: time_slot + 1,
			offenders: vec![4],
		};
		let offence3 = Offence {
			validator_set_count: 5,
			session_index: SESSION_INDEX + 1,
			time_slot: time_slot + 5,
			offenders: vec![6, 7],
		};
		let offence4 = Offence {
			validator_set_count: 5,
			session_index: SESSION_INDEX - 1,
			time_slot: time_slot - 1,
			offenders: vec![3],
		};

		// when
		Offences::report_offence(vec![], offence1).unwrap();

		// then
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
			f.clear();
		});

		// when
		// report for the second time
		Offences::report_offence(vec![], offence2).unwrap();
		Offences::report_offence(vec![], offence3).unwrap();
		Offences::report_offence(vec![], offence4).unwrap();

		assert_eq!(
			offence_reports(KIND, time_slot - 1),
			vec![OffenceDetails { offender: 3, reporters: vec![] }]
		);

		<Offences as SessionChangeListener>::on_session_change(SESSION_INDEX + 5);

		assert_eq!(offence_reports(KIND, time_slot - 1), vec![]);

		// then
		let obsolete_session_reports = SessionReports::<Runtime>::get(SESSION_INDEX - 1);
		assert_eq!(obsolete_session_reports, vec![]);

		let session_reports = SessionReports::<Runtime>::get(SESSION_INDEX + 1);
		assert_eq!(
			session_reports,
			vec![
				(KIND, (time_slot + 5).encode(), report_id(time_slot + 5, 6)),
				(KIND, (time_slot + 5).encode(), report_id(time_slot + 5, 7)),
			]
		);

		assert_eq!(
			offence_reports(KIND, time_slot + 5),
			vec![
				OffenceDetails { offender: 6, reporters: vec![] },
				OffenceDetails { offender: 7, reporters: vec![] },
			]
		);
	});
}
