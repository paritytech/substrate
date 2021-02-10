// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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
	Offences, System, Offence, Event, KIND, new_test_ext, with_on_offence_fractions,
	offence_reports, set_can_report, set_offence_weight,
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
				event: Event::offences(crate::Event::Offence(KIND, time_slot.encode(), true)),
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
				event: Event::offences(crate::Event::Offence(KIND, time_slot.encode(), true)),
				topics: vec![],
			}]
		);
	});
}

#[test]
fn reports_if_an_offence_is_dup() {
	type TestOffence = Offence<u64>;

	new_test_ext().execute_with(|| {
		let time_slot = 42;
		assert_eq!(offence_reports(KIND, time_slot), vec![]);

		let offence = |time_slot, offenders| TestOffence {
			validator_set_count: 5,
			time_slot,
			offenders,
		};

		let mut test_offence = offence(time_slot, vec![0]);

		// the report for authority 0 at time slot 42 should not be a known
		// offence
		assert!(
			!<Offences as ReportOffence<_, _, TestOffence>>::is_known_offence(
				&test_offence.offenders,
				&test_offence.time_slot
			)
		);

		// we report an offence for authority 0 at time slot 42
		Offences::report_offence(vec![], test_offence.clone()).unwrap();

		// the same report should be a known offence now
		assert!(
			<Offences as ReportOffence<_, _, TestOffence>>::is_known_offence(
				&test_offence.offenders,
				&test_offence.time_slot
			)
		);

		// and reporting it again should yield a duplicate report error
		assert_eq!(
			Offences::report_offence(vec![], test_offence.clone()),
			Err(OffenceError::DuplicateReport)
		);

		// after adding a new offender to the offence report
		test_offence.offenders.push(1);

		// it should not be a known offence anymore
		assert!(
			!<Offences as ReportOffence<_, _, TestOffence>>::is_known_offence(
				&test_offence.offenders,
				&test_offence.time_slot
			)
		);

		// and reporting it again should work without any error
		assert_eq!(
			Offences::report_offence(vec![], test_offence.clone()),
			Ok(())
		);

		// creating a new offence for the same authorities on the next slot
		// should be considered a new offence and thefore not known
		let test_offence_next_slot = offence(time_slot + 1, vec![0, 1]);
		assert!(
			!<Offences as ReportOffence<_, _, TestOffence>>::is_known_offence(
				&test_offence_next_slot.offenders,
				&test_offence_next_slot.time_slot
			)
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
				event: Event::offences(crate::Event::Offence(KIND, 42u128.encode(), false)),
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

#[test]
fn weight_soft_limit_is_used() {
	new_test_ext().execute_with(|| {
		set_can_report(false);
		// Only 2 can fit in one block
		set_offence_weight(<mock::Runtime as Config>::WeightSoftLimit::get() / 2);

		// Queue 3 offences
		// #1
		let offence = Offence {
			validator_set_count: 5,
			time_slot: 42,
			offenders: vec![5],
		};
		Offences::report_offence(vec![], offence).unwrap();
		// #2
		let offence = Offence {
			validator_set_count: 5,
			time_slot: 62,
			offenders: vec![5],
		};
		Offences::report_offence(vec![], offence).unwrap();
		// #3
		let offence = Offence {
			validator_set_count: 5,
			time_slot: 72,
			offenders: vec![5],
		};
		Offences::report_offence(vec![], offence).unwrap();
		// 3 are queued
		assert_eq!(Offences::deferred_offences().len(), 3);

		// Allow reporting
		set_can_report(true);

		Offences::on_initialize(3);
		// Two are completed, one is left in the queue
		assert_eq!(Offences::deferred_offences().len(), 1);

		Offences::on_initialize(4);
		// All are done now
		assert_eq!(Offences::deferred_offences().len(), 0);
	})
}
