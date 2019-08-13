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
};
use system::{EventRecord, Phase};
use runtime_io::with_externalities;

#[test]
fn should_report_an_authority_and_trigger_on_offence() {
	with_externalities(&mut new_test_ext(), || {
		// given
		let session_index = 5;
		let time_slot = 42;
		assert_eq!(Offences::offence_reports(&KIND, &(session_index, time_slot)), vec![]);

		let offence = Offence {
			validator_set_count: 5,
			session_index,
			time_slot,
			offenders: vec![5],
		};

		// when
		Offences::report_offence(None, offence);

		// then
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
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
			validator_set_count: 5,
			session_index,
			time_slot,
			offenders: vec![5],
		};
		let offence2 = Offence {
			validator_set_count: 5,
			session_index,
			time_slot,
			offenders: vec![4],
		};

		// when
		Offences::report_offence(None, offence1);
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
		});

		Offences::report_offence(None, offence2);

		// then
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(20), Perbill::from_percent(45)]);
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
			validator_set_count: 5,
			session_index,
			time_slot,
			offenders: vec![5],
		};
		Offences::report_offence(None, offence.clone());
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
			f.clear();
		});

		// when
		// reportfor the second time
		Offences::report_offence(None, offence);

		// then
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![]);
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
			validator_set_count: 5,
			session_index,
			time_slot,
			offenders: vec![5],
		};
		Offences::report_offence(None, offence.clone());
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
			f.clear();
		});

		// when
		// reportfor the second time
		offence.time_slot += 1;
		Offences::report_offence(None, offence);

		// then
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
		});
	});
}

#[test]
fn should_deposit_event() {
	with_externalities(&mut new_test_ext(), || {
		// given
		let session_index = 5;
		let time_slot = 42;
		assert_eq!(
			Offences::offence_reports(&KIND, &(session_index, time_slot)),
			vec![]
		);

		let offence = Offence {
			validator_set_count: 5,
			session_index,
			time_slot,
			offenders: vec![5],
		};

		// when
		Offences::report_offence(None, offence);

		// then
		assert_eq!(
			System::events(),
			vec![EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: TestEvent::offences(crate::Event::Offence(KIND, session_index, time_slot)),
				topics: vec![],
			}]
		);
	});
}

#[test]
fn doesnt_deposit_event_for_dups() {
	with_externalities(&mut new_test_ext(), || {
		// given
		let session_index = 5;
		let time_slot = 42;
		assert_eq!(Offences::offence_reports(&KIND, &(session_index, time_slot)), vec![]);

		let offence = Offence {
			validator_set_count: 5,
			session_index,
			time_slot,
			offenders: vec![5],
		};
		Offences::report_offence(None, offence.clone());
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
			f.clear();
		});

		// when
		// report for the second time
		Offences::report_offence(None, offence);

		// then
		// there is only one event.
		assert_eq!(
			System::events(),
			vec![EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: TestEvent::offences(crate::Event::Offence(KIND, session_index, time_slot)),
				topics: vec![],
			}]
		);
	});
}

#[test]
fn should_properly_count_offences() {
	// We report two different authorities for the same issue. Ultimately, the 1st authority
	// should have `count` equal 2 and the count of the 2nd one should be equal to 1.
	with_externalities(&mut new_test_ext(), || {
		// given
		let session_index = 5;
		let time_slot = 42;
		assert_eq!(Offences::offence_reports(&KIND, &(session_index, time_slot)), vec![]);

		let offence1 = Offence {
			validator_set_count: 5,
			session_index,
			time_slot,
			offenders: vec![5],
		};
		let offence2 = Offence {
			validator_set_count: 5,
			session_index,
			time_slot,
			offenders: vec![4],
		};
		Offences::report_offence(None, offence1);
		with_on_offence_fractions(|f| {
			assert_eq!(f.clone(), vec![Perbill::from_percent(25)]);
			f.clear();
		});

		// when
		// report for the second time
		Offences::report_offence(None, offence2);

		// then
		// the 1st authority should have count 2 and the 2nd one should be reported only once.
		assert_eq!(
			Offences::offence_reports(&KIND, &(session_index, time_slot)),
			vec![
				OffenceDetails { offender: 5, count: 2, reporters: vec![] },
				OffenceDetails { offender: 4, count: 1, reporters: vec![] },
			]
		);
	});
}
