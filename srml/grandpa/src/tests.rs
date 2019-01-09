// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

use primitives::{testing, traits::OnFinalise};
use primitives::traits::Header;
use runtime_io::with_externalities;
use mock::{Grandpa, System, new_test_ext};
use system::{EventRecord, Phase};
use {RawLog, RawEvent};

#[test]
fn authorities_change_logged() {
	with_externalities(&mut new_test_ext(vec![(1, 1), (2, 1), (3, 1)]), || {
		System::initialise(&1, &Default::default(), &Default::default());
		Grandpa::schedule_change(vec![(4, 1), (5, 1), (6, 1)], 0).unwrap();

		System::note_finished_extrinsics();
		Grandpa::on_finalise(1);

		let header = System::finalise();
		assert_eq!(header.digest, testing::Digest {
			logs: vec![
				RawLog::AuthoritiesChangeSignal(0, vec![(4, 1), (5, 1), (6, 1)]).into(),
			],
		});

		assert_eq!(System::events(), vec![
			EventRecord {
				phase: Phase::Finalization,
				event: RawEvent::NewAuthorities(vec![(4, 1), (5, 1), (6, 1)]).into(),
			},
		]);
	});
}

#[test]
fn authorities_change_logged_after_delay() {
	with_externalities(&mut new_test_ext(vec![(1, 1), (2, 1), (3, 1)]), || {
		System::initialise(&1, &Default::default(), &Default::default());
		Grandpa::schedule_change(vec![(4, 1), (5, 1), (6, 1)], 1).unwrap();
		Grandpa::on_finalise(1);
		let header = System::finalise();
		assert_eq!(header.digest, testing::Digest {
			logs: vec![
				RawLog::AuthoritiesChangeSignal(1, vec![(4, 1), (5, 1), (6, 1)]).into(),
			],
		});

		// no change at this height.
		assert_eq!(System::events(), vec![]);

		System::initialise(&2, &header.hash(), &Default::default());
		System::note_finished_extrinsics();
		Grandpa::on_finalise(2);

		let _header = System::finalise();
		assert_eq!(System::events(), vec![
			EventRecord {
				phase: Phase::Finalization,
				event: RawEvent::NewAuthorities(vec![(4, 1), (5, 1), (6, 1)]).into(),
			},
		]);
	});
}

#[test]
fn cannot_schedule_change_when_one_pending() {
	with_externalities(&mut new_test_ext(vec![(1, 1), (2, 1), (3, 1)]), || {
		System::initialise(&1, &Default::default(), &Default::default());
		Grandpa::schedule_change(vec![(4, 1), (5, 1), (6, 1)], 1).unwrap();
		assert!(Grandpa::pending_change().is_some());
		assert!(Grandpa::schedule_change(vec![(5, 1)], 1).is_err());

		Grandpa::on_finalise(1);
		let header = System::finalise();

		System::initialise(&2, &header.hash(), &Default::default());
		assert!(Grandpa::pending_change().is_some());
		assert!(Grandpa::schedule_change(vec![(5, 1)], 1).is_err());

		Grandpa::on_finalise(2);
		let header = System::finalise();

		System::initialise(&3, &header.hash(), &Default::default());
		assert!(Grandpa::pending_change().is_none());
		assert!(Grandpa::schedule_change(vec![(5, 1)], 1).is_ok());

		Grandpa::on_finalise(3);
		let _header = System::finalise();
	});
}
