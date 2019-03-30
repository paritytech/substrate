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

use lazy_static::lazy_static;
use crate::mock::{System, Aura, new_test_ext};
use primitives::traits::Header;
use runtime_io::with_externalities;
use parking_lot::Mutex;
use crate::{AuraReport, HandleReport};

#[test]
fn aura_report_gets_skipped_correctly() {
	let mut report = AuraReport {
		start_slot: 3,
		skipped: 15,
	};

	let mut validators = vec![0; 10];
	report.punish(10, |idx, count| validators[idx] += count);
	assert_eq!(validators, vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]);

	let mut validators = vec![0; 10];
	report.skipped = 5;
	report.punish(10, |idx, count| validators[idx] += count);
	assert_eq!(validators, vec![0, 0, 0, 1, 1, 1, 1, 1, 0, 0]);

	let mut validators = vec![0; 10];
	report.start_slot = 8;
	report.punish(10, |idx, count| validators[idx] += count);
	assert_eq!(validators, vec![1, 1, 1, 0, 0, 0, 0, 0, 1, 1]);

	let mut validators = vec![0; 4];
	report.start_slot = 1;
	report.skipped = 3;
	report.punish(4, |idx, count| validators[idx] += count);
	assert_eq!(validators, vec![0, 1, 1, 1]);

	let mut validators = vec![0; 4];
	report.start_slot = 2;
	report.punish(4, |idx, count| validators[idx] += count);
	assert_eq!(validators, vec![1, 0, 1, 1]);
}

#[test]
fn aura_reports_offline() {
	lazy_static! {
		static ref SLASH_COUNTS: Mutex<Vec<usize>> = Mutex::new(vec![0; 4]);
	}

	struct HandleTestReport;
	impl HandleReport for HandleTestReport {
		fn handle_report(report: AuraReport) {
			let mut counts = SLASH_COUNTS.lock();
			report.punish(counts.len(), |idx, count| counts[idx] += count);
		}
	}

	with_externalities(&mut new_test_ext(vec![0, 1, 2, 3]), || {
		System::initialize(&1, &Default::default(), &Default::default());
		let slot_duration = Aura::slot_duration();

		Aura::on_timestamp_set::<HandleTestReport>(5 * slot_duration, slot_duration);
		let header = System::finalize();

		// no slashing when last step was 0.
		assert_eq!(SLASH_COUNTS.lock().as_slice(), &[0, 0, 0, 0]);

		System::initialize(&2, &header.hash(), &Default::default());
		Aura::on_timestamp_set::<HandleTestReport>(8 * slot_duration, slot_duration);
		let _header = System::finalize();

		// Steps 6 and 7 were skipped.
		assert_eq!(SLASH_COUNTS.lock().as_slice(), &[0, 0, 1, 1]);
	});
}
