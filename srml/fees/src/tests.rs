// Copyright 2019 Parity Technologies (UK) Ltd.
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
use runtime_io::with_externalities;
use system::{EventRecord, Phase};

use mock::{Fees, System, ExtBuilder, Balances};
use srml_support::{assert_ok, assert_err};

fn get_events() -> Vec<EventRecord<mock::TestEvent>> {
	System::events()
		.into_iter()
		.filter(|e| match e.event {
			mock::TestEvent::fees(_) => true,
			mock::TestEvent::balances(_) => true,
			_ => false,
		})
		.collect()
}

#[test]
fn charge_base_bytes_fee_should_work() {
	with_externalities(
		&mut ExtBuilder::default()
			.transaction_base_fee(3)
			.transaction_byte_fee(5)
			.build(),
		|| {
			System::set_extrinsic_index(0);
			let fee = 3 + 5 * 7;
			assert_ok!(Fees::charge_base_bytes_fee(&0, 7));
			assert_eq!(Balances::free_balance(&0), 1000 - fee);

			System::set_extrinsic_index(1);
			let fee2 = 3 + 5 * 11;
			assert_ok!(Fees::charge_base_bytes_fee(&0, 11));
			assert_eq!(Balances::free_balance(&0), 1000 - fee - fee2);

			assert_eq!(get_events(), vec![
				EventRecord {
					phase: Phase::ApplyExtrinsic(0),
					event: RawEvent::Charged(0, fee).into(),
				},
				EventRecord {
					phase: Phase::ApplyExtrinsic(1),
					event: RawEvent::Charged(0, fee2).into(),
				},
			]);
		}
	);
}

#[test]
fn charge_base_bytes_fee_should_not_work_if_bytes_fee_overflow() {
	// bytes fee overflows.
	with_externalities(
		&mut ExtBuilder::default()
			.transaction_base_fee(0)
			.transaction_byte_fee(u64::max_value())
			.build(),
		|| {
			assert_err!(
				Fees::charge_base_bytes_fee(&0, 2),
				"bytes fee overflow"
			);

			assert_eq!(get_events(), Vec::new());
		}
	);
}

#[test]
fn charge_base_bytes_fee_should_not_work_if_overall_fee_overflow() {
	// bytes fee doesn't overflow, but overall fee (bytes_fee + base_fee) does
	with_externalities(
		&mut ExtBuilder::default()
			.transaction_base_fee(u64::max_value())
			.transaction_byte_fee(1)
			.build(),
		|| {
			assert_err!(
				Fees::charge_base_bytes_fee(&0, 1),
				"bytes fee overflow"
			);

			assert_eq!(get_events(), Vec::new());
		}
	);
}

#[test]
fn charge_fee_should_work() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		assert_ok!(Fees::charge_fee(&0, 2));
		assert_eq!(Balances::free_balance(0), 1000 - 2);
		assert_ok!(Fees::charge_fee(&0, 3));
		assert_eq!(Balances::free_balance(0), 1000 - 2 - 3);

		assert_eq!(get_events(), vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: RawEvent::Charged(0, 2).into(),
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: RawEvent::Charged(0, 3).into(),
			},
		]);
	});
}

#[test]
fn charge_fee_without_enough_balance_should_not_work() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		assert_err!(Fees::charge_fee(&0, 1001), "account has too few funds");
		assert_err!(Fees::charge_fee(&1, 1), "account has too few funds");

		assert_eq!(get_events(), Vec::new());
	});
}

#[test]
fn refund_fee_should_work() {
	with_externalities(&mut ExtBuilder::default().build(), || {
		assert_ok!(Fees::charge_fee(&0, 5));
		assert_ok!(Fees::refund_fee(&0, 3));
		assert_eq!(Balances::free_balance(0), 1000 - 5 + 3);
		assert_ok!(Fees::refund_fee(&0, 2));
		assert_eq!(Balances::free_balance(0), 1000 - 5 + 3 + 2);

		assert_eq!(get_events(), vec![
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: RawEvent::Charged(0, 5).into(),
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: RawEvent::Refunded(0, 3).into(),
			},
			EventRecord {
				phase: Phase::ApplyExtrinsic(0),
				event: RawEvent::Refunded(0, 2).into(),
			},
		]);
	});
}
