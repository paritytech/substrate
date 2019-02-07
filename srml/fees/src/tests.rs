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

use super::*;
use runtime_io::with_externalities;
use mock::{Fees, System, ExtBuilder};

#[test]
fn charge_base_bytes_fee_should_work() {
	with_externalities(
		&mut ExtBuilder::default()
			.transaction_base_fee(3)
			.transaction_byte_fee(5)
			.build(),
		|| {
			System::set_extrinsic_index(0);
			assert_ok!(Fees::charge_base_bytes_fee(&0, 7));
			assert_eq!(Fees::current_transaction_fee(0), 3 + 5 * 7);

			System::set_extrinsic_index(1);
			assert_ok!(Fees::charge_base_bytes_fee(&0, 11));
			assert_eq!(Fees::current_transaction_fee(1), 3 + 5 * 11);

			System::set_extrinsic_index(3);
			assert_ok!(Fees::charge_base_bytes_fee(&0, 13));
			assert_eq!(Fees::current_transaction_fee(3), 3 + 5 * 13);
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
			System::set_extrinsic_index(0);
			assert_err!(
				Fees::charge_base_bytes_fee(&0, 2),
				"bytes fee overflow"
			);
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
			System::set_extrinsic_index(0);
			assert_err!(
				Fees::charge_base_bytes_fee(&0, 1),
				"bytes fee overflow"
			);
		}
	);
}
