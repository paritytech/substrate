// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

use super::*;
use frame_support::{assert_err, assert_ok};
use mock::{active_era, start_session, Balances, ExtBuilder, RootOffences, RuntimeOrigin, System};

#[test]
fn create_offence_fails_given_signed_origin() {
	use sp_runtime::traits::BadOrigin;
	ExtBuilder::default().build_and_execute(|| {
		let offenders = (&[]).to_vec();
		assert_err!(RootOffences::create_offence(RuntimeOrigin::signed(1), offenders), BadOrigin);
	})
}

#[test]
fn create_offence_works_given_root_origin() {
	ExtBuilder::default().build_and_execute(|| {
		start_session(1);

		assert_eq!(active_era(), 0);

		assert_eq!(Balances::free_balance(11), 1000);

		let offenders = [(11, Perbill::from_percent(50))].to_vec();
		assert_ok!(RootOffences::create_offence(RuntimeOrigin::root(), offenders.clone()));

		System::assert_last_event(Event::OffenceCreated { offenders }.into());
		// the slash should be applied right away.
		assert_eq!(Balances::free_balance(11), 500);

		// the other validator should keep their balance, because we only created
		// an offences for the first validator.
		assert_eq!(Balances::free_balance(21), 1000);
	})
}

#[test]
fn create_offence_wont_slash_non_active_validators() {
	ExtBuilder::default().build_and_execute(|| {
		start_session(1);

		assert_eq!(active_era(), 0);

		// 31 is not an active validator.
		assert_eq!(Balances::free_balance(31), 500);

		let offenders = [(31, Perbill::from_percent(20)), (11, Perbill::from_percent(20))].to_vec();
		assert_ok!(RootOffences::create_offence(RuntimeOrigin::root(), offenders.clone()));

		System::assert_last_event(Event::OffenceCreated { offenders }.into());

		// so 31 didn't get slashed.
		assert_eq!(Balances::free_balance(31), 500);

		// but 11 is an active validator so they got slashed.
		assert_eq!(Balances::free_balance(11), 800);
	})
}

#[test]
fn create_offence_wont_slash_idle() {
	ExtBuilder::default().build_and_execute(|| {
		start_session(1);

		assert_eq!(active_era(), 0);

		// 41 is idle.
		assert_eq!(Balances::free_balance(41), 1000);

		let offenders = [(41, Perbill::from_percent(50))].to_vec();
		assert_ok!(RootOffences::create_offence(RuntimeOrigin::root(), offenders.clone()));

		System::assert_last_event(Event::OffenceCreated { offenders }.into());

		// 41 didn't get slashed.
		assert_eq!(Balances::free_balance(41), 1000);
	})
}
