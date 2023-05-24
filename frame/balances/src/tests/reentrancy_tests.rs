// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Tests regarding the reentrancy functionality.

use super::*;
use frame_support::traits::tokens::{
	Fortitude::Force,
	Precision::BestEffort,
	Preservation::{Expendable, Protect},
};
use fungible::Balanced;

#[test]
fn transfer_dust_removal_tst1_should_work() {
	ExtBuilder::default()
		.existential_deposit(100)
		.dust_trap(1)
		.build_and_execute_with(|| {
			// Verification of reentrancy in dust removal
			assert_ok!(Balances::force_set_balance(RawOrigin::Root.into(), 1, 1000));
			assert_ok!(Balances::force_set_balance(RawOrigin::Root.into(), 2, 500));

			// In this transaction, account 2 free balance
			// drops below existential balance
			// and dust balance is removed from account 2
			assert_ok!(Balances::transfer_allow_death(RawOrigin::Signed(2).into(), 3, 450));

			// As expected dust balance is removed.
			assert_eq!(Balances::free_balance(&2), 0);

			// As expected beneficiary account 3
			// received the transfered fund.
			assert_eq!(Balances::free_balance(&3), 450);

			// Dust balance is deposited to account 1
			// during the process of dust removal.
			assert_eq!(Balances::free_balance(&1), 1050);

			// Verify the events
			assert_eq!(System::events().len(), 12);

			System::assert_has_event(RuntimeEvent::Balances(crate::Event::Transfer {
				from: 2,
				to: 3,
				amount: 450,
			}));
			System::assert_has_event(RuntimeEvent::Balances(crate::Event::DustLost {
				account: 2,
				amount: 50,
			}));
			System::assert_has_event(RuntimeEvent::Balances(crate::Event::Deposit {
				who: 1,
				amount: 50,
			}));
		});
}

#[test]
fn transfer_dust_removal_tst2_should_work() {
	ExtBuilder::default()
		.existential_deposit(100)
		.dust_trap(1)
		.build_and_execute_with(|| {
			// Verification of reentrancy in dust removal
			assert_ok!(Balances::force_set_balance(RawOrigin::Root.into(), 1, 1000));
			assert_ok!(Balances::force_set_balance(RawOrigin::Root.into(), 2, 500));

			// In this transaction, account 2 free balance
			// drops below existential balance
			// and dust balance is removed from account 2
			assert_ok!(Balances::transfer_allow_death(RawOrigin::Signed(2).into(), 1, 450));

			// As expected dust balance is removed.
			assert_eq!(Balances::free_balance(&2), 0);

			// Dust balance is deposited to account 1
			// during the process of dust removal.
			assert_eq!(Balances::free_balance(&1), 1500);

			// Verify the events
			assert_eq!(System::events().len(), 10);

			System::assert_has_event(RuntimeEvent::Balances(crate::Event::Transfer {
				from: 2,
				to: 1,
				amount: 450,
			}));
			System::assert_has_event(RuntimeEvent::Balances(crate::Event::DustLost {
				account: 2,
				amount: 50,
			}));
			System::assert_has_event(RuntimeEvent::Balances(crate::Event::Deposit {
				who: 1,
				amount: 50,
			}));
		});
}

#[test]
fn repatriating_reserved_balance_dust_removal_should_work() {
	ExtBuilder::default()
		.existential_deposit(100)
		.dust_trap(1)
		.build_and_execute_with(|| {
			// Verification of reentrancy in dust removal
			assert_ok!(Balances::force_set_balance(RawOrigin::Root.into(), 1, 1000));
			assert_ok!(Balances::force_set_balance(RawOrigin::Root.into(), 2, 500));

			// Reserve a value on account 2,
			// Such that free balance is lower than
			// Exestintial deposit.
			assert_ok!(Balances::transfer_allow_death(RuntimeOrigin::signed(2), 1, 450));

			// Since free balance of account 2 is lower than
			// existential deposit, dust amount is
			// removed from the account 2
			assert_eq!(Balances::reserved_balance(2), 0);
			assert_eq!(Balances::free_balance(2), 0);

			// account 1 is credited with reserved amount
			// together with dust balance during dust
			// removal.
			assert_eq!(Balances::reserved_balance(1), 0);
			assert_eq!(Balances::free_balance(1), 1500);

			// Verify the events
			assert_eq!(System::events().len(), 10);

			System::assert_has_event(RuntimeEvent::Balances(crate::Event::Transfer {
				from: 2,
				to: 1,
				amount: 450,
			}));
			System::assert_has_event(RuntimeEvent::Balances(crate::Event::DustLost {
				account: 2,
				amount: 50,
			}));
			System::assert_has_event(RuntimeEvent::Balances(crate::Event::Deposit {
				who: 1,
				amount: 50,
			}));
		});
}

#[test]
fn emit_events_with_no_existential_deposit_suicide_with_dust() {
	ExtBuilder::default().existential_deposit(2).build_and_execute_with(|| {
		assert_ok!(Balances::force_set_balance(RawOrigin::Root.into(), 1, 100));

		assert_eq!(
			events(),
			[
				RuntimeEvent::System(system::Event::NewAccount { account: 1 }),
				RuntimeEvent::Balances(crate::Event::Endowed { account: 1, free_balance: 100 }),
				RuntimeEvent::Balances(crate::Event::BalanceSet { who: 1, free: 100 }),
			]
		);

		let res = Balances::withdraw(&1, 98, BestEffort, Protect, Force);
		assert_eq!(res.unwrap().peek(), 98);

		// no events
		assert_eq!(
			events(),
			[RuntimeEvent::Balances(crate::Event::Withdraw { who: 1, amount: 98 })]
		);

		let res = Balances::withdraw(&1, 1, BestEffort, Expendable, Force);
		assert_eq!(res.unwrap().peek(), 1);

		assert_eq!(
			events(),
			[
				RuntimeEvent::System(system::Event::KilledAccount { account: 1 }),
				RuntimeEvent::Balances(crate::Event::DustLost { account: 1, amount: 1 }),
				RuntimeEvent::Balances(crate::Event::Withdraw { who: 1, amount: 1 })
			]
		);
	});
}
