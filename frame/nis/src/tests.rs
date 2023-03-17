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

//! Tests for NIS pallet.

use super::*;
use crate::{mock::*, Error};
use frame_support::{
	assert_noop, assert_ok,
	traits::{
		nonfungible::{Inspect, Transfer},
		Currency,
	},
};
use pallet_balances::{Error as BalancesError, Instance1};
use sp_arithmetic::Perquintill;
use sp_runtime::{Saturating, TokenError};

fn pot() -> u64 {
	Balances::free_balance(&Nis::account_id())
}

fn holdings() -> u64 {
	Nis::issuance().holdings
}

fn signed(who: u64) -> RuntimeOrigin {
	RuntimeOrigin::signed(who)
}

fn enlarge(amount: u64, max_bids: u32) {
	let summary: SummaryRecord<u64, u64> = Summary::<Test>::get();
	let increase_in_proportion_owed = Perquintill::from_rational(amount, Nis::issuance().effective);
	let target = summary.proportion_owed.saturating_add(increase_in_proportion_owed);
	Nis::process_queues(target, u32::max_value(), max_bids, &mut WeightCounter::unlimited());
}

#[test]
fn basic_setup_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);

		for q in 0..3 {
			assert!(Queues::<Test>::get(q).is_empty());
		}
		assert_eq!(
			Summary::<Test>::get(),
			SummaryRecord {
				proportion_owed: Perquintill::zero(),
				index: 0,
				last_period: 0,
				thawed: Perquintill::zero(),
				receipts_on_hold: 0,
			}
		);
	});
}

#[test]
fn place_bid_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_noop!(Nis::place_bid(signed(1), 1, 2), Error::<Test>::AmountTooSmall);
		assert_noop!(
			Nis::place_bid(signed(1), 101, 2),
			BalancesError::<Test, Instance1>::InsufficientBalance
		);
		assert_noop!(Nis::place_bid(signed(1), 10, 4), Error::<Test>::DurationTooBig);
		assert_ok!(Nis::place_bid(signed(1), 10, 2));
		assert_eq!(Balances::reserved_balance(1), 10);
		assert_eq!(Queues::<Test>::get(2), vec![Bid { amount: 10, who: 1 }]);
		assert_eq!(QueueTotals::<Test>::get(), vec![(0, 0), (1, 10), (0, 0)]);
	});
}

#[test]
fn place_bid_queuing_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 20, 2));
		assert_ok!(Nis::place_bid(signed(1), 10, 2));
		assert_ok!(Nis::place_bid(signed(1), 5, 2));
		assert_noop!(Nis::place_bid(signed(1), 5, 2), Error::<Test>::BidTooLow);
		assert_ok!(Nis::place_bid(signed(1), 15, 2));
		assert_eq!(Balances::reserved_balance(1), 45);

		assert_ok!(Nis::place_bid(signed(1), 25, 2));
		assert_eq!(Balances::reserved_balance(1), 60);
		assert_noop!(Nis::place_bid(signed(1), 10, 2), Error::<Test>::BidTooLow);
		assert_eq!(
			Queues::<Test>::get(2),
			vec![
				Bid { amount: 15, who: 1 },
				Bid { amount: 25, who: 1 },
				Bid { amount: 20, who: 1 },
			]
		);
		assert_eq!(QueueTotals::<Test>::get(), vec![(0, 0), (3, 60), (0, 0)]);
	});
}

#[test]
fn place_bid_fails_when_queue_full() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 10, 2));
		assert_ok!(Nis::place_bid(signed(2), 10, 2));
		assert_ok!(Nis::place_bid(signed(3), 10, 2));
		assert_noop!(Nis::place_bid(signed(4), 10, 2), Error::<Test>::BidTooLow);
		assert_ok!(Nis::place_bid(signed(4), 10, 3));
	});
}

#[test]
fn multiple_place_bids_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 10, 1));
		assert_ok!(Nis::place_bid(signed(1), 10, 2));
		assert_ok!(Nis::place_bid(signed(1), 10, 2));
		assert_ok!(Nis::place_bid(signed(1), 10, 3));
		assert_ok!(Nis::place_bid(signed(2), 10, 2));

		assert_eq!(Balances::reserved_balance(1), 40);
		assert_eq!(Balances::reserved_balance(2), 10);
		assert_eq!(Queues::<Test>::get(1), vec![Bid { amount: 10, who: 1 },]);
		assert_eq!(
			Queues::<Test>::get(2),
			vec![
				Bid { amount: 10, who: 2 },
				Bid { amount: 10, who: 1 },
				Bid { amount: 10, who: 1 },
			]
		);
		assert_eq!(Queues::<Test>::get(3), vec![Bid { amount: 10, who: 1 },]);
		assert_eq!(QueueTotals::<Test>::get(), vec![(1, 10), (3, 30), (1, 10)]);
	});
}

#[test]
fn retract_single_item_queue_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 10, 1));
		assert_ok!(Nis::place_bid(signed(1), 10, 2));
		assert_ok!(Nis::retract_bid(signed(1), 10, 1));

		assert_eq!(Balances::reserved_balance(1), 10);
		assert_eq!(Queues::<Test>::get(1), vec![]);
		assert_eq!(Queues::<Test>::get(2), vec![Bid { amount: 10, who: 1 }]);
		assert_eq!(QueueTotals::<Test>::get(), vec![(0, 0), (1, 10), (0, 0)]);
	});
}

#[test]
fn retract_with_other_and_duplicate_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 10, 1));
		assert_ok!(Nis::place_bid(signed(1), 10, 2));
		assert_ok!(Nis::place_bid(signed(1), 10, 2));
		assert_ok!(Nis::place_bid(signed(2), 10, 2));

		assert_ok!(Nis::retract_bid(signed(1), 10, 2));
		assert_eq!(Balances::reserved_balance(1), 20);
		assert_eq!(Balances::reserved_balance(2), 10);
		assert_eq!(Queues::<Test>::get(1), vec![Bid { amount: 10, who: 1 },]);
		assert_eq!(
			Queues::<Test>::get(2),
			vec![Bid { amount: 10, who: 2 }, Bid { amount: 10, who: 1 },]
		);
		assert_eq!(QueueTotals::<Test>::get(), vec![(1, 10), (2, 20), (0, 0)]);
	});
}

#[test]
fn retract_non_existent_item_fails() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_noop!(Nis::retract_bid(signed(1), 10, 1), Error::<Test>::UnknownBid);
		assert_ok!(Nis::place_bid(signed(1), 10, 1));
		assert_noop!(Nis::retract_bid(signed(1), 20, 1), Error::<Test>::UnknownBid);
		assert_noop!(Nis::retract_bid(signed(1), 10, 2), Error::<Test>::UnknownBid);
		assert_noop!(Nis::retract_bid(signed(2), 10, 1), Error::<Test>::UnknownBid);
	});
}

#[test]
fn basic_enlarge_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 40, 1));
		assert_ok!(Nis::place_bid(signed(2), 40, 2));
		enlarge(40, 2);

		// Takes 2/2, then stopped because it reaches its max amount
		assert_eq!(Balances::reserved_balance(1), 40);
		assert_eq!(Balances::reserved_balance(2), 40);
		assert_eq!(holdings(), 40);

		assert_eq!(Queues::<Test>::get(1), vec![Bid { amount: 40, who: 1 }]);
		assert_eq!(Queues::<Test>::get(2), vec![]);
		assert_eq!(QueueTotals::<Test>::get(), vec![(1, 40), (0, 0), (0, 0)]);

		assert_eq!(
			Summary::<Test>::get(),
			SummaryRecord {
				proportion_owed: Perquintill::from_percent(10),
				index: 1,
				last_period: 0,
				thawed: Perquintill::zero(),
				receipts_on_hold: 40,
			}
		);
		assert_eq!(
			Receipts::<Test>::get(0).unwrap(),
			ReceiptRecord {
				proportion: Perquintill::from_percent(10),
				owner: Some((2, 40)),
				expiry: 7
			}
		);
	});
}

#[test]
fn enlarge_respects_bids_limit() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 40, 1));
		assert_ok!(Nis::place_bid(signed(2), 40, 2));
		assert_ok!(Nis::place_bid(signed(3), 40, 2));
		assert_ok!(Nis::place_bid(signed(4), 40, 3));
		enlarge(100, 2);

		// Should have taken 4/3 and 2/2, then stopped because it's only allowed 2.
		assert_eq!(Queues::<Test>::get(1), vec![Bid { amount: 40, who: 1 }]);
		assert_eq!(Queues::<Test>::get(2), vec![Bid { amount: 40, who: 3 }]);
		assert_eq!(Queues::<Test>::get(3), vec![]);
		assert_eq!(QueueTotals::<Test>::get(), vec![(1, 40), (1, 40), (0, 0)]);

		assert_eq!(
			Receipts::<Test>::get(0).unwrap(),
			ReceiptRecord {
				proportion: Perquintill::from_percent(10),
				owner: Some((4, 40)),
				expiry: 10
			}
		);
		assert_eq!(
			Receipts::<Test>::get(1).unwrap(),
			ReceiptRecord {
				proportion: Perquintill::from_percent(10),
				owner: Some((2, 40)),
				expiry: 7
			}
		);
		assert_eq!(
			Summary::<Test>::get(),
			SummaryRecord {
				proportion_owed: Perquintill::from_percent(20),
				index: 2,
				last_period: 0,
				thawed: Perquintill::zero(),
				receipts_on_hold: 80,
			}
		);
	});
}

#[test]
fn enlarge_respects_amount_limit_and_will_split() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 80, 1));
		enlarge(40, 2);

		// Takes 2/2, then stopped because it reaches its max amount
		assert_eq!(Queues::<Test>::get(1), vec![Bid { amount: 40, who: 1 }]);
		assert_eq!(QueueTotals::<Test>::get(), vec![(1, 40), (0, 0), (0, 0)]);

		assert_eq!(
			Receipts::<Test>::get(0).unwrap(),
			ReceiptRecord {
				proportion: Perquintill::from_percent(10),
				owner: Some((1, 40)),
				expiry: 4
			}
		);
		assert_eq!(
			Summary::<Test>::get(),
			SummaryRecord {
				proportion_owed: Perquintill::from_percent(10),
				index: 1,
				last_period: 0,
				thawed: Perquintill::zero(),
				receipts_on_hold: 40,
			}
		);
	});
}

#[test]
fn basic_thaw_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 40, 1));
		assert_eq!(Nis::issuance().effective, 400);
		assert_eq!(Balances::free_balance(1), 60);
		assert_eq!(Balances::reserved_balance(1), 40);
		assert_eq!(holdings(), 0);

		enlarge(40, 1);
		assert_eq!(Nis::issuance().effective, 400);
		assert_eq!(Balances::free_balance(1), 60);
		assert_eq!(Balances::reserved_balance(1), 40);
		assert_eq!(holdings(), 40);

		run_to_block(3);
		assert_noop!(Nis::thaw_private(signed(1), 0, None), Error::<Test>::NotExpired);
		run_to_block(4);
		assert_noop!(Nis::thaw_private(signed(1), 1, None), Error::<Test>::UnknownReceipt);
		assert_noop!(Nis::thaw_private(signed(2), 0, None), Error::<Test>::NotOwner);

		assert_ok!(Nis::thaw_private(signed(1), 0, None));
		assert_eq!(NisBalances::free_balance(1), 0);
		assert_eq!(Nis::typed_attribute::<_, Perquintill>(&0, b"proportion"), None);
		assert_eq!(Nis::issuance().effective, 400);
		assert_eq!(Balances::free_balance(1), 100);
		assert_eq!(pot(), 0);
		assert_eq!(
			Summary::<Test>::get(),
			SummaryRecord {
				proportion_owed: Perquintill::zero(),
				index: 1,
				last_period: 0,
				thawed: Perquintill::from_percent(10),
				receipts_on_hold: 0,
			}
		);
		assert_eq!(Receipts::<Test>::get(0), None);
	});
}

#[test]
fn partial_thaw_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 80, 1));
		enlarge(80, 1);
		assert_eq!(holdings(), 80);

		run_to_block(4);
		let prop = Perquintill::from_rational(4_100_000, 21_000_000u64);
		assert_noop!(Nis::thaw_private(signed(1), 0, Some(prop)), Error::<Test>::MakesDust);
		let prop = Perquintill::from_rational(1_050_000, 21_000_000u64);
		assert_ok!(Nis::thaw_private(signed(1), 0, Some(prop)));

		assert_eq!(
			Nis::typed_attribute::<_, Perquintill>(&0, b"proportion"),
			Some(Perquintill::from_rational(3_150_000u64, 21_000_000u64)),
		);

		assert_eq!(Nis::issuance().effective, 400);
		assert_eq!(Balances::free_balance(1), 40);
		assert_eq!(holdings(), 60);

		assert_ok!(Nis::thaw_private(signed(1), 0, None));

		assert_eq!(Nis::issuance().effective, 400);
		assert_eq!(Balances::free_balance(1), 100);
		assert_eq!(pot(), 0);

		assert_eq!(
			Summary::<Test>::get(),
			SummaryRecord {
				proportion_owed: Perquintill::zero(),
				index: 1,
				last_period: 0,
				thawed: Perquintill::from_percent(20),
				receipts_on_hold: 0,
			}
		);
		assert_eq!(Receipts::<Test>::get(0), None);
	});
}

#[test]
fn thaw_respects_transfers() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 40, 1));
		enlarge(40, 1);
		run_to_block(4);

		assert_eq!(Nis::owner(&0), Some(1));
		assert_eq!(Balances::reserved_balance(&1), 40);
		assert_eq!(Balances::reserved_balance(&2), 0);
		assert_ok!(Nis::transfer(&0, &2));
		assert_eq!(Balances::reserved_balance(&1), 0);
		assert_eq!(Balances::reserved_balance(&2), 40);

		// Transfering the receipt...
		assert_noop!(Nis::thaw_private(signed(1), 0, None), Error::<Test>::NotOwner);

		// ...and thawing is possible.
		assert_ok!(Nis::thaw_private(signed(2), 0, None));

		assert_eq!(Balances::total_balance(&2), 140);
		assert_eq!(Balances::total_balance(&1), 60);
	});
}

#[test]
fn communify_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 40, 1));
		enlarge(40, 1);
		run_to_block(4);

		assert_eq!(Nis::owner(&0), Some(1));
		assert_eq!(Balances::reserved_balance(&1), 40);
		assert_eq!(pot(), 0);
		assert_eq!(NisBalances::free_balance(&1), 0);
		assert_ok!(Nis::communify(signed(1), 0));
		assert_eq!(Nis::owner(&0), None);
		assert_eq!(Balances::reserved_balance(&1), 0);
		assert_eq!(pot(), 40);
		// We now have fungibles.
		assert_eq!(NisBalances::free_balance(&1), 2_100_000);

		// Can't transfer the NFT or thaw it as a private.
		assert_noop!(Nis::thaw_private(signed(1), 0, None), Error::<Test>::AlreadyCommunal);
		assert_noop!(Nis::transfer(&0, &2), Error::<Test>::AlreadyCommunal);
		// Communal thawing would be possible, except it's the wrong receipt.
		assert_noop!(Nis::thaw_communal(signed(1), 1), Error::<Test>::UnknownReceipt);

		// Transfer some of the fungibles away.
		assert_ok!(NisBalances::transfer(signed(1), 2, 100_000));
		assert_eq!(NisBalances::free_balance(&1), 2_000_000);
		assert_eq!(NisBalances::free_balance(&2), 100_000);

		// Communal thawing with the correct index is not possible now.
		assert_noop!(Nis::thaw_communal(signed(1), 0), TokenError::NoFunds);
		assert_noop!(Nis::thaw_communal(signed(2), 0), TokenError::NoFunds);

		// Transfer the rest to 2...
		assert_ok!(NisBalances::transfer(signed(1), 2, 2_000_000));
		assert_eq!(NisBalances::free_balance(&1), 0);
		assert_eq!(NisBalances::free_balance(&2), 2_100_000);

		// ...and thawing becomes possible.
		assert_ok!(Nis::thaw_communal(signed(2), 0));
		assert_eq!(NisBalances::free_balance(&1), 0);
		assert_eq!(NisBalances::free_balance(&2), 0);
		assert_eq!(pot(), 0);
		assert_eq!(Balances::total_balance(&1), 60);
		assert_eq!(Balances::total_balance(&2), 140);

		assert_noop!(Nis::thaw_communal(signed(2), 0), Error::<Test>::UnknownReceipt);
	});
}

#[test]
fn privatize_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 40, 1));
		enlarge(40, 1);
		run_to_block(4);
		assert_noop!(Nis::privatize(signed(2), 0), Error::<Test>::AlreadyPrivate);
		assert_ok!(Nis::communify(signed(1), 0));

		// Transfer the fungibles to #2
		assert_ok!(NisBalances::transfer(signed(1), 2, 2_100_000));
		assert_noop!(Nis::privatize(signed(1), 0), TokenError::NoFunds);

		// Privatize
		assert_ok!(Nis::privatize(signed(2), 0));
		assert_noop!(Nis::privatize(signed(2), 0), Error::<Test>::AlreadyPrivate);
		assert_eq!(NisBalances::free_balance(&2), 0);
		assert_eq!(Nis::owner(&0), Some(2));
		assert_eq!(Balances::reserved_balance(&2), 40);
		assert_eq!(pot(), 0);
	});
}

#[test]
fn privatize_and_thaw_with_another_receipt_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 40, 1));
		assert_ok!(Nis::place_bid(signed(2), 40, 1));
		enlarge(80, 2);
		run_to_block(4);

		assert_ok!(Nis::communify(signed(1), 0));
		assert_ok!(Nis::communify(signed(2), 1));

		// Transfer half of fungibles to #3 from each of #1 and #2, and the other half from #2 to #4
		assert_ok!(NisBalances::transfer(signed(1), 3, 1_050_000));
		assert_ok!(NisBalances::transfer(signed(2), 3, 1_050_000));
		assert_ok!(NisBalances::transfer(signed(2), 4, 1_050_000));

		// #3 privatizes, partially thaws, then re-communifies with #0, then transfers the fungibles
		// to #2
		assert_ok!(Nis::privatize(signed(3), 0));
		assert_ok!(Nis::thaw_private(signed(3), 0, Some(Perquintill::from_percent(5))));
		assert_ok!(Nis::communify(signed(3), 0));
		assert_ok!(NisBalances::transfer(signed(3), 1, 1_050_000));

		// #1 now has enough to thaw using receipt 1
		assert_ok!(Nis::thaw_communal(signed(1), 1));

		// #4 now has enough to thaw using receipt 0
		assert_ok!(Nis::thaw_communal(signed(4), 0));
	});
}

#[test]
fn communal_thaw_when_issuance_higher_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 100, 1));
		enlarge(100, 1);

		assert_ok!(Nis::communify(signed(1), 0));

		assert_eq!(NisBalances::free_balance(1), 5_250_000); // (25% of 21m)

		// Everybody else's balances goes up by 50%
		Balances::make_free_balance_be(&2, 150);
		Balances::make_free_balance_be(&3, 150);
		Balances::make_free_balance_be(&4, 150);

		run_to_block(4);

		// Unfunded initially...
		assert_noop!(Nis::thaw_communal(signed(1), 0), Error::<Test>::Unfunded);
		// ...so we fund.
		assert_ok!(Nis::fund_deficit(signed(1)));

		// Transfer counterparts away...
		assert_ok!(NisBalances::transfer(signed(1), 2, 250_000));
		// ...and it's not thawable.
		assert_noop!(Nis::thaw_communal(signed(1), 0), TokenError::NoFunds);

		// Transfer counterparts back...
		assert_ok!(NisBalances::transfer(signed(2), 1, 250_000));
		// ...and it is.
		assert_ok!(Nis::thaw_communal(signed(1), 0));

		assert_eq!(Balances::free_balance(1), 150);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn private_thaw_when_issuance_higher_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 100, 1));
		enlarge(100, 1);

		// Everybody else's balances goes up by 50%
		Balances::make_free_balance_be(&2, 150);
		Balances::make_free_balance_be(&3, 150);
		Balances::make_free_balance_be(&4, 150);

		run_to_block(4);

		// Unfunded initially...
		assert_noop!(Nis::thaw_private(signed(1), 0, None), Error::<Test>::Unfunded);
		// ...so we fund.
		assert_ok!(Nis::fund_deficit(signed(1)));

		assert_ok!(Nis::thaw_private(signed(1), 0, None));

		assert_eq!(Balances::free_balance(1), 150);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn thaw_with_ignored_issuance_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		// Give account zero some balance.
		Balances::make_free_balance_be(&0, 200);

		assert_ok!(Nis::place_bid(signed(1), 100, 1));
		enlarge(100, 1);

		// Account zero transfers 50 into everyone else's accounts.
		assert_ok!(Balances::transfer(signed(0), 2, 50));
		assert_ok!(Balances::transfer(signed(0), 3, 50));
		assert_ok!(Balances::transfer(signed(0), 4, 50));

		run_to_block(4);
		// Unfunded initially...
		assert_noop!(Nis::thaw_private(signed(1), 0, None), Error::<Test>::Unfunded);
		// ...so we fund...
		assert_ok!(Nis::fund_deficit(signed(1)));
		// ...and then it's ok.
		assert_ok!(Nis::thaw_private(signed(1), 0, None));

		// Account zero changes have been ignored.
		assert_eq!(Balances::free_balance(1), 150);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn thaw_when_issuance_lower_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 100, 1));
		enlarge(100, 1);

		// Everybody else's balances goes down by 25%
		Balances::make_free_balance_be(&2, 75);
		Balances::make_free_balance_be(&3, 75);
		Balances::make_free_balance_be(&4, 75);

		run_to_block(4);
		assert_ok!(Nis::thaw_private(signed(1), 0, None));

		assert_eq!(Balances::free_balance(1), 75);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn multiple_thaws_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 40, 1));
		assert_ok!(Nis::place_bid(signed(1), 60, 1));
		assert_ok!(Nis::place_bid(signed(2), 50, 1));
		enlarge(200, 3);

		// Double everyone's free balances.
		Balances::make_free_balance_be(&2, 100);
		Balances::make_free_balance_be(&3, 200);
		Balances::make_free_balance_be(&4, 200);
		assert_ok!(Nis::fund_deficit(signed(1)));

		run_to_block(4);
		assert_ok!(Nis::thaw_private(signed(1), 0, None));
		assert_ok!(Nis::thaw_private(signed(1), 1, None));
		assert_noop!(Nis::thaw_private(signed(2), 2, None), Error::<Test>::Throttled);
		run_to_block(5);
		assert_ok!(Nis::thaw_private(signed(2), 2, None));

		assert_eq!(Balances::free_balance(1), 200);
		assert_eq!(Balances::free_balance(2), 200);
	});
}

#[test]
fn multiple_thaws_works_in_alternative_thaw_order() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Nis::place_bid(signed(1), 40, 1));
		assert_ok!(Nis::place_bid(signed(1), 60, 1));
		assert_ok!(Nis::place_bid(signed(2), 50, 1));
		enlarge(200, 3);

		// Double everyone's free balances.
		Balances::make_free_balance_be(&2, 100);
		Balances::make_free_balance_be(&3, 200);
		Balances::make_free_balance_be(&4, 200);
		assert_ok!(Nis::fund_deficit(signed(1)));

		run_to_block(4);
		assert_ok!(Nis::thaw_private(signed(2), 2, None));
		assert_noop!(Nis::thaw_private(signed(1), 1, None), Error::<Test>::Throttled);
		assert_ok!(Nis::thaw_private(signed(1), 0, None));

		run_to_block(5);
		assert_ok!(Nis::thaw_private(signed(1), 1, None));

		assert_eq!(Balances::free_balance(1), 200);
		assert_eq!(Balances::free_balance(2), 200);
	});
}

#[test]
fn enlargement_to_target_works() {
	new_test_ext().execute_with(|| {
		run_to_block(2);
		let w = <() as WeightInfo>::process_queues() +
			<() as WeightInfo>::process_queue() +
			(<() as WeightInfo>::process_bid() * 2);
		super::mock::MaxIntakeWeight::set(w);
		assert_ok!(Nis::place_bid(signed(1), 40, 1));
		assert_ok!(Nis::place_bid(signed(1), 40, 2));
		assert_ok!(Nis::place_bid(signed(2), 40, 2));
		assert_ok!(Nis::place_bid(signed(2), 40, 3));
		assert_ok!(Nis::place_bid(signed(3), 40, 3));
		Target::set(Perquintill::from_percent(40));

		run_to_block(3);
		assert_eq!(Queues::<Test>::get(1), vec![Bid { amount: 40, who: 1 },]);
		assert_eq!(
			Queues::<Test>::get(2),
			vec![Bid { amount: 40, who: 2 }, Bid { amount: 40, who: 1 },]
		);
		assert_eq!(
			Queues::<Test>::get(3),
			vec![Bid { amount: 40, who: 3 }, Bid { amount: 40, who: 2 },]
		);
		assert_eq!(QueueTotals::<Test>::get(), vec![(1, 40), (2, 80), (2, 80)]);

		run_to_block(4);
		// Two new items should have been issued to 2 & 3 for 40 each & duration of 3.
		assert_eq!(
			Receipts::<Test>::get(0).unwrap(),
			ReceiptRecord {
				proportion: Perquintill::from_percent(10),
				owner: Some((2, 40)),
				expiry: 13
			}
		);
		assert_eq!(
			Receipts::<Test>::get(1).unwrap(),
			ReceiptRecord {
				proportion: Perquintill::from_percent(10),
				owner: Some((3, 40)),
				expiry: 13
			}
		);
		assert_eq!(
			Summary::<Test>::get(),
			SummaryRecord {
				proportion_owed: Perquintill::from_percent(20),
				index: 2,
				last_period: 0,
				thawed: Perquintill::zero(),
				receipts_on_hold: 80,
			}
		);

		run_to_block(5);
		// No change
		assert_eq!(
			Summary::<Test>::get(),
			SummaryRecord {
				proportion_owed: Perquintill::from_percent(20),
				index: 2,
				last_period: 0,
				thawed: Perquintill::zero(),
				receipts_on_hold: 80,
			}
		);

		run_to_block(6);
		// Two new items should have been issued to 1 & 2 for 40 each & duration of 2.
		assert_eq!(
			Receipts::<Test>::get(2).unwrap(),
			ReceiptRecord {
				proportion: Perquintill::from_percent(10),
				owner: Some((1, 40)),
				expiry: 12
			}
		);
		assert_eq!(
			Receipts::<Test>::get(3).unwrap(),
			ReceiptRecord {
				proportion: Perquintill::from_percent(10),
				owner: Some((2, 40)),
				expiry: 12
			}
		);
		assert_eq!(
			Summary::<Test>::get(),
			SummaryRecord {
				proportion_owed: Perquintill::from_percent(40),
				index: 4,
				last_period: 0,
				thawed: Perquintill::zero(),
				receipts_on_hold: 160,
			}
		);

		run_to_block(8);
		// No change now.
		assert_eq!(
			Summary::<Test>::get(),
			SummaryRecord {
				proportion_owed: Perquintill::from_percent(40),
				index: 4,
				last_period: 0,
				thawed: Perquintill::zero(),
				receipts_on_hold: 160,
			}
		);

		// Set target a bit higher to use up the remaining bid.
		Target::set(Perquintill::from_percent(60));
		run_to_block(10);

		// One new item should have been issued to 1 for 40 each & duration of 2.
		assert_eq!(
			Receipts::<Test>::get(4).unwrap(),
			ReceiptRecord {
				proportion: Perquintill::from_percent(10),
				owner: Some((1, 40)),
				expiry: 13
			}
		);

		assert_eq!(
			Summary::<Test>::get(),
			SummaryRecord {
				proportion_owed: Perquintill::from_percent(50),
				index: 5,
				last_period: 0,
				thawed: Perquintill::zero(),
				receipts_on_hold: 200,
			}
		);
	});
}
