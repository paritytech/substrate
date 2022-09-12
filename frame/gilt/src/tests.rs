// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Tests for Gilt pallet.

use super::*;
use crate::{Error, mock::*};
use frame_support::{assert_ok, assert_noop, dispatch::DispatchError, traits::Currency};
use sp_arithmetic::Perquintill;
use pallet_balances::Error as BalancesError;

#[test]
fn basic_setup_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);

		for q in 0..3 {
			assert!(Queues::<Test>::get(q).is_empty());
		}
		assert_eq!(ActiveTotal::<Test>::get(), ActiveGiltsTotal {
			frozen: 0,
			proportion: Perquintill::zero(),
			index: 0,
			target: Perquintill::zero(),
		});
		assert_eq!(QueueTotals::<Test>::get(), vec![(0, 0); 3]);
	});
}

#[test]
fn set_target_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		let e = DispatchError::BadOrigin;
		assert_noop!(Gilt::set_target(Origin::signed(2), Perquintill::from_percent(50)), e);
		assert_ok!(Gilt::set_target(Origin::signed(1), Perquintill::from_percent(50)));

		assert_eq!(ActiveTotal::<Test>::get(), ActiveGiltsTotal {
			frozen: 0,
			proportion: Perquintill::zero(),
			index: 0,
			target: Perquintill::from_percent(50),
		});
	});
}

#[test]
fn place_bid_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_noop!(Gilt::place_bid(Origin::signed(1), 1, 2), Error::<Test>::AmountTooSmall);
		assert_noop!(Gilt::place_bid(Origin::signed(1), 101, 2), BalancesError::<Test>::InsufficientBalance);
		assert_noop!(Gilt::place_bid(Origin::signed(1), 10, 4), Error::<Test>::DurationTooBig);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 10, 2));
		assert_eq!(Balances::reserved_balance(1), 10);
		assert_eq!(Queues::<Test>::get(2), vec![GiltBid { amount: 10, who: 1 }]);
		assert_eq!(QueueTotals::<Test>::get(), vec![(0, 0), (1, 10), (0, 0)]);
	});
}

#[test]
fn place_bid_queuing_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 20, 2));
		assert_ok!(Gilt::place_bid(Origin::signed(1), 10, 2));
		assert_ok!(Gilt::place_bid(Origin::signed(1), 5, 2));
		assert_noop!(Gilt::place_bid(Origin::signed(1), 5, 2), Error::<Test>::BidTooLow);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 15, 2));
		assert_eq!(Balances::reserved_balance(1), 45);

		assert_ok!(Gilt::place_bid(Origin::signed(1), 25, 2));
		assert_eq!(Balances::reserved_balance(1), 60);
		assert_noop!(Gilt::place_bid(Origin::signed(1), 10, 2), Error::<Test>::BidTooLow);
		assert_eq!(Queues::<Test>::get(2), vec![
			GiltBid { amount: 15, who: 1 },
			GiltBid { amount: 25, who: 1 },
			GiltBid { amount: 20, who: 1 },
		]);
		assert_eq!(QueueTotals::<Test>::get(), vec![(0, 0), (3, 60), (0, 0)]);
	});
}

#[test]
fn place_bid_fails_when_queue_full() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 10, 2));
		assert_ok!(Gilt::place_bid(Origin::signed(2), 10, 2));
		assert_ok!(Gilt::place_bid(Origin::signed(3), 10, 2));
		assert_noop!(Gilt::place_bid(Origin::signed(4), 10, 2), Error::<Test>::BidTooLow);
		assert_ok!(Gilt::place_bid(Origin::signed(4), 10, 3));
	});
}

#[test]
fn multiple_place_bids_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 10, 1));
		assert_ok!(Gilt::place_bid(Origin::signed(1), 10, 2));
		assert_ok!(Gilt::place_bid(Origin::signed(1), 10, 2));
		assert_ok!(Gilt::place_bid(Origin::signed(1), 10, 3));
		assert_ok!(Gilt::place_bid(Origin::signed(2), 10, 2));

		assert_eq!(Balances::reserved_balance(1), 40);
		assert_eq!(Balances::reserved_balance(2), 10);
		assert_eq!(Queues::<Test>::get(1), vec![
			GiltBid { amount: 10, who: 1 },
		]);
		assert_eq!(Queues::<Test>::get(2), vec![
			GiltBid { amount: 10, who: 2 },
			GiltBid { amount: 10, who: 1 },
			GiltBid { amount: 10, who: 1 },
		]);
		assert_eq!(Queues::<Test>::get(3), vec![
			GiltBid { amount: 10, who: 1 },
		]);
		assert_eq!(QueueTotals::<Test>::get(), vec![(1, 10), (3, 30), (1, 10)]);
	});
}

#[test]
fn retract_single_item_queue_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 10, 1));
		assert_ok!(Gilt::place_bid(Origin::signed(1), 10, 2));
		assert_ok!(Gilt::retract_bid(Origin::signed(1), 10, 1));

		assert_eq!(Balances::reserved_balance(1), 10);
		assert_eq!(Queues::<Test>::get(1), vec![]);
		assert_eq!(Queues::<Test>::get(2), vec![ GiltBid { amount: 10, who: 1 } ]);
		assert_eq!(QueueTotals::<Test>::get(), vec![(0, 0), (1, 10), (0, 0)]);
	});
}

#[test]
fn retract_with_other_and_duplicate_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 10, 1));
		assert_ok!(Gilt::place_bid(Origin::signed(1), 10, 2));
		assert_ok!(Gilt::place_bid(Origin::signed(1), 10, 2));
		assert_ok!(Gilt::place_bid(Origin::signed(2), 10, 2));

		assert_ok!(Gilt::retract_bid(Origin::signed(1), 10, 2));
		assert_eq!(Balances::reserved_balance(1), 20);
		assert_eq!(Balances::reserved_balance(2), 10);
		assert_eq!(Queues::<Test>::get(1), vec![
			GiltBid { amount: 10, who: 1 },
		]);
		assert_eq!(Queues::<Test>::get(2), vec![
			GiltBid { amount: 10, who: 2 },
			GiltBid { amount: 10, who: 1 },
		]);
		assert_eq!(QueueTotals::<Test>::get(), vec![(1, 10), (2, 20), (0, 0)]);
	});
}

#[test]
fn retract_non_existent_item_fails() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_noop!(Gilt::retract_bid(Origin::signed(1), 10, 1), Error::<Test>::NotFound);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 10, 1));
		assert_noop!(Gilt::retract_bid(Origin::signed(1), 20, 1), Error::<Test>::NotFound);
		assert_noop!(Gilt::retract_bid(Origin::signed(1), 10, 2), Error::<Test>::NotFound);
		assert_noop!(Gilt::retract_bid(Origin::signed(2), 10, 1), Error::<Test>::NotFound);
	});
}

#[test]
fn basic_enlarge_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 40, 1));
		assert_ok!(Gilt::place_bid(Origin::signed(2), 40, 2));
		Gilt::enlarge(40, 2);

		// Takes 2/2, then stopped because it reaches its max amount
		assert_eq!(Balances::reserved_balance(1), 40);
		assert_eq!(Balances::reserved_balance(2), 40);
		assert_eq!(Queues::<Test>::get(1), vec![ GiltBid { amount: 40, who: 1 } ]);
		assert_eq!(Queues::<Test>::get(2), vec![]);
		assert_eq!(QueueTotals::<Test>::get(), vec![(1, 40), (0, 0), (0, 0)]);

		assert_eq!(ActiveTotal::<Test>::get(), ActiveGiltsTotal {
			frozen: 40,
			proportion: Perquintill::from_percent(10),
			index: 1,
			target: Perquintill::zero(),
		});
		assert_eq!(Active::<Test>::get(0).unwrap(), ActiveGilt {
			proportion: Perquintill::from_percent(10),
			amount: 40,
			who: 2,
			expiry: 7,
		});
	});
}

#[test]
fn enlarge_respects_bids_limit() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 40, 1));
		assert_ok!(Gilt::place_bid(Origin::signed(2), 40, 2));
		assert_ok!(Gilt::place_bid(Origin::signed(3), 40, 2));
		assert_ok!(Gilt::place_bid(Origin::signed(4), 40, 3));
		Gilt::enlarge(100, 2);

		// Should have taken 4/3 and 2/2, then stopped because it's only allowed 2.
		assert_eq!(Queues::<Test>::get(1), vec![ GiltBid { amount: 40, who: 1 } ]);
		assert_eq!(Queues::<Test>::get(2), vec![ GiltBid { amount: 40, who: 3 } ]);
		assert_eq!(Queues::<Test>::get(3), vec![]);
		assert_eq!(QueueTotals::<Test>::get(), vec![(1, 40), (1, 40), (0, 0)]);

		assert_eq!(Active::<Test>::get(0).unwrap(), ActiveGilt {
			proportion: Perquintill::from_percent(10),
			amount: 40,
			who: 4,
			expiry: 10,
		});
		assert_eq!(Active::<Test>::get(1).unwrap(), ActiveGilt {
			proportion: Perquintill::from_percent(10),
			amount: 40,
			who: 2,
			expiry: 7,
		});
		assert_eq!(ActiveTotal::<Test>::get(), ActiveGiltsTotal {
			frozen: 80,
			proportion: Perquintill::from_percent(20),
			index: 2,
			target: Perquintill::zero(),
		});
	});
}

#[test]
fn enlarge_respects_amount_limit_and_will_split() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 80, 1));
		Gilt::enlarge(40, 2);

		// Takes 2/2, then stopped because it reaches its max amount
		assert_eq!(Queues::<Test>::get(1), vec![ GiltBid { amount: 40, who: 1 } ]);
		assert_eq!(QueueTotals::<Test>::get(), vec![(1, 40), (0, 0), (0, 0)]);

		assert_eq!(Active::<Test>::get(0).unwrap(), ActiveGilt {
			proportion: Perquintill::from_percent(10),
			amount: 40,
			who: 1,
			expiry: 4,
		});
		assert_eq!(ActiveTotal::<Test>::get(), ActiveGiltsTotal {
			frozen: 40,
			proportion: Perquintill::from_percent(10),
			index: 1,
			target: Perquintill::zero(),
		});
	});
}

#[test]
fn basic_thaw_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 40, 1));
		Gilt::enlarge(40, 1);
		run_to_block(3);
		assert_noop!(Gilt::thaw(Origin::signed(1), 0), Error::<Test>::NotExpired);
		run_to_block(4);
		assert_noop!(Gilt::thaw(Origin::signed(1), 1), Error::<Test>::Unknown);
		assert_noop!(Gilt::thaw(Origin::signed(2), 0), Error::<Test>::NotOwner);
		assert_ok!(Gilt::thaw(Origin::signed(1), 0));

		assert_eq!(ActiveTotal::<Test>::get(), ActiveGiltsTotal {
			frozen: 0,
			proportion: Perquintill::zero(),
			index: 1,
			target: Perquintill::zero(),
		});
		assert_eq!(Active::<Test>::get(0), None);
		assert_eq!(Balances::free_balance(1), 100);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn thaw_when_issuance_higher_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 100, 1));
		Gilt::enlarge(100, 1);

		// Everybody else's balances goes up by 50%
		Balances::make_free_balance_be(&2, 150);
		Balances::make_free_balance_be(&3, 150);
		Balances::make_free_balance_be(&4, 150);

		run_to_block(4);
		assert_ok!(Gilt::thaw(Origin::signed(1), 0));

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

		assert_ok!(Gilt::place_bid(Origin::signed(1), 100, 1));
		Gilt::enlarge(100, 1);

		// Account zero transfers 50 into everyone else's accounts.
		assert_ok!(Balances::transfer(Origin::signed(0), 2, 50));
		assert_ok!(Balances::transfer(Origin::signed(0), 3, 50));
		assert_ok!(Balances::transfer(Origin::signed(0), 4, 50));

		run_to_block(4);
		assert_ok!(Gilt::thaw(Origin::signed(1), 0));

		// Account zero changes have been ignored.
		assert_eq!(Balances::free_balance(1), 150);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn thaw_when_issuance_lower_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 100, 1));
		Gilt::enlarge(100, 1);

		// Everybody else's balances goes down by 25%
		Balances::make_free_balance_be(&2, 75);
		Balances::make_free_balance_be(&3, 75);
		Balances::make_free_balance_be(&4, 75);

		run_to_block(4);
		assert_ok!(Gilt::thaw(Origin::signed(1), 0));

		assert_eq!(Balances::free_balance(1), 75);
		assert_eq!(Balances::reserved_balance(1), 0);
	});
}

#[test]
fn multiple_thaws_works() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 40, 1));
		assert_ok!(Gilt::place_bid(Origin::signed(1), 60, 1));
		assert_ok!(Gilt::place_bid(Origin::signed(2), 50, 1));
		Gilt::enlarge(200, 3);

		// Double everyone's free balances.
		Balances::make_free_balance_be(&2, 100);
		Balances::make_free_balance_be(&3, 200);
		Balances::make_free_balance_be(&4, 200);

		run_to_block(4);
		assert_ok!(Gilt::thaw(Origin::signed(1), 0));
		assert_ok!(Gilt::thaw(Origin::signed(1), 1));
		assert_ok!(Gilt::thaw(Origin::signed(2), 2));

		assert_eq!(Balances::free_balance(1), 200);
		assert_eq!(Balances::free_balance(2), 200);
	});
}

#[test]
fn multiple_thaws_works_in_alternative_thaw_order() {
	new_test_ext().execute_with(|| {
		run_to_block(1);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 40, 1));
		assert_ok!(Gilt::place_bid(Origin::signed(1), 60, 1));
		assert_ok!(Gilt::place_bid(Origin::signed(2), 50, 1));
		Gilt::enlarge(200, 3);

		// Double everyone's free balances.
		Balances::make_free_balance_be(&2, 100);
		Balances::make_free_balance_be(&3, 200);
		Balances::make_free_balance_be(&4, 200);

		run_to_block(4);
		assert_ok!(Gilt::thaw(Origin::signed(2), 2));
		assert_ok!(Gilt::thaw(Origin::signed(1), 1));
		assert_ok!(Gilt::thaw(Origin::signed(1), 0));

		assert_eq!(Balances::free_balance(1), 200);
		assert_eq!(Balances::free_balance(2), 200);
	});
}

#[test]
fn enlargement_to_target_works() {
	new_test_ext().execute_with(|| {
		run_to_block(2);
		assert_ok!(Gilt::place_bid(Origin::signed(1), 40, 1));
		assert_ok!(Gilt::place_bid(Origin::signed(1), 40, 2));
		assert_ok!(Gilt::place_bid(Origin::signed(2), 40, 2));
		assert_ok!(Gilt::place_bid(Origin::signed(2), 40, 3));
		assert_ok!(Gilt::place_bid(Origin::signed(3), 40, 3));
		assert_ok!(Gilt::set_target(Origin::signed(1), Perquintill::from_percent(40)));

		run_to_block(3);
		assert_eq!(Queues::<Test>::get(1), vec![
			GiltBid { amount: 40, who: 1 },
		]);
		assert_eq!(Queues::<Test>::get(2), vec![
			GiltBid { amount: 40, who: 2 },
			GiltBid { amount: 40, who: 1 },
		]);
		assert_eq!(Queues::<Test>::get(3), vec![
			GiltBid { amount: 40, who: 3 },
			GiltBid { amount: 40, who: 2 },
		]);
		assert_eq!(QueueTotals::<Test>::get(), vec![(1, 40), (2, 80), (2, 80)]);

		run_to_block(4);
		// Two new gilts should have been issued to 2 & 3 for 40 each & duration of 3.
		assert_eq!(Active::<Test>::get(0).unwrap(), ActiveGilt {
			proportion: Perquintill::from_percent(10),
			amount: 40,
			who: 2,
			expiry: 13,
		});
		assert_eq!(Active::<Test>::get(1).unwrap(), ActiveGilt {
			proportion: Perquintill::from_percent(10),
			amount: 40,
			who: 3,
			expiry: 13,

		});
		assert_eq!(ActiveTotal::<Test>::get(), ActiveGiltsTotal {
			frozen: 80,
			proportion: Perquintill::from_percent(20),
			index: 2,
			target: Perquintill::from_percent(40),
		});

		run_to_block(5);
		// No change
		assert_eq!(ActiveTotal::<Test>::get(), ActiveGiltsTotal {
			frozen: 80,
			proportion: Perquintill::from_percent(20),
			index: 2,
			target: Perquintill::from_percent(40),
		});

		run_to_block(6);
		// Two new gilts should have been issued to 1 & 2 for 40 each & duration of 2.
		assert_eq!(Active::<Test>::get(2).unwrap(), ActiveGilt {
			proportion: Perquintill::from_percent(10),
			amount: 40,
			who: 1,
			expiry: 12,
		});
		assert_eq!(Active::<Test>::get(3).unwrap(), ActiveGilt {
			proportion: Perquintill::from_percent(10),
			amount: 40,
			who: 2,
			expiry: 12,

		});
		assert_eq!(ActiveTotal::<Test>::get(), ActiveGiltsTotal {
			frozen: 160,
			proportion: Perquintill::from_percent(40),
			index: 4,
			target: Perquintill::from_percent(40),
		});

		run_to_block(8);
		// No change now.
		assert_eq!(ActiveTotal::<Test>::get(), ActiveGiltsTotal {
			frozen: 160,
			proportion: Perquintill::from_percent(40),
			index: 4,
			target: Perquintill::from_percent(40),
		});

		// Set target a bit higher to use up the remaining bid.
		assert_ok!(Gilt::set_target(Origin::signed(1), Perquintill::from_percent(60)));
		run_to_block(10);

		// Two new gilts should have been issued to 1 & 2 for 40 each & duration of 2.
		assert_eq!(Active::<Test>::get(4).unwrap(), ActiveGilt {
			proportion: Perquintill::from_percent(10),
			amount: 40,
			who: 1,
			expiry: 13,
		});

		assert_eq!(ActiveTotal::<Test>::get(), ActiveGiltsTotal {
			frozen: 200,
			proportion: Perquintill::from_percent(50),
			index: 5,
			target: Perquintill::from_percent(60),
		});
	});
}
