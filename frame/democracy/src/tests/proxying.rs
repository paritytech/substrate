// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! The tests for functionality concerning proxying.

use super::*;

#[test]
fn proxy_should_work() {
	new_test_ext().execute_with(|| {
		assert_eq!(Democracy::proxy(10), None);
		assert!(System::allow_death(&10));

		assert_noop!(Democracy::activate_proxy(Origin::signed(1), 10), Error::<Test>::NotOpen);

		assert_ok!(Democracy::open_proxy(Origin::signed(10), 1));
		assert!(!System::allow_death(&10));
		assert_eq!(Democracy::proxy(10), Some(ProxyState::Open(1)));

		assert_noop!(Democracy::activate_proxy(Origin::signed(2), 10), Error::<Test>::WrongOpen);
		assert_ok!(Democracy::activate_proxy(Origin::signed(1), 10));
		assert_eq!(Democracy::proxy(10), Some(ProxyState::Active(1)));

		// Can't set when already set.
		assert_noop!(Democracy::activate_proxy(Origin::signed(2), 10), Error::<Test>::AlreadyProxy);

		// But this works because 11 isn't proxying.
		assert_ok!(Democracy::open_proxy(Origin::signed(11), 2));
		assert_ok!(Democracy::activate_proxy(Origin::signed(2), 11));
		assert_eq!(Democracy::proxy(10), Some(ProxyState::Active(1)));
		assert_eq!(Democracy::proxy(11), Some(ProxyState::Active(2)));

		// 2 cannot fire 1's proxy:
		assert_noop!(Democracy::deactivate_proxy(Origin::signed(2), 10), Error::<Test>::WrongProxy);

		// 1 deactivates their proxy:
		assert_ok!(Democracy::deactivate_proxy(Origin::signed(1), 10));
		assert_eq!(Democracy::proxy(10), Some(ProxyState::Open(1)));
		// but the proxy account cannot be killed until the proxy is closed.
		assert!(!System::allow_death(&10));

		// and then 10 closes it completely:
		assert_ok!(Democracy::close_proxy(Origin::signed(10)));
		assert_eq!(Democracy::proxy(10), None);
		assert!(System::allow_death(&10));

		// 11 just closes without 2's "permission".
		assert_ok!(Democracy::close_proxy(Origin::signed(11)));
		assert_eq!(Democracy::proxy(11), None);
		assert!(System::allow_death(&11));
	});
}

#[test]
fn voting_and_removing_votes_should_work_with_proxy() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert_ok!(propose_set_balance_and_note(1, 2, 1));

		fast_forward_to(2);
		let r = 0;
		assert_ok!(Democracy::open_proxy(Origin::signed(10), 1));
		assert_ok!(Democracy::activate_proxy(Origin::signed(1), 10));

		assert_ok!(Democracy::proxy_vote(Origin::signed(10), r, aye(1)));
		assert_eq!(tally(r), Tally { ayes: 1, nays: 0, turnout: 10 });

		assert_ok!(Democracy::proxy_remove_vote(Origin::signed(10), r));
		assert_eq!(tally(r), Tally { ayes: 0, nays: 0, turnout: 0 });
	});
}

#[test]
fn delegation_and_undelegation_should_work_with_proxy() {
	new_test_ext().execute_with(|| {
		System::set_block_number(0);
		assert_ok!(propose_set_balance_and_note(1, 2, 1));
		fast_forward_to(2);
		let r = 0;
		assert_ok!(Democracy::open_proxy(Origin::signed(10), 1));
		assert_ok!(Democracy::activate_proxy(Origin::signed(1), 10));
		assert_ok!(Democracy::vote(Origin::signed(2), r, aye(2)));

		assert_ok!(Democracy::proxy_delegate(Origin::signed(10), 2, Conviction::None, 10));
		assert_eq!(tally(r), Tally { ayes: 3, nays: 0, turnout: 30 });

		assert_ok!(Democracy::proxy_undelegate(Origin::signed(10)));
		assert_eq!(tally(r), Tally { ayes: 2, nays: 0, turnout: 20 });
	});
}

