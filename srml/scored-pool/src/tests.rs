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

use super::*;
use mock::*;

use srml_support::{assert_ok, assert_noop};
use sr_io::with_externalities;
use sr_primitives::traits::OnInitialize;

type ScoredPool = Module<Test>;
type System = system::Module<Test>;
type Balances = balances::Module<Test>;

fn fetch_from_pool(who: u64) -> Option<(u64, Option<u64>)> {
	ScoredPool::pool()
		.into_iter()
		.find(|item| item.0 == who)
}

#[test]
fn query_membership_works() {
	with_externalities(&mut new_test_ext(), || {
		assert_eq!(ScoredPool::members(), vec![20, 40]);
		assert_eq!(Balances::reserved_balance(&31), CandidateDeposit::get());
		assert_eq!(Balances::reserved_balance(&40), CandidateDeposit::get());
		assert_eq!(MEMBERS.with(|m| m.borrow().clone()), vec![20, 40]);
	});
}
#[test]
fn submit_candidacy_must_not_work() {
	with_externalities(&mut new_test_ext(), || {
		assert_noop!(ScoredPool::submit_candidacy(Origin::signed(99)), "balance too low");
		assert_noop!(ScoredPool::submit_candidacy(Origin::signed(10)), "already a member");
	});
}

#[test]
fn submit_candidacy_works() {
	with_externalities(&mut new_test_ext(), || {
		// given
		let who = 15;

		// when
		assert_ok!(ScoredPool::submit_candidacy(Origin::signed(who)));
		assert_eq!(fetch_from_pool(15), Some((who, None)));

		// then
		assert_eq!(Balances::reserved_balance(&who), CandidateDeposit::get());
	});
}

#[test]
fn scoring_works() {
	with_externalities(&mut new_test_ext(), || {
		// given
		let who = 15;
		let score = 99;
		assert_ok!(ScoredPool::submit_candidacy(Origin::signed(who)));

		// when
		assert_ok!(ScoredPool::score(Origin::signed(ScoreOrigin::get()), who, score));

		// then
		assert_eq!(fetch_from_pool(who), Some((who, Some(score))));
		assert_eq!(ScoredPool::find_in_pool(&who),
				   Ok(0)); // must be first element, since highest scored
	});
}

#[test]
fn scoring_same_element_with_same_score_works() {
	with_externalities(&mut new_test_ext(), || {
		// given
		let who = 31;
		let score = 2;

		// when
		assert_ok!(ScoredPool::score(Origin::signed(ScoreOrigin::get()), who, score));

		// then
		assert_eq!(fetch_from_pool(who), Some((who, Some(score))));

		// must have been inserted right before the `20` element which is
		// of the same score as `31`. so sort order is maintained.
		assert_eq!(ScoredPool::find_in_pool(&who), Ok(1));
	});
}

#[test]
fn kicking_works_only_for_authorized() {
	with_externalities(&mut new_test_ext(), || {
		assert_noop!(ScoredPool::kick(Origin::signed(99), 40), "bad origin");
	});
}

#[test]
fn kicking_works() {
	with_externalities(&mut new_test_ext(), || {
		// given
		let who = 40;
		assert_eq!(Balances::reserved_balance(&who), CandidateDeposit::get());
		assert_eq!(ScoredPool::find_in_pool(&who), Ok(0));

		// when
		assert_ok!(ScoredPool::kick(Origin::signed(KickOrigin::get()), who));

		// then
		assert_eq!(ScoredPool::find_in_pool(&who), Err("not a member"));
		assert_eq!(ScoredPool::members(), vec![20, 31]);
		assert_eq!(MEMBERS.with(|m| m.borrow().clone()), ScoredPool::members());
		assert_eq!(Balances::reserved_balance(&who), 0); // deposit must have been returned
	});
}

#[test]
fn unscored_entities_must_not_be_used_for_filling_members() {
	with_externalities(&mut new_test_ext(), || {
		// given
		// we submit a candidacy, score will be None
		assert_ok!(ScoredPool::submit_candidacy(Origin::signed(15)));

		// when
		// we remove every scored member
		ScoredPool::pool()
			.into_iter()
			.for_each(|(who, score)| {
				if let Some(_) = score {
					assert_ok!(ScoredPool::kick(Origin::signed(KickOrigin::get()), who));
				}
			});

		// then
		// the None candidates should not have been filled in
		assert_eq!(ScoredPool::members(), vec![]);
		assert_eq!(MEMBERS.with(|m| m.borrow().clone()), ScoredPool::members());
	});
}

#[test]
fn refreshing_works() {
	with_externalities(&mut new_test_ext(), || {
		// given
		assert_ok!(ScoredPool::submit_candidacy(Origin::signed(15)));
		assert_ok!(ScoredPool::score(Origin::signed(ScoreOrigin::get()), 15, 99));

		// when
		ScoredPool::refresh_members(true);

		// then
		assert_eq!(ScoredPool::members(), vec![15, 40]);
		assert_eq!(MEMBERS.with(|m| m.borrow().clone()), ScoredPool::members());
	});
}

#[test]
fn refreshing_happens_every_period() {
	with_externalities(&mut new_test_ext(), || {
		// given
		System::set_block_number(1);
		assert_ok!(ScoredPool::submit_candidacy(Origin::signed(15)));
		assert_ok!(ScoredPool::score(Origin::signed(ScoreOrigin::get()), 15, 99));
		assert_eq!(ScoredPool::members(), vec![20, 40]);

		// when
		System::set_block_number(4);
		ScoredPool::on_initialize(4);

		// then
		assert_eq!(ScoredPool::members(), vec![15, 40]);
		assert_eq!(MEMBERS.with(|m| m.borrow().clone()), ScoredPool::members());
	});
}

#[test]
fn test_withdraw_candidacy_only_works_for_members() {
	with_externalities(&mut new_test_ext(), || {
		assert_noop!(ScoredPool::withdraw_candidacy(Origin::signed(77)), "not a member");
	});
}

#[test]
fn test_withdraw_unscored_candidacy() {
	with_externalities(&mut new_test_ext(), || {
		// given
		let who = 5;

		// when
		assert_ok!(ScoredPool::withdraw_candidacy(Origin::signed(who)));

		// then
		assert_eq!(fetch_from_pool(5), None);
	});
}

#[test]
fn test_withdraw_scored_candidacy() {
	with_externalities(&mut new_test_ext(), || {
		// given
		let who = 40;
		assert_eq!(Balances::reserved_balance(&who), CandidateDeposit::get());

		// when
		assert_ok!(ScoredPool::withdraw_candidacy(Origin::signed(who)));

		// then
		assert_eq!(fetch_from_pool(who), None);
		assert_eq!(ScoredPool::members(), vec![20, 31]);
		assert_eq!(Balances::reserved_balance(&who), 0);
	});
}
