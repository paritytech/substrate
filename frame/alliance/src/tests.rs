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

//! Tests for the alliance pallet.

use frame_support::{assert_noop, assert_ok, error::BadOrigin};
use frame_system::{EventRecord, Phase};

use super::*;
use crate::mock::*;

type AllianceMotionEvent = pallet_collective::Event<Test, pallet_collective::Instance1>;

#[test]
fn init_members_works() {
	new_test_ext().execute_with(|| {
		// alliance must be reset first, no witness data
		assert_noop!(
			Alliance::init_members(Origin::root(), vec![8], vec![], vec![],),
			Error::<Test, ()>::AllianceAlreadyInitialized,
		);

		// give a retirement notice to check later a retiring member not removed
		assert_ok!(Alliance::give_retirement_notice(Origin::signed(2)));
		assert!(Alliance::is_member_of(&2, MemberRole::Retiring));

		// disband the Alliance to init new
		assert_ok!(Alliance::disband(Origin::root(), DisbandWitness::new(2, 0)));

		// fails without root
		assert_noop!(Alliance::init_members(Origin::signed(1), vec![], vec![], vec![]), BadOrigin);

		// founders missing, other members given
		assert_noop!(
			Alliance::init_members(Origin::root(), vec![], vec![4], vec![2],),
			Error::<Test, ()>::FoundersMissing,
		);

		// success call
		assert_ok!(Alliance::init_members(Origin::root(), vec![8, 5], vec![4], vec![2],));

		// assert new set of voting members
		assert_eq!(Alliance::voting_members_sorted(), vec![4, 5, 8]);
		// assert new members member
		assert!(Alliance::is_founder(&8));
		assert!(Alliance::is_founder(&5));
		assert!(Alliance::is_fellow(&4));
		assert!(Alliance::is_ally(&2));
		// assert a retiring member from previous Alliance not removed
		assert!(Alliance::is_member_of(&2, MemberRole::Retiring));

		System::assert_last_event(mock::RuntimeEvent::Alliance(crate::Event::MembersInitialized {
			founders: vec![5, 8],
			fellows: vec![4],
			allies: vec![2],
		}));
	})
}

#[test]
fn disband_works() {
	new_test_ext().execute_with(|| {
		// ensure alliance is set
		assert_eq!(Alliance::voting_members_sorted(), vec![1, 2, 3]);

		// give a retirement notice to check later a retiring member not removed
		assert_ok!(Alliance::give_retirement_notice(Origin::signed(2)));
		assert!(Alliance::is_member_of(&2, MemberRole::Retiring));

		// join alliance and reserve funds
		assert_eq!(Balances::free_balance(9), 40);
		assert_ok!(Alliance::join_alliance(Origin::signed(9)));
		assert_eq!(Alliance::deposit_of(9), Some(25));
		assert_eq!(Balances::free_balance(9), 15);
		assert!(Alliance::is_member_of(&9, MemberRole::Ally));

		// fails without root
		assert_noop!(Alliance::disband(Origin::signed(1), Default::default()), BadOrigin);

		// bad witness data checks
		assert_noop!(
			Alliance::disband(Origin::root(), Default::default(),),
			Error::<Test, ()>::BadWitness
		);

		assert_noop!(
			Alliance::disband(Origin::root(), DisbandWitness::new(1, 1)),
			Error::<Test, ()>::BadWitness,
		);
		assert_noop!(
			Alliance::disband(Origin::root(), DisbandWitness::new(2, 0)),
			Error::<Test, ()>::BadWitness,
		);

		// success call
		assert_ok!(Alliance::disband(Origin::root(), DisbandWitness::new(2, 1)));

		// assert members disband
		assert!(!Alliance::is_member(&1));
		assert!(!Alliance::is_initialized());
		// assert a retiring member from the previous Alliance not removed
		assert!(Alliance::is_member_of(&2, MemberRole::Retiring));
		// deposit unreserved
		assert_eq!(Balances::free_balance(9), 40);

		System::assert_last_event(mock::RuntimeEvent::Alliance(crate::Event::AllianceDisbanded {
			voting_members: 2,
			ally_members: 1,
			unreserved: 1,
		}));

		// the Alliance must be set first
		assert_noop!(
			Alliance::disband(Origin::root(), DisbandWitness::new(100, 100)),
			Error::<Test, ()>::AllianceNotYetInitialized,
		);
	})
}

#[test]
fn propose_works() {
	new_test_ext().execute_with(|| {
		let (proposal, proposal_len, hash) = make_remark_proposal(42);

		// only voting member can propose proposal, 4 is ally not have vote rights
		assert_noop!(
			Alliance::propose(Origin::signed(4), 3, Box::new(proposal.clone()), proposal_len),
			Error::<Test, ()>::NoVotingRights
		);

		assert_ok!(Alliance::propose(
			Origin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_eq!(*AllianceMotion::proposals(), vec![hash]);
		assert_eq!(AllianceMotion::proposal_of(&hash), Some(proposal));
		assert_eq!(
			System::events(),
			vec![EventRecord {
				phase: Phase::Initialization,
				event: mock::RuntimeEvent::AllianceMotion(AllianceMotionEvent::Proposed {
					account: 1,
					proposal_index: 0,
					proposal_hash: hash,
					threshold: 3,
				}),
				topics: vec![],
			}]
		);
	});
}

#[test]
fn vote_works() {
	new_test_ext().execute_with(|| {
		let (proposal, proposal_len, hash) = make_remark_proposal(42);
		assert_ok!(Alliance::propose(
			Origin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_ok!(Alliance::vote(Origin::signed(2), hash, 0, true));

		let record = |event| EventRecord { phase: Phase::Initialization, event, topics: vec![] };
		assert_eq!(
			System::events(),
			vec![
				record(mock::RuntimeEvent::AllianceMotion(AllianceMotionEvent::Proposed {
					account: 1,
					proposal_index: 0,
					proposal_hash: hash,
					threshold: 3
				})),
				record(mock::RuntimeEvent::AllianceMotion(AllianceMotionEvent::Voted {
					account: 2,
					proposal_hash: hash,
					voted: true,
					yes: 1,
					no: 0,
				})),
			]
		);
	});
}

#[test]
fn veto_works() {
	new_test_ext().execute_with(|| {
		let (proposal, proposal_len, hash) = make_remark_proposal(42);
		assert_ok!(Alliance::propose(
			Origin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		// only set_rule/elevate_ally can be veto
		assert_noop!(
			Alliance::veto(Origin::signed(1), hash),
			Error::<Test, ()>::NotVetoableProposal
		);

		let cid = test_cid();
		let (vetoable_proposal, vetoable_proposal_len, vetoable_hash) = make_set_rule_proposal(cid);
		assert_ok!(Alliance::propose(
			Origin::signed(1),
			3,
			Box::new(vetoable_proposal.clone()),
			vetoable_proposal_len
		));

		// only founder have veto rights, 3 is fellow
		assert_noop!(
			Alliance::veto(Origin::signed(3), vetoable_hash),
			Error::<Test, ()>::NotFounder
		);

		assert_ok!(Alliance::veto(Origin::signed(2), vetoable_hash));
		let record = |event| EventRecord { phase: Phase::Initialization, event, topics: vec![] };
		assert_eq!(
			System::events(),
			vec![
				record(mock::RuntimeEvent::AllianceMotion(AllianceMotionEvent::Proposed {
					account: 1,
					proposal_index: 0,
					proposal_hash: hash,
					threshold: 3
				})),
				record(mock::RuntimeEvent::AllianceMotion(AllianceMotionEvent::Proposed {
					account: 1,
					proposal_index: 1,
					proposal_hash: vetoable_hash,
					threshold: 3
				})),
				record(mock::RuntimeEvent::AllianceMotion(AllianceMotionEvent::Disapproved {
					proposal_hash: vetoable_hash
				})),
			]
		);
	})
}

#[test]
fn close_works() {
	new_test_ext().execute_with(|| {
		let (proposal, proposal_len, hash) = make_remark_proposal(42);
		let proposal_weight = proposal.get_dispatch_info().weight;
		assert_ok!(Alliance::propose(
			Origin::signed(1),
			3,
			Box::new(proposal.clone()),
			proposal_len
		));
		assert_ok!(Alliance::vote(Origin::signed(1), hash, 0, true));
		assert_ok!(Alliance::vote(Origin::signed(2), hash, 0, true));
		assert_ok!(Alliance::vote(Origin::signed(3), hash, 0, true));
		assert_ok!(Alliance::close(Origin::signed(1), hash, 0, proposal_weight, proposal_len));

		let record = |event| EventRecord { phase: Phase::Initialization, event, topics: vec![] };
		assert_eq!(
			System::events(),
			vec![
				record(mock::RuntimeEvent::AllianceMotion(AllianceMotionEvent::Proposed {
					account: 1,
					proposal_index: 0,
					proposal_hash: hash,
					threshold: 3
				})),
				record(mock::RuntimeEvent::AllianceMotion(AllianceMotionEvent::Voted {
					account: 1,
					proposal_hash: hash,
					voted: true,
					yes: 1,
					no: 0,
				})),
				record(mock::RuntimeEvent::AllianceMotion(AllianceMotionEvent::Voted {
					account: 2,
					proposal_hash: hash,
					voted: true,
					yes: 2,
					no: 0,
				})),
				record(mock::RuntimeEvent::AllianceMotion(AllianceMotionEvent::Voted {
					account: 3,
					proposal_hash: hash,
					voted: true,
					yes: 3,
					no: 0,
				})),
				record(mock::RuntimeEvent::AllianceMotion(AllianceMotionEvent::Closed {
					proposal_hash: hash,
					yes: 3,
					no: 0,
				})),
				record(mock::RuntimeEvent::AllianceMotion(AllianceMotionEvent::Approved {
					proposal_hash: hash
				})),
				record(mock::RuntimeEvent::AllianceMotion(AllianceMotionEvent::Executed {
					proposal_hash: hash,
					result: Err(DispatchError::BadOrigin),
				}))
			]
		);
	});
}

#[test]
fn set_rule_works() {
	new_test_ext().execute_with(|| {
		let cid = test_cid();
		assert_ok!(Alliance::set_rule(Origin::signed(1), cid.clone()));
		assert_eq!(Alliance::rule(), Some(cid.clone()));

		System::assert_last_event(mock::RuntimeEvent::Alliance(crate::Event::NewRuleSet {
			rule: cid,
		}));
	});
}

#[test]
fn announce_works() {
	new_test_ext().execute_with(|| {
		let cid = test_cid();

		assert_noop!(Alliance::announce(Origin::signed(2), cid.clone()), BadOrigin);

		assert_ok!(Alliance::announce(Origin::signed(3), cid.clone()));
		assert_eq!(Alliance::announcements(), vec![cid.clone()]);

		System::assert_last_event(mock::RuntimeEvent::Alliance(crate::Event::Announced {
			announcement: cid,
		}));
	});
}

#[test]
fn remove_announcement_works() {
	new_test_ext().execute_with(|| {
		let cid = test_cid();
		assert_ok!(Alliance::announce(Origin::signed(3), cid.clone()));
		assert_eq!(Alliance::announcements(), vec![cid.clone()]);
		System::assert_last_event(mock::RuntimeEvent::Alliance(crate::Event::Announced {
			announcement: cid.clone(),
		}));

		System::set_block_number(2);

		assert_ok!(Alliance::remove_announcement(Origin::signed(3), cid.clone()));
		assert_eq!(Alliance::announcements(), vec![]);
		System::assert_last_event(mock::RuntimeEvent::Alliance(
			crate::Event::AnnouncementRemoved { announcement: cid },
		));
	});
}

#[test]
fn join_alliance_works() {
	new_test_ext().execute_with(|| {
		// check already member
		assert_noop!(Alliance::join_alliance(Origin::signed(1)), Error::<Test, ()>::AlreadyMember);

		// check already listed as unscrupulous
		assert_ok!(Alliance::add_unscrupulous_items(
			Origin::signed(3),
			vec![UnscrupulousItem::AccountId(4)]
		));
		assert_noop!(
			Alliance::join_alliance(Origin::signed(4)),
			Error::<Test, ()>::AccountNonGrata
		);
		assert_ok!(Alliance::remove_unscrupulous_items(
			Origin::signed(3),
			vec![UnscrupulousItem::AccountId(4)]
		));

		// check deposit funds
		assert_noop!(
			Alliance::join_alliance(Origin::signed(5)),
			Error::<Test, ()>::InsufficientFunds
		);

		// success to submit
		assert_ok!(Alliance::join_alliance(Origin::signed(4)));
		assert_eq!(Alliance::deposit_of(4), Some(25));
		assert_eq!(Alliance::members(MemberRole::Ally), vec![4]);

		// check already member
		assert_noop!(Alliance::join_alliance(Origin::signed(4)), Error::<Test, ()>::AlreadyMember);

		// check missing identity judgement
		#[cfg(not(feature = "runtime-benchmarks"))]
		assert_noop!(
			Alliance::join_alliance(Origin::signed(6)),
			Error::<Test, ()>::WithoutGoodIdentityJudgement
		);
		// check missing identity info
		#[cfg(not(feature = "runtime-benchmarks"))]
		assert_noop!(
			Alliance::join_alliance(Origin::signed(7)),
			Error::<Test, ()>::WithoutIdentityDisplayAndWebsite
		);
	});
}

#[test]
fn nominate_ally_works() {
	new_test_ext().execute_with(|| {
		// check already member
		assert_noop!(
			Alliance::nominate_ally(Origin::signed(1), 2),
			Error::<Test, ()>::AlreadyMember
		);

		// only voting member(founder/fellow) have nominate right
		assert_noop!(
			Alliance::nominate_ally(Origin::signed(5), 4),
			Error::<Test, ()>::NoVotingRights
		);

		// check already listed as unscrupulous
		assert_ok!(Alliance::add_unscrupulous_items(
			Origin::signed(3),
			vec![UnscrupulousItem::AccountId(4)]
		));
		assert_noop!(
			Alliance::nominate_ally(Origin::signed(1), 4),
			Error::<Test, ()>::AccountNonGrata
		);
		assert_ok!(Alliance::remove_unscrupulous_items(
			Origin::signed(3),
			vec![UnscrupulousItem::AccountId(4)]
		));

		// success to nominate
		assert_ok!(Alliance::nominate_ally(Origin::signed(1), 4));
		assert_eq!(Alliance::deposit_of(4), None);
		assert_eq!(Alliance::members(MemberRole::Ally), vec![4]);

		// check already member
		assert_noop!(
			Alliance::nominate_ally(Origin::signed(1), 4),
			Error::<Test, ()>::AlreadyMember
		);

		// check missing identity judgement
		#[cfg(not(feature = "runtime-benchmarks"))]
		assert_noop!(
			Alliance::join_alliance(Origin::signed(6)),
			Error::<Test, ()>::WithoutGoodIdentityJudgement
		);
		// check missing identity info
		#[cfg(not(feature = "runtime-benchmarks"))]
		assert_noop!(
			Alliance::join_alliance(Origin::signed(7)),
			Error::<Test, ()>::WithoutIdentityDisplayAndWebsite
		);
	});
}

#[test]
fn elevate_ally_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(Alliance::elevate_ally(Origin::signed(2), 4), Error::<Test, ()>::NotAlly);

		assert_ok!(Alliance::join_alliance(Origin::signed(4)));
		assert_eq!(Alliance::members(MemberRole::Ally), vec![4]);
		assert_eq!(Alliance::members(MemberRole::Fellow), vec![3]);

		assert_ok!(Alliance::elevate_ally(Origin::signed(2), 4));
		assert_eq!(Alliance::members(MemberRole::Ally), Vec::<u64>::new());
		assert_eq!(Alliance::members(MemberRole::Fellow), vec![3, 4]);
	});
}

#[test]
fn give_retirement_notice_work() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			Alliance::give_retirement_notice(Origin::signed(4)),
			Error::<Test, ()>::NotMember
		);

		assert_eq!(Alliance::members(MemberRole::Fellow), vec![3]);
		assert_ok!(Alliance::give_retirement_notice(Origin::signed(3)));
		assert_eq!(Alliance::members(MemberRole::Fellow), Vec::<u64>::new());
		assert_eq!(Alliance::members(MemberRole::Retiring), vec![3]);
		System::assert_last_event(mock::RuntimeEvent::Alliance(
			crate::Event::MemberRetirementPeriodStarted { member: (3) },
		));

		assert_noop!(
			Alliance::give_retirement_notice(Origin::signed(3)),
			Error::<Test, ()>::AlreadyRetiring
		);
	});
}

#[test]
fn retire_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(
			Alliance::retire(Origin::signed(2)),
			Error::<Test, ()>::RetirementNoticeNotGiven
		);

		assert_noop!(
			Alliance::retire(Origin::signed(4)),
			Error::<Test, ()>::RetirementNoticeNotGiven
		);

		assert_eq!(Alliance::members(MemberRole::Fellow), vec![3]);
		assert_ok!(Alliance::give_retirement_notice(Origin::signed(3)));
		assert_noop!(
			Alliance::retire(Origin::signed(3)),
			Error::<Test, ()>::RetirementPeriodNotPassed
		);
		System::set_block_number(System::block_number() + RetirementPeriod::get());
		assert_ok!(Alliance::retire(Origin::signed(3)));
		assert_eq!(Alliance::members(MemberRole::Fellow), Vec::<u64>::new());
		System::assert_last_event(mock::RuntimeEvent::Alliance(crate::Event::MemberRetired {
			member: (3),
			unreserved: None,
		}));

		// Move time on:
		System::set_block_number(System::block_number() + RetirementPeriod::get());

		assert_powerless(Origin::signed(3));
	});
}

fn assert_powerless(user: Origin) {
	//vote / veto with a valid propsal
	let cid = test_cid();
	let (proposal, _, _) = make_kick_member_proposal(42);

	assert_noop!(Alliance::init_members(user.clone(), vec![], vec![], vec![],), BadOrigin);

	assert_noop!(
		Alliance::disband(user.clone(), DisbandWitness { voting_members: 3, ..Default::default() }),
		BadOrigin
	);

	assert_noop!(Alliance::set_rule(user.clone(), cid.clone()), BadOrigin);

	assert_noop!(Alliance::retire(user.clone()), Error::<Test, ()>::RetirementNoticeNotGiven);

	assert_noop!(Alliance::give_retirement_notice(user.clone()), Error::<Test, ()>::NotMember);

	assert_noop!(Alliance::elevate_ally(user.clone(), 4), BadOrigin);

	assert_noop!(Alliance::kick_member(user.clone(), 1), BadOrigin);

	assert_noop!(Alliance::nominate_ally(user.clone(), 4), Error::<Test, ()>::NoVotingRights);

	assert_noop!(
		Alliance::propose(user.clone(), 5, Box::new(proposal), 1000),
		Error::<Test, ()>::NoVotingRights
	);
}

#[test]
fn kick_member_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(Alliance::kick_member(Origin::signed(4), 4), BadOrigin);

		assert_noop!(Alliance::kick_member(Origin::signed(2), 4), Error::<Test, ()>::NotMember);

		<DepositOf<Test, ()>>::insert(2, 25);
		assert_eq!(Alliance::members(MemberRole::Founder), vec![1, 2]);
		assert_ok!(Alliance::kick_member(Origin::signed(2), 2));
		assert_eq!(Alliance::members(MemberRole::Founder), vec![1]);
		assert_eq!(<DepositOf<Test, ()>>::get(2), None);
		System::assert_last_event(mock::RuntimeEvent::Alliance(crate::Event::MemberKicked {
			member: (2),
			slashed: Some(25),
		}));
	});
}

#[test]
fn add_unscrupulous_items_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(Alliance::add_unscrupulous_items(Origin::signed(2), vec![]), BadOrigin);

		assert_ok!(Alliance::add_unscrupulous_items(
			Origin::signed(3),
			vec![
				UnscrupulousItem::AccountId(3),
				UnscrupulousItem::Website("abc".as_bytes().to_vec().try_into().unwrap())
			]
		));
		assert_eq!(Alliance::unscrupulous_accounts().into_inner(), vec![3]);
		assert_eq!(Alliance::unscrupulous_websites().into_inner(), vec!["abc".as_bytes().to_vec()]);

		assert_noop!(
			Alliance::add_unscrupulous_items(
				Origin::signed(3),
				vec![UnscrupulousItem::AccountId(3)]
			),
			Error::<Test, ()>::AlreadyUnscrupulous
		);
	});
}

#[test]
fn remove_unscrupulous_items_works() {
	new_test_ext().execute_with(|| {
		assert_noop!(Alliance::remove_unscrupulous_items(Origin::signed(2), vec![]), BadOrigin);

		assert_noop!(
			Alliance::remove_unscrupulous_items(
				Origin::signed(3),
				vec![UnscrupulousItem::AccountId(3)]
			),
			Error::<Test, ()>::NotListedAsUnscrupulous
		);

		assert_ok!(Alliance::add_unscrupulous_items(
			Origin::signed(3),
			vec![UnscrupulousItem::AccountId(3)]
		));
		assert_eq!(Alliance::unscrupulous_accounts(), vec![3]);
		assert_ok!(Alliance::remove_unscrupulous_items(
			Origin::signed(3),
			vec![UnscrupulousItem::AccountId(3)]
		));
		assert_eq!(Alliance::unscrupulous_accounts(), Vec::<u64>::new());
	});
}
