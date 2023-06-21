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

//! The crate's tests.

use super::*;
use crate::mock::{RefState::*, *};
use assert_matches::assert_matches;
use codec::Decode;
use frame_support::{
	assert_noop, assert_ok,
	dispatch::{DispatchError::BadOrigin, RawOrigin},
	traits::Contains,
};
use pallet_balances::Error as BalancesError;

#[test]
fn params_should_work() {
	ExtBuilder::default().build_and_execute(|| {
		assert_eq!(ReferendumCount::<Test>::get(), 0);
		assert_eq!(Balances::free_balance(42), 0);
		assert_eq!(Balances::total_issuance(), 600);
	});
}

#[test]
fn basic_happy_path_works() {
	ExtBuilder::default().build_and_execute(|| {
		// #1: submit
		assert_ok!(Referenda::submit(
			RuntimeOrigin::signed(1),
			Box::new(RawOrigin::Root.into()),
			set_balance_proposal_bounded(1),
			DispatchTime::At(10),
		));
		assert_eq!(Balances::reserved_balance(&1), 2);
		assert_eq!(ReferendumCount::<Test>::get(), 1);
		assert_ok!(Referenda::place_decision_deposit(RuntimeOrigin::signed(2), 0));
		run_to(4);
		assert_eq!(DecidingCount::<Test>::get(0), 0);
		run_to(5);
		// #5: 4 blocks after submit - vote should now be deciding.
		assert_eq!(DecidingCount::<Test>::get(0), 1);
		run_to(6);
		// #6: Lots of ayes. Should now be confirming.
		set_tally(0, 100, 0);
		run_to(7);
		assert_eq!(confirming_until(0), 9);
		run_to(9);
		// #8: Should be confirmed & ended.
		assert_eq!(approved_since(0), 9);
		assert_ok!(Referenda::refund_decision_deposit(RuntimeOrigin::signed(2), 0));
		run_to(12);
		// #9: Should not yet be enacted.
		assert_eq!(Balances::free_balance(&42), 0);
		run_to(13);
		// #10: Proposal should be executed.
		assert_eq!(Balances::free_balance(&42), 1);
	});
}

#[test]
fn insta_confirm_then_kill_works() {
	ExtBuilder::default().build_and_execute(|| {
		let r = Confirming { immediate: true }.create();
		run_to(6);
		assert_ok!(Referenda::kill(RuntimeOrigin::root(), r));
		assert_eq!(killed_since(r), 6);
	});
}

#[test]
fn confirm_then_reconfirm_with_elapsed_trigger_works() {
	ExtBuilder::default().build_and_execute(|| {
		let r = Confirming { immediate: false }.create();
		assert_eq!(confirming_until(r), 8);
		run_to(7);
		set_tally(r, 100, 99);
		run_to(8);
		assert_eq!(deciding_and_failing_since(r), 5);
		run_to(11);
		assert_eq!(approved_since(r), 11);
	});
}

#[test]
fn instaconfirm_then_reconfirm_with_elapsed_trigger_works() {
	ExtBuilder::default().build_and_execute(|| {
		let r = Confirming { immediate: true }.create();
		run_to(6);
		assert_eq!(confirming_until(r), 7);
		set_tally(r, 100, 99);
		run_to(7);
		assert_eq!(deciding_and_failing_since(r), 5);
		run_to(11);
		assert_eq!(approved_since(r), 11);
	});
}

#[test]
fn instaconfirm_then_reconfirm_with_voting_trigger_works() {
	ExtBuilder::default().build_and_execute(|| {
		let r = Confirming { immediate: true }.create();
		run_to(6);
		assert_eq!(confirming_until(r), 7);
		set_tally(r, 100, 99);
		run_to(7);
		assert_eq!(deciding_and_failing_since(r), 5);
		run_to(8);
		set_tally(r, 100, 0);
		run_to(9);
		assert_eq!(confirming_until(r), 11);
		run_to(11);
		assert_eq!(approved_since(r), 11);
	});
}

#[test]
fn voting_should_extend_for_late_confirmation() {
	ExtBuilder::default().build_and_execute(|| {
		let r = Passing.create();
		run_to(10);
		assert_eq!(confirming_until(r), 11);
		run_to(11);
		assert_eq!(approved_since(r), 11);
	});
}

#[test]
fn should_instafail_during_extension_confirmation() {
	ExtBuilder::default().build_and_execute(|| {
		let r = Passing.create();
		run_to(10);
		assert_eq!(confirming_until(r), 11);
		// Should insta-fail since it's now past the normal voting time.
		set_tally(r, 100, 101);
		run_to(11);
		assert_eq!(rejected_since(r), 11);
	});
}

#[test]
fn confirming_then_fail_works() {
	ExtBuilder::default().build_and_execute(|| {
		let r = Failing.create();
		// Normally ends at 5 + 4 (voting period) = 9.
		assert_eq!(deciding_and_failing_since(r), 5);
		set_tally(r, 100, 0);
		run_to(6);
		assert_eq!(confirming_until(r), 8);
		set_tally(r, 100, 101);
		run_to(9);
		assert_eq!(rejected_since(r), 9);
	});
}

#[test]
fn queueing_works() {
	ExtBuilder::default().build_and_execute(|| {
		// Submit a proposal into a track with a queue len of 1.
		assert_ok!(Referenda::submit(
			RuntimeOrigin::signed(5),
			Box::new(RawOrigin::Root.into()),
			set_balance_proposal_bounded(0),
			DispatchTime::After(0),
		));
		assert_ok!(Referenda::place_decision_deposit(RuntimeOrigin::signed(5), 0));

		run_to(2);

		// Submit 3 more proposals into the same queue.
		for i in 1..=4 {
			assert_ok!(Referenda::submit(
				RuntimeOrigin::signed(i),
				Box::new(RawOrigin::Root.into()),
				set_balance_proposal_bounded(i),
				DispatchTime::After(0),
			));
		}
		for i in [1, 2, 4] {
			assert_ok!(Referenda::place_decision_deposit(RuntimeOrigin::signed(i), i as u32));
			// TODO: decision deposit after some initial votes with a non-highest voted coming
			// first.
		}
		assert_eq!(ReferendumCount::<Test>::get(), 5);

		run_to(5);
		// One should be being decided.
		assert_eq!(DecidingCount::<Test>::get(0), 1);
		assert_eq!(deciding_and_failing_since(0), 5);
		for i in 1..=4 {
			assert_eq!(waiting_since(i), 2);
		}

		// Vote to set order.
		set_tally(1, 1, 10);
		set_tally(2, 2, 20);
		set_tally(3, 3, 30);
		set_tally(4, 100, 0);
		println!("Agenda #6: {:?}", pallet_scheduler::Agenda::<Test>::get(6));
		run_to(6);
		println!("{:?}", Vec::<_>::from(TrackQueue::<Test>::get(0)));

		// Cancel the first.
		assert_ok!(Referenda::cancel(RuntimeOrigin::signed(4), 0));
		assert_eq!(cancelled_since(0), 6);

		// The other with the most approvals (#4) should be being decided.
		run_to(7);
		assert_eq!(DecidingCount::<Test>::get(0), 1);
		assert_eq!(deciding_since(4), 7);
		assert_eq!(confirming_until(4), 9);

		// Vote on the remaining two to change order.
		println!("Set tally #1");
		set_tally(1, 30, 31);
		println!("{:?}", Vec::<_>::from(TrackQueue::<Test>::get(0)));
		println!("Set tally #2");
		set_tally(2, 20, 20);
		println!("{:?}", Vec::<_>::from(TrackQueue::<Test>::get(0)));

		// Let confirmation period end.
		run_to(9);

		// #4 should have been confirmed.
		assert_eq!(approved_since(4), 9);

		// On to the next block to select the new referendum
		run_to(10);
		// #1 (the one with the most approvals) should now be being decided.
		assert_eq!(deciding_since(1), 10);

		// Let it end unsuccessfully.
		run_to(14);
		assert_eq!(rejected_since(1), 14);

		// Service queue.
		run_to(15);
		// #2 should now be being decided. It will (barely) pass.
		assert_eq!(deciding_and_failing_since(2), 15);

		// #2 moves into confirming at the last moment with a 50% approval.
		run_to(19);
		assert_eq!(confirming_until(2), 21);

		// #2 gets approved.
		run_to(21);
		assert_eq!(approved_since(2), 21);

		// The final one has since timed out.
		run_to(22);
		assert_eq!(timed_out_since(3), 22);
	});
}

#[test]
fn alarm_interval_works() {
	ExtBuilder::default().build_and_execute(|| {
		let call =
			<Test as Config>::Preimages::bound(CallOf::<Test, ()>::from(Call::nudge_referendum {
				index: 0,
			}))
			.unwrap();
		for n in 0..10 {
			let interval = n * n;
			let now = 100 * (interval + 1);
			System::set_block_number(now);
			AlarmInterval::set(interval);
			let when = now + 1;
			let (actual, _) = Referenda::set_alarm(call.clone(), when).unwrap();
			assert!(actual >= when);
			assert!(actual - interval <= when);
		}
	});
}

#[test]
fn decision_time_is_correct() {
	ExtBuilder::default().build_and_execute(|| {
		let decision_time = |since: u64| {
			Pallet::<Test>::decision_time(
				&DecidingStatus { since: since.into(), confirming: None },
				&Tally { ayes: 100, nays: 5 },
				TestTracksInfo::tracks()[0].0,
				&TestTracksInfo::tracks()[0].1,
			)
		};

		for i in 0u64..=100 {
			assert!(decision_time(i) > i, "The decision time should be delayed by the curve");
		}
	});
}

#[test]
fn auto_timeout_should_happen_with_nothing_but_submit() {
	ExtBuilder::default().build_and_execute(|| {
		// #1: submit
		assert_ok!(Referenda::submit(
			RuntimeOrigin::signed(1),
			Box::new(RawOrigin::Root.into()),
			set_balance_proposal_bounded(1),
			DispatchTime::At(20),
		));
		run_to(20);
		assert_matches!(ReferendumInfoFor::<Test>::get(0), Some(ReferendumInfo::Ongoing(..)));
		run_to(21);
		// #11: Timed out - ended.
		assert_matches!(
			ReferendumInfoFor::<Test>::get(0),
			Some(ReferendumInfo::TimedOut(21, _, None))
		);
	});
}

#[test]
fn tracks_are_distinguished() {
	ExtBuilder::default().build_and_execute(|| {
		assert_ok!(Referenda::submit(
			RuntimeOrigin::signed(1),
			Box::new(RawOrigin::Root.into()),
			set_balance_proposal_bounded(1),
			DispatchTime::At(10),
		));
		assert_ok!(Referenda::submit(
			RuntimeOrigin::signed(2),
			Box::new(RawOrigin::None.into()),
			set_balance_proposal_bounded(2),
			DispatchTime::At(20),
		));

		assert_ok!(Referenda::place_decision_deposit(RuntimeOrigin::signed(3), 0));
		assert_ok!(Referenda::place_decision_deposit(RuntimeOrigin::signed(4), 1));

		let mut i = ReferendumInfoFor::<Test>::iter().collect::<Vec<_>>();
		i.sort_by_key(|x| x.0);
		assert_eq!(
			i,
			vec![
				(
					0,
					ReferendumInfo::Ongoing(ReferendumStatus {
						track: 0,
						origin: OriginCaller::system(RawOrigin::Root),
						proposal: set_balance_proposal_bounded(1),
						enactment: DispatchTime::At(10),
						submitted: 1,
						submission_deposit: Deposit { who: 1, amount: 2 },
						decision_deposit: Some(Deposit { who: 3, amount: 10 }),
						deciding: None,
						tally: Tally { ayes: 0, nays: 0 },
						in_queue: false,
						alarm: Some((5, (5, 0))),
					})
				),
				(
					1,
					ReferendumInfo::Ongoing(ReferendumStatus {
						track: 1,
						origin: OriginCaller::system(RawOrigin::None),
						proposal: set_balance_proposal_bounded(2),
						enactment: DispatchTime::At(20),
						submitted: 1,
						submission_deposit: Deposit { who: 2, amount: 2 },
						decision_deposit: Some(Deposit { who: 4, amount: 1 }),
						deciding: None,
						tally: Tally { ayes: 0, nays: 0 },
						in_queue: false,
						alarm: Some((3, (3, 0))),
					})
				),
			]
		);
	});
}

#[test]
fn submit_errors_work() {
	ExtBuilder::default().build_and_execute(|| {
		let h = set_balance_proposal_bounded(1);
		// No track for Signed origins.
		assert_noop!(
			Referenda::submit(
				RuntimeOrigin::signed(1),
				Box::new(RawOrigin::Signed(2).into()),
				h.clone(),
				DispatchTime::At(10),
			),
			Error::<Test>::NoTrack
		);

		// No funds for deposit
		assert_noop!(
			Referenda::submit(
				RuntimeOrigin::signed(10),
				Box::new(RawOrigin::Root.into()),
				h,
				DispatchTime::At(10),
			),
			BalancesError::<Test>::InsufficientBalance
		);
	});
}

#[test]
fn decision_deposit_errors_work() {
	ExtBuilder::default().build_and_execute(|| {
		let e = Error::<Test>::NotOngoing;
		assert_noop!(Referenda::place_decision_deposit(RuntimeOrigin::signed(2), 0), e);

		let h = set_balance_proposal_bounded(1);
		assert_ok!(Referenda::submit(
			RuntimeOrigin::signed(1),
			Box::new(RawOrigin::Root.into()),
			h,
			DispatchTime::At(10),
		));
		let e = BalancesError::<Test>::InsufficientBalance;
		assert_noop!(Referenda::place_decision_deposit(RuntimeOrigin::signed(10), 0), e);

		assert_ok!(Referenda::place_decision_deposit(RuntimeOrigin::signed(2), 0));
		let e = Error::<Test>::HasDeposit;
		assert_noop!(Referenda::place_decision_deposit(RuntimeOrigin::signed(2), 0), e);
	});
}

#[test]
fn refund_deposit_works() {
	ExtBuilder::default().build_and_execute(|| {
		let e = Error::<Test>::BadReferendum;
		assert_noop!(Referenda::refund_decision_deposit(RuntimeOrigin::signed(1), 0), e);

		let h = set_balance_proposal_bounded(1);
		assert_ok!(Referenda::submit(
			RuntimeOrigin::signed(1),
			Box::new(RawOrigin::Root.into()),
			h,
			DispatchTime::At(10),
		));
		let e = Error::<Test>::NoDeposit;
		assert_noop!(Referenda::refund_decision_deposit(RuntimeOrigin::signed(2), 0), e);

		assert_ok!(Referenda::place_decision_deposit(RuntimeOrigin::signed(2), 0));
		let e = Error::<Test>::Unfinished;
		assert_noop!(Referenda::refund_decision_deposit(RuntimeOrigin::signed(3), 0), e);

		run_to(11);
		assert_ok!(Referenda::refund_decision_deposit(RuntimeOrigin::signed(3), 0));
	});
}

#[test]
fn refund_submission_deposit_works() {
	ExtBuilder::default().build_and_execute(|| {
		// refund of non existing referendum fails.
		let e = Error::<Test>::BadReferendum;
		assert_noop!(Referenda::refund_submission_deposit(RuntimeOrigin::signed(1), 0), e);
		// create a referendum.
		let h = set_balance_proposal_bounded(1);
		assert_ok!(Referenda::submit(
			RuntimeOrigin::signed(1),
			Box::new(RawOrigin::Root.into()),
			h.clone(),
			DispatchTime::At(10),
		));
		// refund of an ongoing referendum fails.
		let e = Error::<Test>::BadStatus;
		assert_noop!(Referenda::refund_submission_deposit(RuntimeOrigin::signed(3), 0), e);
		// cancel referendum.
		assert_ok!(Referenda::cancel(RuntimeOrigin::signed(4), 0));
		// refund of canceled referendum works.
		assert_ok!(Referenda::refund_submission_deposit(RuntimeOrigin::signed(3), 0));
		// fails if already refunded.
		let e = Error::<Test>::NoDeposit;
		assert_noop!(Referenda::refund_submission_deposit(RuntimeOrigin::signed(2), 0), e);
		// create second referendum.
		assert_ok!(Referenda::submit(
			RuntimeOrigin::signed(1),
			Box::new(RawOrigin::Root.into()),
			h,
			DispatchTime::At(10),
		));
		// refund of a killed referendum fails.
		assert_ok!(Referenda::kill(RuntimeOrigin::root(), 1));
		let e = Error::<Test>::NoDeposit;
		assert_noop!(Referenda::refund_submission_deposit(RuntimeOrigin::signed(2), 0), e);
	});
}

#[test]
fn cancel_works() {
	ExtBuilder::default().build_and_execute(|| {
		let h = set_balance_proposal_bounded(1);
		assert_ok!(Referenda::submit(
			RuntimeOrigin::signed(1),
			Box::new(RawOrigin::Root.into()),
			h,
			DispatchTime::At(10),
		));
		assert_ok!(Referenda::place_decision_deposit(RuntimeOrigin::signed(2), 0));

		run_to(8);
		assert_ok!(Referenda::cancel(RuntimeOrigin::signed(4), 0));
		assert_ok!(Referenda::refund_decision_deposit(RuntimeOrigin::signed(3), 0));
		assert_eq!(cancelled_since(0), 8);
	});
}

#[test]
fn cancel_errors_works() {
	ExtBuilder::default().build_and_execute(|| {
		let h = set_balance_proposal_bounded(1);
		assert_ok!(Referenda::submit(
			RuntimeOrigin::signed(1),
			Box::new(RawOrigin::Root.into()),
			h,
			DispatchTime::At(10),
		));
		assert_ok!(Referenda::place_decision_deposit(RuntimeOrigin::signed(2), 0));
		assert_noop!(Referenda::cancel(RuntimeOrigin::signed(1), 0), BadOrigin);

		run_to(11);
		assert_noop!(Referenda::cancel(RuntimeOrigin::signed(4), 0), Error::<Test>::NotOngoing);
	});
}

#[test]
fn kill_works() {
	ExtBuilder::default().build_and_execute(|| {
		let h = set_balance_proposal_bounded(1);
		assert_ok!(Referenda::submit(
			RuntimeOrigin::signed(1),
			Box::new(RawOrigin::Root.into()),
			h,
			DispatchTime::At(10),
		));
		assert_ok!(Referenda::place_decision_deposit(RuntimeOrigin::signed(2), 0));

		run_to(8);
		assert_ok!(Referenda::kill(RuntimeOrigin::root(), 0));
		let e = Error::<Test>::NoDeposit;
		assert_noop!(Referenda::refund_decision_deposit(RuntimeOrigin::signed(3), 0), e);
		assert_eq!(killed_since(0), 8);
	});
}

#[test]
fn kill_errors_works() {
	ExtBuilder::default().build_and_execute(|| {
		let h = set_balance_proposal_bounded(1);
		assert_ok!(Referenda::submit(
			RuntimeOrigin::signed(1),
			Box::new(RawOrigin::Root.into()),
			h,
			DispatchTime::At(10),
		));
		assert_ok!(Referenda::place_decision_deposit(RuntimeOrigin::signed(2), 0));
		assert_noop!(Referenda::kill(RuntimeOrigin::signed(4), 0), BadOrigin);

		run_to(11);
		assert_noop!(Referenda::kill(RuntimeOrigin::root(), 0), Error::<Test>::NotOngoing);
	});
}

#[test]
fn set_balance_proposal_is_correctly_filtered_out() {
	for i in 0..10 {
		let call = crate::mock::RuntimeCall::decode(&mut &set_balance_proposal(i)[..]).unwrap();
		assert!(!<Test as frame_system::Config>::BaseCallFilter::contains(&call));
	}
}

#[test]
fn curve_handles_all_inputs() {
	let test_curve = Curve::LinearDecreasing {
		length: Perbill::one(),
		floor: Perbill::zero(),
		ceil: Perbill::from_percent(100),
	};

	let delay = test_curve.delay(Perbill::zero());
	assert_eq!(delay, Perbill::one());

	let threshold = test_curve.threshold(Perbill::one());
	assert_eq!(threshold, Perbill::zero());
}

#[test]
fn set_metadata_works() {
	ExtBuilder::default().build_and_execute(|| {
		use frame_support::traits::Hash as PreimageHash;
		// invalid preimage hash.
		let invalid_hash: PreimageHash = [1u8; 32].into();
		// fails to set metadata for a finished referendum.
		assert_ok!(Referenda::submit(
			RuntimeOrigin::signed(1),
			Box::new(RawOrigin::Root.into()),
			set_balance_proposal_bounded(1),
			DispatchTime::At(1),
		));
		let index = ReferendumCount::<Test>::get() - 1;
		assert_ok!(Referenda::kill(RuntimeOrigin::root(), index));
		assert_noop!(
			Referenda::set_metadata(RuntimeOrigin::signed(1), index, Some(invalid_hash)),
			Error::<Test>::NotOngoing,
		);
		// no permission to set metadata.
		assert_ok!(Referenda::submit(
			RuntimeOrigin::signed(1),
			Box::new(RawOrigin::Root.into()),
			set_balance_proposal_bounded(1),
			DispatchTime::At(1),
		));
		let index = ReferendumCount::<Test>::get() - 1;
		assert_noop!(
			Referenda::set_metadata(RuntimeOrigin::signed(2), index, Some(invalid_hash)),
			Error::<Test>::NoPermission,
		);
		// preimage does not exist.
		let index = ReferendumCount::<Test>::get() - 1;
		assert_noop!(
			Referenda::set_metadata(RuntimeOrigin::signed(1), index, Some(invalid_hash)),
			Error::<Test>::PreimageNotExist,
		);
		// metadata set.
		let index = ReferendumCount::<Test>::get() - 1;
		let hash = note_preimage(1);
		assert_ok!(Referenda::set_metadata(RuntimeOrigin::signed(1), index, Some(hash)));
		System::assert_last_event(RuntimeEvent::Referenda(crate::Event::MetadataSet {
			index,
			hash,
		}));
	});
}

#[test]
fn clear_metadata_works() {
	ExtBuilder::default().build_and_execute(|| {
		let hash = note_preimage(1);
		assert_ok!(Referenda::submit(
			RuntimeOrigin::signed(1),
			Box::new(RawOrigin::Root.into()),
			set_balance_proposal_bounded(1),
			DispatchTime::At(1),
		));
		let index = ReferendumCount::<Test>::get() - 1;
		assert_ok!(Referenda::set_metadata(RuntimeOrigin::signed(1), index, Some(hash)));
		assert_noop!(
			Referenda::set_metadata(RuntimeOrigin::signed(2), index, None),
			Error::<Test>::NoPermission,
		);
		assert_ok!(Referenda::set_metadata(RuntimeOrigin::signed(1), index, None),);
		System::assert_last_event(RuntimeEvent::Referenda(crate::Event::MetadataCleared {
			index,
			hash,
		}));
	});
}
