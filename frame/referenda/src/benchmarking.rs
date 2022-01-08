// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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

//! Democracy pallet benchmarking.

use super::*;
use crate::Pallet as Referenda;
use assert_matches::assert_matches;
use frame_benchmarking::{account, benchmarks, whitelist_account};
use frame_support::{
	assert_ok,
	traits::{Currency, EnsureOrigin},
};
use frame_system::RawOrigin;
use sp_runtime::traits::{Bounded, Hash};

const SEED: u32 = 0;

#[allow(dead_code)]
fn assert_last_event<T: Config>(generic_event: <T as Config>::Event) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

fn funded_account<T: Config>(name: &'static str, index: u32) -> T::AccountId {
	let caller: T::AccountId = account(name, index, SEED);
	T::Currency::make_free_balance_be(&caller, BalanceOf::<T>::max_value());
	caller
}

fn create_referendum<T: Config>() -> (T::AccountId, ReferendumIndex) {
	let caller = funded_account::<T>("caller", 0);
	whitelist_account!(caller);
	assert_ok!(Referenda::<T>::submit(
		RawOrigin::Signed(caller.clone()).into(),
		RawOrigin::Root.into(),
		T::Hashing::hash_of(&0),
		AtOrAfter::After(0u32.into())
	));
	let index = ReferendumCount::<T>::get() - 1;
	(caller, index)
}

fn place_deposit<T: Config>(index: ReferendumIndex) {
	let caller = funded_account::<T>("caller", 0);
	whitelist_account!(caller);
	assert_ok!(Referenda::<T>::place_decision_deposit(
		RawOrigin::Signed(caller.clone()).into(),
		index,
	));
}

fn nudge<T: Config>(index: ReferendumIndex) {
	assert_ok!(Referenda::<T>::nudge_referendum(RawOrigin::Root.into(), index));
}

fn fill_queue<T: Config>(
	index: ReferendumIndex,
	spaces: u32,
	pass_after: u32,
) -> Vec<ReferendumIndex> {
	// First, create enough other referendums to fill the track.
	let mut others = vec![];
	for _ in 0..info::<T>(index).max_deciding {
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
		others.push(index);
	}

	// We will also need enough referenda which are queued and passing, we want `MaxQueued - 1`
	// in order to force the maximum amount of work to insert ours into the queue.
	for _ in spaces..T::MaxQueued::get() {
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
		make_passing_after::<T>(index, Perbill::from_percent(pass_after));
		others.push(index);
	}

	// Skip to when they can start being decided.
	skip_prepare_period::<T>(index);

	// Manually nudge the other referenda first to ensure that they begin.
	others.iter().for_each(|&i| nudge::<T>(i));

	others
}

fn info<T: Config>(index: ReferendumIndex) -> &'static TrackInfoOf<T> {
	let status = Referenda::<T>::ensure_ongoing(index).unwrap();
	T::Tracks::info(status.track).expect("Id value returned from T::Tracks")
}

fn make_passing_after<T: Config>(index: ReferendumIndex, period_portion: Perbill) {
	let turnout = info::<T>(index).min_turnout.threshold(period_portion);
	let approval = info::<T>(index).min_approval.threshold(period_portion);
	Referenda::<T>::access_poll(index, |status| {
		if let PollStatus::Ongoing(tally, ..) = status {
			*tally = T::Tally::from_requirements(turnout, approval);
		}
	});
}

fn make_passing<T: Config>(index: ReferendumIndex) {
	Referenda::<T>::access_poll(index, |status| {
		if let PollStatus::Ongoing(tally, ..) = status {
			*tally = T::Tally::unanimity();
		}
	});
}

fn make_failing<T: Config>(index: ReferendumIndex) {
	Referenda::<T>::access_poll(index, |status| {
		if let PollStatus::Ongoing(tally, ..) = status {
			*tally = T::Tally::default();
		}
	});
}

fn skip_prepare_period<T: Config>(index: ReferendumIndex) {
	let status = Referenda::<T>::ensure_ongoing(index).unwrap();
	let prepare_period_over = status.submitted + info::<T>(index).prepare_period;
	frame_system::Pallet::<T>::set_block_number(prepare_period_over);
}

fn skip_decision_period<T: Config>(index: ReferendumIndex) {
	let status = Referenda::<T>::ensure_ongoing(index).unwrap();
	let decision_period_over = status.deciding.unwrap().since + info::<T>(index).decision_period;
	frame_system::Pallet::<T>::set_block_number(decision_period_over);
}

fn skip_confirm_period<T: Config>(index: ReferendumIndex) {
	let status = Referenda::<T>::ensure_ongoing(index).unwrap();
	let confirm_period_over = status.deciding.unwrap().confirming.unwrap();
	frame_system::Pallet::<T>::set_block_number(confirm_period_over);
}

fn skip_timeout_period<T: Config>(index: ReferendumIndex) {
	let status = Referenda::<T>::ensure_ongoing(index).unwrap();
	let timeout_period_over = status.submitted + T::UndecidingTimeout::get();
	frame_system::Pallet::<T>::set_block_number(timeout_period_over);
}

fn alarm_time<T: Config>(index: ReferendumIndex) -> T::BlockNumber {
	let status = Referenda::<T>::ensure_ongoing(index).unwrap();
	status.alarm.unwrap().0
}

fn is_confirming<T: Config>(index: ReferendumIndex) -> bool {
	let status = Referenda::<T>::ensure_ongoing(index).unwrap();
	matches!(
		status,
		ReferendumStatus { deciding: Some(DecidingStatus { confirming: Some(_), .. }), .. }
	)
}

fn is_not_confirming<T: Config>(index: ReferendumIndex) -> bool {
	let status = Referenda::<T>::ensure_ongoing(index).unwrap();
	matches!(
		status,
		ReferendumStatus { deciding: Some(DecidingStatus { confirming: None, .. }), .. }
	)
}

benchmarks! {
	submit {
		let caller = funded_account::<T>("caller", 0);
		whitelist_account!(caller);
	}: _(
		RawOrigin::Signed(caller),
		RawOrigin::Root.into(),
		T::Hashing::hash_of(&0),
		AtOrAfter::After(0u32.into())
	) verify {
		let index = ReferendumCount::<T>::get().checked_sub(1).unwrap();
		assert_matches!(ReferendumInfoFor::<T>::get(index), Some(ReferendumInfo::Ongoing(_)));
	}

	place_decision_deposit_preparing {
		let (caller, index) = create_referendum::<T>();
	}: place_decision_deposit(RawOrigin::Signed(caller), index)
	verify {
		assert!(Referenda::<T>::ensure_ongoing(index).unwrap().decision_deposit.is_some());
	}

	place_decision_deposit_queued {
		let (caller, index) = create_referendum::<T>();
		fill_queue::<T>(index, 1, 90);
	}: place_decision_deposit(RawOrigin::Signed(caller), index)
	verify {
		let track = Referenda::<T>::ensure_ongoing(index).unwrap().track;
		assert_eq!(TrackQueue::<T>::get(&track).len() as u32, T::MaxQueued::get());
		assert_eq!(TrackQueue::<T>::get(&track)[0], (index, 0u32.into()));
	}

	place_decision_deposit_not_queued {
		let (caller, index) = create_referendum::<T>();
		fill_queue::<T>(index, 0, 90);
	}: place_decision_deposit(RawOrigin::Signed(caller), index)
	verify {
		let track = Referenda::<T>::ensure_ongoing(index).unwrap().track;
		assert_eq!(TrackQueue::<T>::get(&track).len() as u32, T::MaxQueued::get());
		assert!(TrackQueue::<T>::get(&track).into_iter().all(|(i, _)| i != index));
	}

	place_decision_deposit_passing {
		let (caller, index) = create_referendum::<T>();
		skip_prepare_period::<T>(index);
		make_passing::<T>(index);
	}: place_decision_deposit(RawOrigin::Signed(caller), index)
	verify {
		assert!(is_confirming::<T>(index));
	}

	place_decision_deposit_failing {
		let (caller, index) = create_referendum::<T>();
		skip_prepare_period::<T>(index);
	}: place_decision_deposit(RawOrigin::Signed(caller), index)
	verify {
		assert!(is_not_confirming::<T>(index));
	}

	refund_decision_deposit {
		let (caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
		assert_ok!(Referenda::<T>::cancel(T::CancelOrigin::successful_origin(), index));
	}: _(RawOrigin::Signed(caller), index)
	verify {
		assert_matches!(ReferendumInfoFor::<T>::get(index), Some(ReferendumInfo::Cancelled(_, _, None)));
	}

	cancel {
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
	}: _<T::Origin>(T::CancelOrigin::successful_origin(), index)
	verify {
		assert_matches!(ReferendumInfoFor::<T>::get(index), Some(ReferendumInfo::Cancelled(..)));
	}

	kill {
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
	}: _<T::Origin>(T::KillOrigin::successful_origin(), index)
	verify {
		assert_matches!(ReferendumInfoFor::<T>::get(index), Some(ReferendumInfo::Killed(..)));
	}

	one_fewer_deciding_queue_empty {
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
		skip_prepare_period::<T>(index);
		nudge::<T>(index);
		let track = Referenda::<T>::ensure_ongoing(index).unwrap().track;
		assert_ok!(Referenda::<T>::cancel(T::CancelOrigin::successful_origin(), index));
		assert_eq!(DecidingCount::<T>::get(&track), 1);
	}: one_fewer_deciding(RawOrigin::Root, track.clone())
	verify {
		assert_eq!(DecidingCount::<T>::get(&track), 0);
	}

	one_fewer_deciding_failing {
		let (_caller, index) = create_referendum::<T>();
		// No spaces free in the queue.
		let queued = fill_queue::<T>(index, 0, 90);
		let track = Referenda::<T>::ensure_ongoing(index).unwrap().track;
		assert_ok!(Referenda::<T>::cancel(T::CancelOrigin::successful_origin(), queued[0]));
		assert_eq!(TrackQueue::<T>::get(&track).len() as u32, T::MaxQueued::get());
		let deciding_count = DecidingCount::<T>::get(&track);
	}: one_fewer_deciding(RawOrigin::Root, track.clone())
	verify {
		assert_eq!(DecidingCount::<T>::get(&track), deciding_count);
		assert_eq!(TrackQueue::<T>::get(&track).len() as u32, T::MaxQueued::get() - 1);
		assert!(queued.into_iter().skip(1).all(|i| Referenda::<T>::ensure_ongoing(i)
			.unwrap()
			.deciding
			.map_or(true, |d| d.confirming.is_none())
		));
	}

	one_fewer_deciding_passing {
		let (_caller, index) = create_referendum::<T>();
		// No spaces free in the queue.
		let queued = fill_queue::<T>(index, 0, 0);
		let track = Referenda::<T>::ensure_ongoing(index).unwrap().track;
		assert_ok!(Referenda::<T>::cancel(T::CancelOrigin::successful_origin(), queued[0]));
		assert_eq!(TrackQueue::<T>::get(&track).len() as u32, T::MaxQueued::get());
		let deciding_count = DecidingCount::<T>::get(&track);
	}: one_fewer_deciding(RawOrigin::Root, track.clone())
	verify {
		assert_eq!(DecidingCount::<T>::get(&track), deciding_count);
		assert_eq!(TrackQueue::<T>::get(&track).len() as u32, T::MaxQueued::get() - 1);
		assert!(queued.into_iter().skip(1).all(|i| Referenda::<T>::ensure_ongoing(i)
			.unwrap()
			.deciding
			.map_or(true, |d| d.confirming.is_some())
		));
	}

	nudge_referendum_requeued_insertion {
		// First create our referendum and place the deposit. It will be failing.
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
		fill_queue::<T>(index, 0, 90);

		// Now nudge ours, with the track now full and the queue full of referenda with votes,
		// ours will not be in the queue.
		nudge::<T>(index);
		let track = Referenda::<T>::ensure_ongoing(index).unwrap().track;
		assert!(TrackQueue::<T>::get(&track).into_iter().all(|(i, _)| i != index));

		// Now alter the voting, so that ours goes into pole-position and shifts others down.
		make_passing::<T>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		let t = TrackQueue::<T>::get(&track);
		assert_eq!(t.len() as u32, T::MaxQueued::get());
		assert_eq!(t[t.len() - 1].0, index);
	}

	nudge_referendum_requeued_slide {
		// First create our referendum and place the deposit. It will be failing.
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
		fill_queue::<T>(index, 1, 90);

		// Now nudge ours, with the track now full, ours will be queued, but with no votes, it
		// will have the worst position.
		nudge::<T>(index);
		let track = Referenda::<T>::ensure_ongoing(index).unwrap().track;
		assert_eq!(TrackQueue::<T>::get(&track).len() as u32, T::MaxQueued::get());
		assert_eq!(TrackQueue::<T>::get(&track)[0], (index, 0u32.into()));

		// Now alter the voting, so that ours leap-frogs all into the best position.
		make_passing::<T>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		let t = TrackQueue::<T>::get(&track);
		assert_eq!(t.len() as u32, T::MaxQueued::get());
		assert_eq!(t[t.len() - 1].0, index);
	}

	nudge_referendum_queued {
		// NOTE: worst possible queue situation is with a queue full of passing refs with one slot
		// free and this failing. It would result in `QUEUE_SIZE - 1` items being shifted for the
		// insertion at the beginning.

		// First create our referendum and place the deposit. It will be failing.
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
		fill_queue::<T>(index, 1, 0);

		let track = Referenda::<T>::ensure_ongoing(index).unwrap().track;
		assert_eq!(TrackQueue::<T>::get(&track).len() as u32, T::MaxQueued::get() - 1);
		assert!(TrackQueue::<T>::get(&track).into_iter().all(|(_, v)| v > 0u32.into()));

		// Then nudge ours, with the track now full, ours will be queued.
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		assert_eq!(TrackQueue::<T>::get(&track).len() as u32, T::MaxQueued::get());
		assert_eq!(TrackQueue::<T>::get(&track)[0], (index, 0u32.into()));
	}

	nudge_referendum_not_queued {
		// First create our referendum and place the deposit. It will be failing.
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
		fill_queue::<T>(index, 0, 0);

		let track = Referenda::<T>::ensure_ongoing(index).unwrap().track;
		assert_eq!(TrackQueue::<T>::get(&track).len() as u32, T::MaxQueued::get());
		assert!(TrackQueue::<T>::get(&track).into_iter().all(|(_, v)| v > 0u32.into()));

		// Then nudge ours, with the track now full, ours will be queued.
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		assert_eq!(TrackQueue::<T>::get(&track).len() as u32, T::MaxQueued::get());
		assert!(TrackQueue::<T>::get(&track).into_iter().all(|(i, _)| i != index));
	}

	nudge_referendum_no_deposit {
		let (_caller, index) = create_referendum::<T>();
		skip_prepare_period::<T>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		let status = Referenda::<T>::ensure_ongoing(index).unwrap();
		assert_matches!(status, ReferendumStatus { deciding: None, .. });
	}

	nudge_referendum_preparing {
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		let status = Referenda::<T>::ensure_ongoing(index).unwrap();
		assert_matches!(status, ReferendumStatus { deciding: None, .. });
	}

	nudge_referendum_timed_out {
		let (_caller, index) = create_referendum::<T>();
		skip_timeout_period::<T>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		let info = ReferendumInfoFor::<T>::get(index).unwrap();
		assert_matches!(info, ReferendumInfo::TimedOut(..));
	}

	nudge_referendum_begin_deciding_failing {
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
		skip_prepare_period::<T>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		assert!(is_not_confirming::<T>(index));
	}

	nudge_referendum_begin_deciding_passing {
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
		make_passing::<T>(index);
		skip_prepare_period::<T>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		assert!(is_confirming::<T>(index));
	}

	nudge_referendum_begin_confirming {
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
		skip_prepare_period::<T>(index);
		nudge::<T>(index);
		assert!(!is_confirming::<T>(index));
		make_passing::<T>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		assert!(is_confirming::<T>(index));
	}

	nudge_referendum_end_confirming {
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
		skip_prepare_period::<T>(index);
		make_passing::<T>(index);
		nudge::<T>(index);
		assert!(is_confirming::<T>(index));
		make_failing::<T>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		assert!(!is_confirming::<T>(index));
	}

	nudge_referendum_continue_not_confirming {
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
		skip_prepare_period::<T>(index);
		nudge::<T>(index);
		assert!(!is_confirming::<T>(index));
		let old_alarm = alarm_time::<T>(index);
		make_passing_after::<T>(index, Perbill::from_percent(50));
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		assert_ne!(old_alarm, alarm_time::<T>(index));
		assert!(!is_confirming::<T>(index));
	}

	nudge_referendum_continue_confirming {
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
		make_passing::<T>(index);
		skip_prepare_period::<T>(index);
		nudge::<T>(index);
		assert!(is_confirming::<T>(index));
		let old_alarm = alarm_time::<T>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		assert!(is_confirming::<T>(index));
	}

	nudge_referendum_approved {
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
		skip_prepare_period::<T>(index);
		make_passing::<T>(index);
		nudge::<T>(index);
		skip_confirm_period::<T>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		let info = ReferendumInfoFor::<T>::get(index).unwrap();
		assert_matches!(info, ReferendumInfo::Approved(..));
	}

	nudge_referendum_rejected {
		let (_caller, index) = create_referendum::<T>();
		place_deposit::<T>(index);
		skip_prepare_period::<T>(index);
		nudge::<T>(index);
		skip_decision_period::<T>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		let info = ReferendumInfoFor::<T>::get(index).unwrap();
		assert_matches!(info, ReferendumInfo::Rejected(..));
	}

	impl_benchmark_test_suite!(
		Referenda,
		crate::mock::new_test_ext(),
		crate::mock::Test
	);
}
