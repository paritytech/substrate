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

//! Democracy pallet benchmarking.

use super::*;
use crate::Pallet as Referenda;
use assert_matches::assert_matches;
use frame_benchmarking::v1::{
	account, benchmarks_instance_pallet, whitelist_account, BenchmarkError,
};
use frame_support::{
	assert_ok,
	dispatch::UnfilteredDispatchable,
	traits::{Bounded, Currency, EnsureOrigin, EnsureOriginWithArg},
};
use frame_system::RawOrigin;
use sp_runtime::traits::Bounded as ArithBounded;

const SEED: u32 = 0;

fn assert_last_event<T: Config<I>, I: 'static>(generic_event: <T as Config<I>>::RuntimeEvent) {
	frame_system::Pallet::<T>::assert_last_event(generic_event.into());
}

fn funded_account<T: Config<I>, I: 'static>(name: &'static str, index: u32) -> T::AccountId {
	let caller: T::AccountId = account(name, index, SEED);
	T::Currency::make_free_balance_be(&caller, BalanceOf::<T, I>::max_value());
	caller
}

fn dummy_call<T: Config<I>, I: 'static>() -> Bounded<<T as Config<I>>::RuntimeCall> {
	let inner = frame_system::Call::remark { remark: vec![] };
	let call = <T as Config<I>>::RuntimeCall::from(inner);
	T::Preimages::bound(call).unwrap()
}

fn create_referendum<T: Config<I>, I: 'static>(origin: T::RuntimeOrigin) -> ReferendumIndex {
	if let Ok(caller) = frame_system::ensure_signed(origin.clone()) {
		T::Currency::make_free_balance_be(&caller, BalanceOf::<T, I>::max_value());
		whitelist_account!(caller);
	}

	let proposal_origin = Box::new(RawOrigin::Root.into());
	let proposal = dummy_call::<T, I>();
	let enactment_moment = DispatchTime::After(0u32.into());
	let call = crate::Call::<T, I>::submit { proposal_origin, proposal, enactment_moment };
	assert_ok!(call.dispatch_bypass_filter(origin.clone()));
	let index = ReferendumCount::<T, I>::get() - 1;
	index
}

fn place_deposit<T: Config<I>, I: 'static>(index: ReferendumIndex) {
	let caller = funded_account::<T, I>("caller", 0);
	whitelist_account!(caller);
	assert_ok!(Referenda::<T, I>::place_decision_deposit(RawOrigin::Signed(caller).into(), index));
}

fn nudge<T: Config<I>, I: 'static>(index: ReferendumIndex) {
	assert_ok!(Referenda::<T, I>::nudge_referendum(RawOrigin::Root.into(), index));
}

fn fill_queue<T: Config<I>, I: 'static>(
	origin: T::RuntimeOrigin,
	index: ReferendumIndex,
	spaces: u32,
	pass_after: u32,
) -> Vec<ReferendumIndex> {
	// First, create enough other referendums to fill the track.
	let mut others = vec![];
	for _ in 0..info::<T, I>(index).max_deciding {
		let index = create_referendum::<T, I>(origin.clone());
		place_deposit::<T, I>(index);
		others.push(index);
	}

	// We will also need enough referenda which are queued and passing, we want `MaxQueued - 1`
	// in order to force the maximum amount of work to insert ours into the queue.
	for _ in spaces..T::MaxQueued::get() {
		let index = create_referendum::<T, I>(origin.clone());
		place_deposit::<T, I>(index);
		make_passing_after::<T, I>(index, Perbill::from_percent(pass_after));
		others.push(index);
	}

	// Skip to when they can start being decided.
	skip_prepare_period::<T, I>(index);

	// Manually nudge the other referenda first to ensure that they begin.
	others.iter().for_each(|&i| nudge::<T, I>(i));

	others
}

fn info<T: Config<I>, I: 'static>(index: ReferendumIndex) -> &'static TrackInfoOf<T, I> {
	let status = Referenda::<T, I>::ensure_ongoing(index).unwrap();
	T::Tracks::info(status.track).expect("Id value returned from T::Tracks")
}

fn make_passing_after<T: Config<I>, I: 'static>(index: ReferendumIndex, period_portion: Perbill) {
	// We add an extra 1 percent to handle any perbill rounding errors which may cause
	// a proposal to not actually pass.
	let support = info::<T, I>(index)
		.min_support
		.threshold(period_portion)
		.saturating_add(Perbill::from_percent(1));
	let approval = info::<T, I>(index)
		.min_approval
		.threshold(period_portion)
		.saturating_add(Perbill::from_percent(1));
	Referenda::<T, I>::access_poll(index, |status| {
		if let PollStatus::Ongoing(tally, class) = status {
			T::Tally::setup(class, Perbill::from_rational(1u32, 1000u32));
			*tally = T::Tally::from_requirements(support, approval, class);
		}
	});
}

fn make_passing<T: Config<I>, I: 'static>(index: ReferendumIndex) {
	Referenda::<T, I>::access_poll(index, |status| {
		if let PollStatus::Ongoing(tally, class) = status {
			T::Tally::setup(class, Perbill::from_rational(1u32, 1000u32));
			*tally = T::Tally::unanimity(class);
		}
	});
}

fn make_failing<T: Config<I>, I: 'static>(index: ReferendumIndex) {
	Referenda::<T, I>::access_poll(index, |status| {
		if let PollStatus::Ongoing(tally, class) = status {
			T::Tally::setup(class, Perbill::from_rational(1u32, 1000u32));
			*tally = T::Tally::rejection(class);
		}
	});
}

fn skip_prepare_period<T: Config<I>, I: 'static>(index: ReferendumIndex) {
	let status = Referenda::<T, I>::ensure_ongoing(index).unwrap();
	let prepare_period_over = status.submitted + info::<T, I>(index).prepare_period;
	frame_system::Pallet::<T>::set_block_number(prepare_period_over);
}

fn skip_decision_period<T: Config<I>, I: 'static>(index: ReferendumIndex) {
	let status = Referenda::<T, I>::ensure_ongoing(index).unwrap();
	let decision_period_over = status.deciding.unwrap().since + info::<T, I>(index).decision_period;
	frame_system::Pallet::<T>::set_block_number(decision_period_over);
}

fn skip_confirm_period<T: Config<I>, I: 'static>(index: ReferendumIndex) {
	let status = Referenda::<T, I>::ensure_ongoing(index).unwrap();
	let confirm_period_over = status.deciding.unwrap().confirming.unwrap();
	frame_system::Pallet::<T>::set_block_number(confirm_period_over);
}

fn skip_timeout_period<T: Config<I>, I: 'static>(index: ReferendumIndex) {
	let status = Referenda::<T, I>::ensure_ongoing(index).unwrap();
	let timeout_period_over = status.submitted + T::UndecidingTimeout::get();
	frame_system::Pallet::<T>::set_block_number(timeout_period_over);
}

fn alarm_time<T: Config<I>, I: 'static>(index: ReferendumIndex) -> T::BlockNumber {
	let status = Referenda::<T, I>::ensure_ongoing(index).unwrap();
	status.alarm.unwrap().0
}

fn is_confirming<T: Config<I>, I: 'static>(index: ReferendumIndex) -> bool {
	let status = Referenda::<T, I>::ensure_ongoing(index).unwrap();
	matches!(
		status,
		ReferendumStatus { deciding: Some(DecidingStatus { confirming: Some(_), .. }), .. }
	)
}

fn is_not_confirming<T: Config<I>, I: 'static>(index: ReferendumIndex) -> bool {
	let status = Referenda::<T, I>::ensure_ongoing(index).unwrap();
	matches!(
		status,
		ReferendumStatus { deciding: Some(DecidingStatus { confirming: None, .. }), .. }
	)
}

benchmarks_instance_pallet! {
	submit {
		let origin =
			T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into()).map_err(|_| BenchmarkError::Weightless)?;
		if let Ok(caller) = frame_system::ensure_signed(origin.clone()) {
			T::Currency::make_free_balance_be(&caller, BalanceOf::<T, I>::max_value());
			whitelist_account!(caller);
		}
	}: _<T::RuntimeOrigin>(
		origin,
		Box::new(RawOrigin::Root.into()),
		dummy_call::<T, I>(),
		DispatchTime::After(0u32.into())
	) verify {
		let index = ReferendumCount::<T, I>::get().checked_sub(1).unwrap();
		assert_matches!(ReferendumInfoFor::<T, I>::get(index), Some(ReferendumInfo::Ongoing(_)));
	}

	place_decision_deposit_preparing {
		let origin =
			T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into()).map_err(|_| BenchmarkError::Weightless)?;
		let index = create_referendum::<T, I>(origin.clone());
	}: place_decision_deposit<T::RuntimeOrigin>(origin, index)
	verify {
		assert!(Referenda::<T, I>::ensure_ongoing(index).unwrap().decision_deposit.is_some());
	}

	place_decision_deposit_queued {
		let origin =
			T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into()).map_err(|_| BenchmarkError::Weightless)?;
		let index = create_referendum::<T, I>(origin.clone());
		fill_queue::<T, I>(origin.clone(), index, 1, 90);
	}: place_decision_deposit<T::RuntimeOrigin>(origin, index)
	verify {
		let track = Referenda::<T, I>::ensure_ongoing(index).unwrap().track;
		assert_eq!(TrackQueue::<T, I>::get(&track).len() as u32, T::MaxQueued::get());
		assert!(TrackQueue::<T, I>::get(&track).contains(&(index, 0u32.into())));
	}

	place_decision_deposit_not_queued {
		let origin =
			T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into()).map_err(|_| BenchmarkError::Weightless)?;
		let index = create_referendum::<T, I>(origin.clone());
		fill_queue::<T, I>(origin.clone(), index, 0, 90);
		let track = Referenda::<T, I>::ensure_ongoing(index).unwrap().track;
		assert_eq!(TrackQueue::<T, I>::get(&track).len() as u32, T::MaxQueued::get());
		assert!(TrackQueue::<T, I>::get(&track).into_iter().all(|(i, _)| i != index));
	}: place_decision_deposit<T::RuntimeOrigin>(origin, index)
	verify {
		assert_eq!(TrackQueue::<T, I>::get(&track).len() as u32, T::MaxQueued::get());
		assert!(TrackQueue::<T, I>::get(&track).into_iter().all(|(i, _)| i != index));
	}

	place_decision_deposit_passing {
		let origin =
			T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into()).map_err(|_| BenchmarkError::Weightless)?;
		let index = create_referendum::<T, I>(origin.clone());
		skip_prepare_period::<T, I>(index);
		make_passing::<T, I>(index);
	}: place_decision_deposit<T::RuntimeOrigin>(origin, index)
	verify {
		assert!(is_confirming::<T, I>(index));
	}

	place_decision_deposit_failing {
		let origin =
			T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into()).map_err(|_| BenchmarkError::Weightless)?;
		let index = create_referendum::<T, I>(origin.clone());
		skip_prepare_period::<T, I>(index);
	}: place_decision_deposit<T::RuntimeOrigin>(origin, index)
	verify {
		assert!(is_not_confirming::<T, I>(index));
	}

	refund_decision_deposit {
		let origin =
			T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into()).map_err(|_| BenchmarkError::Weightless)?;
		let index = create_referendum::<T, I>(origin.clone());
		place_deposit::<T, I>(index);
		assert_ok!(Referenda::<T, I>::cancel(
			T::CancelOrigin::try_successful_origin()
				.expect("CancelOrigin has no successful origin required for the benchmark"),
			index,
		));
	}: _<T::RuntimeOrigin>(origin, index)
	verify {
		assert_matches!(ReferendumInfoFor::<T, I>::get(index), Some(ReferendumInfo::Cancelled(_, _, None)));
	}

	refund_submission_deposit {
		let origin =
			T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into()).map_err(|_| BenchmarkError::Weightless)?;
		let index = create_referendum::<T, I>(origin.clone());
		let caller = frame_system::ensure_signed(origin.clone()).unwrap();
		let balance = T::Currency::free_balance(&caller);
		assert_ok!(Referenda::<T, I>::cancel(
			T::CancelOrigin::try_successful_origin()
				.expect("CancelOrigin has no successful origin required for the benchmark"),
			index,
		));
		assert_matches!(ReferendumInfoFor::<T, I>::get(index), Some(ReferendumInfo::Cancelled(_, Some(_), _)));
	}: _<T::RuntimeOrigin>(origin, index)
	verify {
		assert_matches!(ReferendumInfoFor::<T, I>::get(index), Some(ReferendumInfo::Cancelled(_, None, _)));
		let new_balance = T::Currency::free_balance(&caller);
		// the deposit is zero or make sure it was unreserved.
		assert!(T::SubmissionDeposit::get().is_zero() || new_balance > balance);
	}

	cancel {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin);
		place_deposit::<T, I>(index);
	}: _<T::RuntimeOrigin>(
		T::CancelOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?,
		index
	) verify {
		assert_matches!(ReferendumInfoFor::<T, I>::get(index), Some(ReferendumInfo::Cancelled(..)));
	}

	kill {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin);
		place_deposit::<T, I>(index);
	}: _<T::RuntimeOrigin>(
		T::KillOrigin::try_successful_origin().map_err(|_| BenchmarkError::Weightless)?,
		index
	) verify {
		assert_matches!(ReferendumInfoFor::<T, I>::get(index), Some(ReferendumInfo::Killed(..)));
	}

	one_fewer_deciding_queue_empty {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin);
		place_deposit::<T, I>(index);
		skip_prepare_period::<T, I>(index);
		nudge::<T, I>(index);
		let track = Referenda::<T, I>::ensure_ongoing(index).unwrap().track;
		assert_ok!(Referenda::<T, I>::cancel(
			T::CancelOrigin::try_successful_origin()
				.expect("CancelOrigin has no successful origin required for the benchmark"),
			index,
		));
		assert_eq!(DecidingCount::<T, I>::get(&track), 1);
	}: one_fewer_deciding(RawOrigin::Root, track)
	verify {
		assert_eq!(DecidingCount::<T, I>::get(&track), 0);
	}

	one_fewer_deciding_failing {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin.clone());
		// No spaces free in the queue.
		let queued = fill_queue::<T, I>(origin, index, 0, 90);
		let track = Referenda::<T, I>::ensure_ongoing(index).unwrap().track;
		assert_ok!(Referenda::<T, I>::cancel(
			T::CancelOrigin::try_successful_origin()
				.expect("CancelOrigin has no successful origin required for the benchmark"),
			queued[0],
		));
		assert_eq!(TrackQueue::<T, I>::get(&track).len() as u32, T::MaxQueued::get());
		let deciding_count = DecidingCount::<T, I>::get(&track);
	}: one_fewer_deciding(RawOrigin::Root, track)
	verify {
		assert_eq!(DecidingCount::<T, I>::get(&track), deciding_count);
		assert_eq!(TrackQueue::<T, I>::get(&track).len() as u32, T::MaxQueued::get() - 1);
		assert!(queued.into_iter().skip(1).all(|i| Referenda::<T, I>::ensure_ongoing(i)
			.unwrap()
			.deciding
			.map_or(true, |d| d.confirming.is_none())
		));
	}

	one_fewer_deciding_passing {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin.clone());
		// No spaces free in the queue.
		let queued = fill_queue::<T, I>(origin, index, 0, 0);
		let track = Referenda::<T, I>::ensure_ongoing(index).unwrap().track;
		assert_ok!(Referenda::<T, I>::cancel(
			T::CancelOrigin::try_successful_origin()
				.expect("CancelOrigin has no successful origin required for the benchmark"),
			queued[0],
		));
		assert_eq!(TrackQueue::<T, I>::get(&track).len() as u32, T::MaxQueued::get());
		let deciding_count = DecidingCount::<T, I>::get(&track);
	}: one_fewer_deciding(RawOrigin::Root, track)
	verify {
		assert_eq!(DecidingCount::<T, I>::get(&track), deciding_count);
		assert_eq!(TrackQueue::<T, I>::get(&track).len() as u32, T::MaxQueued::get() - 1);
		assert!(queued.into_iter().skip(1).filter(|i| Referenda::<T, I>::ensure_ongoing(*i)
			.unwrap()
			.deciding
			.map_or(false, |d| d.confirming.is_some())
		).count() == 1);
	}

	nudge_referendum_requeued_insertion {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		// First create our referendum and place the deposit. It will be failing.
		let index = create_referendum::<T, I>(origin.clone());
		place_deposit::<T, I>(index);
		fill_queue::<T, I>(origin, index, 0, 90);

		// Now nudge ours, with the track now full and the queue full of referenda with votes,
		// ours will not be in the queue.
		nudge::<T, I>(index);
		let track = Referenda::<T, I>::ensure_ongoing(index).unwrap().track;
		assert!(TrackQueue::<T, I>::get(&track).into_iter().all(|(i, _)| i != index));

		// Now alter the voting, so that ours goes into pole-position and shifts others down.
		make_passing::<T, I>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		let t = TrackQueue::<T, I>::get(&track);
		assert_eq!(t.len() as u32, T::MaxQueued::get());
		assert_eq!(t[t.len() - 1].0, index);
	}

	nudge_referendum_requeued_slide {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		// First create our referendum and place the deposit. It will be failing.
		let index = create_referendum::<T, I>(origin.clone());
		place_deposit::<T, I>(index);
		fill_queue::<T, I>(origin, index, 1, 90);

		// Now nudge ours, with the track now full, ours will be queued, but with no votes, it
		// will have the worst position.
		nudge::<T, I>(index);
		let track = Referenda::<T, I>::ensure_ongoing(index).unwrap().track;
		assert_eq!(TrackQueue::<T, I>::get(&track).len() as u32, T::MaxQueued::get());
		assert_eq!(TrackQueue::<T, I>::get(&track)[0], (index, 0u32.into()));

		// Now alter the voting, so that ours leap-frogs all into the best position.
		make_passing::<T, I>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		let t = TrackQueue::<T, I>::get(&track);
		assert_eq!(t.len() as u32, T::MaxQueued::get());
		assert_eq!(t[t.len() - 1].0, index);
	}

	nudge_referendum_queued {
		// NOTE: worst possible queue situation is with a queue full of passing refs with one slot
		// free and this failing. It would result in `QUEUE_SIZE - 1` items being shifted for the
		// insertion at the beginning.

		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		// First create our referendum and place the deposit. It will be failing.
		let index = create_referendum::<T, I>(origin.clone());
		place_deposit::<T, I>(index);
		fill_queue::<T, I>(origin, index, 1, 0);

		let track = Referenda::<T, I>::ensure_ongoing(index).unwrap().track;
		assert_eq!(TrackQueue::<T, I>::get(&track).len() as u32, T::MaxQueued::get() - 1);
		assert!(TrackQueue::<T, I>::get(&track).into_iter().all(|(_, v)| v > 0u32.into()));

		// Then nudge ours, with the track now full, ours will be queued.
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		assert_eq!(TrackQueue::<T, I>::get(&track).len() as u32, T::MaxQueued::get());
		assert_eq!(TrackQueue::<T, I>::get(&track)[0], (index, 0u32.into()));
	}

	nudge_referendum_not_queued {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		// First create our referendum and place the deposit. It will be failing.
		let index = create_referendum::<T, I>(origin.clone());
		place_deposit::<T, I>(index);
		fill_queue::<T, I>(origin, index, 0, 0);

		let track = Referenda::<T, I>::ensure_ongoing(index).unwrap().track;
		assert_eq!(TrackQueue::<T, I>::get(&track).len() as u32, T::MaxQueued::get());
		assert!(TrackQueue::<T, I>::get(&track).into_iter().all(|(_, v)| v > 0u32.into()));

		// Then nudge ours, with the track now full, ours will be queued.
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		assert_eq!(TrackQueue::<T, I>::get(&track).len() as u32, T::MaxQueued::get());
		assert!(TrackQueue::<T, I>::get(&track).into_iter().all(|(i, _)| i != index));
	}

	nudge_referendum_no_deposit {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin);
		skip_prepare_period::<T, I>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		let status = Referenda::<T, I>::ensure_ongoing(index).unwrap();
		assert_matches!(status, ReferendumStatus { deciding: None, .. });
	}

	nudge_referendum_preparing {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin);
		place_deposit::<T, I>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		let status = Referenda::<T, I>::ensure_ongoing(index).unwrap();
		assert_matches!(status, ReferendumStatus { deciding: None, .. });
	}

	nudge_referendum_timed_out {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin);
		skip_timeout_period::<T, I>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		let info = ReferendumInfoFor::<T, I>::get(index).unwrap();
		assert_matches!(info, ReferendumInfo::TimedOut(..));
	}

	nudge_referendum_begin_deciding_failing {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin);
		place_deposit::<T, I>(index);
		skip_prepare_period::<T, I>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		assert!(is_not_confirming::<T, I>(index));
	}

	nudge_referendum_begin_deciding_passing {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin);
		place_deposit::<T, I>(index);
		make_passing::<T, I>(index);
		skip_prepare_period::<T, I>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		assert!(is_confirming::<T, I>(index));
	}

	nudge_referendum_begin_confirming {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin);
		place_deposit::<T, I>(index);
		skip_prepare_period::<T, I>(index);
		nudge::<T, I>(index);
		assert!(!is_confirming::<T, I>(index));
		make_passing::<T, I>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		assert!(is_confirming::<T, I>(index));
	}

	nudge_referendum_end_confirming {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin);
		place_deposit::<T, I>(index);
		skip_prepare_period::<T, I>(index);
		make_passing::<T, I>(index);
		nudge::<T, I>(index);
		assert!(is_confirming::<T, I>(index));
		make_failing::<T, I>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		assert!(!is_confirming::<T, I>(index));
	}

	nudge_referendum_continue_not_confirming {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin);
		place_deposit::<T, I>(index);
		skip_prepare_period::<T, I>(index);
		nudge::<T, I>(index);
		assert!(!is_confirming::<T, I>(index));
		let old_alarm = alarm_time::<T, I>(index);
		make_passing_after::<T, I>(index, Perbill::from_percent(50));
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		assert_ne!(old_alarm, alarm_time::<T, I>(index));
		assert!(!is_confirming::<T, I>(index));
	}

	nudge_referendum_continue_confirming {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin);
		place_deposit::<T, I>(index);
		make_passing::<T, I>(index);
		skip_prepare_period::<T, I>(index);
		nudge::<T, I>(index);
		assert!(is_confirming::<T, I>(index));
		let old_alarm = alarm_time::<T, I>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		assert!(is_confirming::<T, I>(index));
	}

	nudge_referendum_approved {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin);
		place_deposit::<T, I>(index);
		skip_prepare_period::<T, I>(index);
		make_passing::<T, I>(index);
		nudge::<T, I>(index);
		skip_confirm_period::<T, I>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		let info = ReferendumInfoFor::<T, I>::get(index).unwrap();
		assert_matches!(info, ReferendumInfo::Approved(..));
	}

	nudge_referendum_rejected {
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin);
		place_deposit::<T, I>(index);
		skip_prepare_period::<T, I>(index);
		make_failing::<T, I>(index);
		nudge::<T, I>(index);
		skip_decision_period::<T, I>(index);
	}: nudge_referendum(RawOrigin::Root, index)
	verify {
		let info = ReferendumInfoFor::<T, I>::get(index).unwrap();
		assert_matches!(info, ReferendumInfo::Rejected(..));
	}

	set_some_metadata {
		use sp_std::borrow::Cow;
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin.clone());
		let hash = T::Preimages::note(Cow::from(vec![5, 6])).unwrap();
	}: set_metadata<T::RuntimeOrigin>(origin, index, Some(hash))
	verify {
		assert_last_event::<T, I>(Event::MetadataSet { index, hash }.into());
	}

	clear_metadata {
		use sp_std::borrow::Cow;
		let origin = T::SubmitOrigin::try_successful_origin(&RawOrigin::Root.into())
			.expect("SubmitOrigin has no successful origin required for the benchmark");
		let index = create_referendum::<T, I>(origin.clone());
		let hash = T::Preimages::note(Cow::from(vec![6, 7, 8])).unwrap();
		assert_ok!(
			Referenda::<T, I>::set_metadata(origin.clone(), index, Some(hash))
		);
	}: set_metadata<T::RuntimeOrigin>(origin, index, None)
	verify {
		assert_last_event::<T, I>(Event::MetadataCleared { index, hash }.into());
	}

	impl_benchmark_test_suite!(
		Referenda,
		crate::mock::new_test_ext(),
		crate::mock::Test
	);
}
