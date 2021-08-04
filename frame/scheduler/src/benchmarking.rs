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

//! Scheduler pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use frame_benchmarking::{benchmarks, impl_benchmark_test_suite};
use frame_support::{ensure, traits::OnInitialize};
use frame_system::RawOrigin;
use sp_std::{prelude::*, vec};

use crate::Pallet as Scheduler;
use frame_system::Pallet as System;

const BLOCK_NUMBER: u32 = 2;

// Add `n` named items to the schedule
fn fill_schedule<T: Config>(when: T::BlockNumber, n: u32) -> Result<(), &'static str> {
	// Essentially a no-op call.
	let call = frame_system::Call::set_storage(vec![]);
	for i in 0..n {
		// Named schedule is strictly heavier than anonymous
		Scheduler::<T>::do_schedule_named(
			i.encode(),
			DispatchTime::At(when),
			// Add periodicity
			Some((T::BlockNumber::one(), 100)),
			// HARD_DEADLINE priority means it gets executed no matter what
			0,
			frame_system::RawOrigin::Root.into(),
			call.clone().into(),
		)?;
	}
	ensure!(Agenda::<T>::get(when).len() == n as usize, "didn't fill schedule");
	Ok(())
}

benchmarks! {
	schedule {
		let s in 0 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();
		let periodic = Some((T::BlockNumber::one(), 100));
		let priority = 0;
		// Essentially a no-op call.
		let call = Box::new(frame_system::Call::set_storage(vec![]).into());

		fill_schedule::<T>(when, s)?;
	}: _(RawOrigin::Root, when, periodic, priority, call)
	verify {
		ensure!(
			Agenda::<T>::get(when).len() == (s + 1) as usize,
			"didn't add to schedule"
		);
	}

	cancel {
		let s in 1 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();

		fill_schedule::<T>(when, s)?;
		assert_eq!(Agenda::<T>::get(when).len(), s as usize);
	}: _(RawOrigin::Root, when, 0)
	verify {
		ensure!(
			Lookup::<T>::get(0.encode()).is_none(),
			"didn't remove from lookup"
		);
		// Removed schedule is NONE
		ensure!(
			Agenda::<T>::get(when)[0].is_none(),
			"didn't remove from schedule"
		);
	}

	schedule_named {
		let s in 0 .. T::MaxScheduledPerBlock::get();
		let id = s.encode();
		let when = BLOCK_NUMBER.into();
		let periodic = Some((T::BlockNumber::one(), 100));
		let priority = 0;
		// Essentially a no-op call.
		let call = Box::new(frame_system::Call::set_storage(vec![]).into());

		fill_schedule::<T>(when, s)?;
	}: _(RawOrigin::Root, id, when, periodic, priority, call)
	verify {
		ensure!(
			Agenda::<T>::get(when).len() == (s + 1) as usize,
			"didn't add to schedule"
		);
	}

	cancel_named {
		let s in 1 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();

		fill_schedule::<T>(when, s)?;
	}: _(RawOrigin::Root, 0.encode())
	verify {
		ensure!(
			Lookup::<T>::get(0.encode()).is_none(),
			"didn't remove from lookup"
		);
		// Removed schedule is NONE
		ensure!(
			Agenda::<T>::get(when)[0].is_none(),
			"didn't remove from schedule"
		);
	}

	// TODO [#7141]: Make this more complex and flexible so it can be used in automation.
	#[extra]
	on_initialize {
		let s in 0 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();
		fill_schedule::<T>(when, s)?;
	}: { Scheduler::<T>::on_initialize(BLOCK_NUMBER.into()); }
	verify {
		assert_eq!(System::<T>::event_count(), s);
		// Next block should have all the schedules again
		ensure!(
			Agenda::<T>::get(when + T::BlockNumber::one()).len() == s as usize,
			"didn't append schedule"
		);
	}
}

impl_benchmark_test_suite!(Scheduler, crate::tests::new_test_ext(), crate::tests::Test);
