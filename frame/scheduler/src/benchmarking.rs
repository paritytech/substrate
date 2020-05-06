// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Scheduler pallet benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use super::*;
use sp_std::{vec, prelude::*};
use frame_system::RawOrigin;
use frame_support::{ensure, traits::OnInitialize};
use frame_benchmarking::benchmarks;

use crate::Module as Scheduler;
use frame_system::Module as System;

const MAX_SCHEDULED: u32 = 50;

// Add `n` named items to the schedule
fn fill_schedule<T: Trait> (when: T::BlockNumber, n: u32) -> Result<(), &'static str> {
	// Essentially a no-op call.
	let call = frame_system::Call::set_storage(vec![]);
	for i in 0..n {
		// Named schedule is strictly heavier than anonymous
		Scheduler::<T>::do_schedule_named(
			i.encode(),
			when,
			// Add periodicity
			Some((T::BlockNumber::one(), 100)),
			// HARD_DEADLINE priority means it gets executed no matter what
			0,
			call.clone().into(),
		)?;
	}
	ensure!(Agenda::<T>::get(when).len() == n as usize, "didn't fill schedule");
	Ok(())
}

benchmarks! {
	_ { }

	schedule {
		let s in 0 .. MAX_SCHEDULED;
		let when = T::BlockNumber::one();
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
		let s in 1 .. MAX_SCHEDULED;
		let when: T::BlockNumber = 2.into();

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
		let s in 0 .. MAX_SCHEDULED;
		let id = s.encode();
		let when = T::BlockNumber::one();
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
		let s in 1 .. MAX_SCHEDULED;
		let when = T::BlockNumber::one();

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

	on_initialize {
		let s in 0 .. MAX_SCHEDULED;
		let when = T::BlockNumber::one();
		fill_schedule::<T>(when, s)?;
	}: { Scheduler::<T>::on_initialize(T::BlockNumber::one()); }
	verify {
		assert_eq!(System::<T>::event_count(), s);
		// Next block should have all the schedules again
		ensure!(
			Agenda::<T>::get(when + T::BlockNumber::one()).len() == s as usize,
			"didn't append schedule"
		);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::tests::{new_test_ext, Test};
	use frame_support::assert_ok;

	#[test]
	fn test_benchmarks() {
		new_test_ext().execute_with(|| {
			assert_ok!(test_benchmark_schedule::<Test>());
			assert_ok!(test_benchmark_cancel::<Test>());
			assert_ok!(test_benchmark_schedule_named::<Test>());
			assert_ok!(test_benchmark_cancel_named::<Test>());
			assert_ok!(test_benchmark_on_initialize::<Test>());
		});
	}
}
