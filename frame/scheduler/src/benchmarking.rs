// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use super::*;
use frame_benchmarking::benchmarks;
use frame_support::{
	ensure,
	traits::{OnInitialize, PreimageProvider, PreimageRecipient},
};
use sp_runtime::traits::Hash;
use sp_std::{prelude::*, vec};

use crate::Pallet as Scheduler;
use frame_system::Pallet as System;

const BLOCK_NUMBER: u32 = 2;

type SystemOrigin<T> = <T as frame_system::Config>::RuntimeOrigin;

/// Add `n` named items to the schedule.
///
/// For `resolved`:
/// - `None`: aborted (hash without preimage)
/// - `Some(true)`: hash resolves into call if possible, plain call otherwise
/// - `Some(false)`: plain call
fn fill_schedule<T: Config>(
	when: T::BlockNumber,
	n: u32,
	periodic: bool,
	named: bool,
	resolved: Option<bool>,
) -> Result<(), &'static str> {
	for i in 0..n {
		// Named schedule is strictly heavier than anonymous
		let (call, hash) = call_and_hash::<T>(i);
		let call_or_hash = match resolved {
			Some(true) => {
				T::PreimageProvider::note_preimage(call.encode().try_into().unwrap());
				if T::PreimageProvider::have_preimage(&hash) {
					CallOrHashOf::<T>::Hash(hash)
				} else {
					call.into()
				}
			},
			Some(false) => call.into(),
			None => CallOrHashOf::<T>::Hash(hash),
		};
		let period = match periodic {
			true => Some(((i + 100).into(), 100)),
			false => None,
		};
		let t = DispatchTime::At(when);
		let origin = frame_system::RawOrigin::Root.into();
		if named {
			Scheduler::<T>::do_schedule_named(i.encode(), t, period, 0, origin, call_or_hash)?;
		} else {
			Scheduler::<T>::do_schedule(t, period, 0, origin, call_or_hash)?;
		}
	}
	ensure!(Agenda::<T>::get(when).len() == n as usize, "didn't fill schedule");
	Ok(())
}

fn call_and_hash<T: Config>(i: u32) -> (<T as Config>::RuntimeCall, T::Hash) {
	// Essentially a no-op call.
	let call: <T as Config>::RuntimeCall = frame_system::Call::remark { remark: i.encode() }.into();
	let hash = T::Hashing::hash_of(&call);
	(call, hash)
}

benchmarks! {
	on_initialize_periodic_named_resolved {
		let s in 1 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();
		fill_schedule::<T>(when, s, true, true, Some(true))?;
	}: { Scheduler::<T>::on_initialize(BLOCK_NUMBER.into()); }
	verify {
		assert_eq!(System::<T>::event_count(), s * 2);
		for i in 0..s {
			assert_eq!(Agenda::<T>::get(when + (i + 100).into()).len(), 1 as usize);
		}
	}

	on_initialize_named_resolved {
		let s in 1 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();
		fill_schedule::<T>(when, s, false, true, Some(true))?;
	}: { Scheduler::<T>::on_initialize(BLOCK_NUMBER.into()); }
	verify {
		assert_eq!(System::<T>::event_count(), s * 2);
		assert!(Agenda::<T>::iter().count() == 0);
	}

	on_initialize_periodic_resolved {
		let s in 1 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();
		fill_schedule::<T>(when, s, true, false, Some(true))?;
	}: { Scheduler::<T>::on_initialize(BLOCK_NUMBER.into()); }
	verify {
		assert_eq!(System::<T>::event_count(), s * 2);
		for i in 0..s {
			assert_eq!(Agenda::<T>::get(when + (i + 100).into()).len(), 1 as usize);
		}
	}

	on_initialize_resolved {
		let s in 1 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();
		fill_schedule::<T>(when, s, false, false, Some(true))?;
	}: { Scheduler::<T>::on_initialize(BLOCK_NUMBER.into()); }
	verify {
		assert_eq!(System::<T>::event_count(), s * 2);
		assert!(Agenda::<T>::iter().count() == 0);
	}

	on_initialize_named_aborted {
		let s in 1 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();
		fill_schedule::<T>(when, s, false, true, None)?;
	}: { Scheduler::<T>::on_initialize(BLOCK_NUMBER.into()); }
	verify {
		assert_eq!(System::<T>::event_count(), 0);
		if let Some(delay) = T::NoPreimagePostponement::get() {
			assert_eq!(Agenda::<T>::get(when + delay).len(), s as usize);
		} else {
			assert!(Agenda::<T>::iter().count() == 0);
		}
	}

	on_initialize_aborted {
		let s in 1 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();
		fill_schedule::<T>(when, s, false, false, None)?;
	}: { Scheduler::<T>::on_initialize(BLOCK_NUMBER.into()); }
	verify {
		assert_eq!(System::<T>::event_count(), 0);
		if let Some(delay) = T::NoPreimagePostponement::get() {
			assert_eq!(Agenda::<T>::get(when + delay).len(), s as usize);
		} else {
			assert!(Agenda::<T>::iter().count() == 0);
		}
	}

	on_initialize_periodic_named {
		let s in 1 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();
		fill_schedule::<T>(when, s, true, true, Some(false))?;
	}: { Scheduler::<T>::on_initialize(BLOCK_NUMBER.into()); }
	verify {
		assert_eq!(System::<T>::event_count(), s);
		for i in 0..s {
			assert_eq!(Agenda::<T>::get(when + (i + 100).into()).len(), 1 as usize);
		}
	}

	on_initialize_periodic {
		let s in 1 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();
		fill_schedule::<T>(when, s, true, false, Some(false))?;
	}: { Scheduler::<T>::on_initialize(when); }
	verify {
		assert_eq!(System::<T>::event_count(), s);
		for i in 0..s {
			assert_eq!(Agenda::<T>::get(when + (i + 100).into()).len(), 1 as usize);
		}
	}

	on_initialize_named {
		let s in 1 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();
		fill_schedule::<T>(when, s, false, true, Some(false))?;
	}: { Scheduler::<T>::on_initialize(BLOCK_NUMBER.into()); }
	verify {
		assert_eq!(System::<T>::event_count(), s);
		assert!(Agenda::<T>::iter().count() == 0);
	}

	on_initialize {
		let s in 1 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();
		fill_schedule::<T>(when, s, false, false, Some(false))?;
	}: { Scheduler::<T>::on_initialize(BLOCK_NUMBER.into()); }
	verify {
		assert_eq!(System::<T>::event_count(), s);
		assert!(Agenda::<T>::iter().count() == 0);
	}

	schedule {
		let s in 0 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();
		let periodic = Some((T::BlockNumber::one(), 100));
		let priority = 0;
		// Essentially a no-op call.
		let inner_call = frame_system::Call::set_storage { items: vec![] }.into();
		let call = Box::new(CallOrHashOf::<T>::Value(inner_call));

		fill_schedule::<T>(when, s, true, true, Some(false))?;
		let schedule_origin = T::ScheduleOrigin::successful_origin();
	}: _<SystemOrigin<T>>(schedule_origin, when, periodic, priority, call)
	verify {
		ensure!(
			Agenda::<T>::get(when).len() == (s + 1) as usize,
			"didn't add to schedule"
		);
	}

	cancel {
		let s in 1 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();

		fill_schedule::<T>(when, s, true, true, Some(false))?;
		assert_eq!(Agenda::<T>::get(when).len(), s as usize);
		let schedule_origin = T::ScheduleOrigin::successful_origin();
	}: _<SystemOrigin<T>>(schedule_origin, when, 0)
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
		let inner_call = frame_system::Call::set_storage { items: vec![] }.into();
		let call = Box::new(CallOrHashOf::<T>::Value(inner_call));

		fill_schedule::<T>(when, s, true, true, Some(false))?;
		let schedule_origin = T::ScheduleOrigin::successful_origin();
	}: _<SystemOrigin<T>>(schedule_origin, id, when, periodic, priority, call)
	verify {
		ensure!(
			Agenda::<T>::get(when).len() == (s + 1) as usize,
			"didn't add to schedule"
		);
	}

	cancel_named {
		let s in 1 .. T::MaxScheduledPerBlock::get();
		let when = BLOCK_NUMBER.into();

		fill_schedule::<T>(when, s, true, true, Some(false))?;
		let schedule_origin = T::ScheduleOrigin::successful_origin();
	}: _<SystemOrigin<T>>(schedule_origin, 0.encode())
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

	impl_benchmark_test_suite!(Scheduler, crate::mock::new_test_ext(), crate::mock::Test);
}
