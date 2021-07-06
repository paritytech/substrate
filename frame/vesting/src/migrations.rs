// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

//! Storage migrations for the vesting pallet.

use super::*;

// Migration from single schedule to multiple schedules.
pub(crate) mod v1 {
	use super::*;

	#[cfg(feature = "try-runtime")]
	pub(crate) fn pre_migrate<T: Config>() -> Result<(), &'static str> {
		assert!(StorageVersion::<T>::get() == Releases::V0, "Storage version too high.");

		log::debug!(
			target: LOG_TARGET,
			"Vesting storage version v1 PRE migration checks succesful!"
		);

		Ok(())
	}

	/// Migrate from single schedule to multi schedule storage
	pub(crate) fn migrate<T: Config>() -> Weight {
		let mut reads_writes = 0;

		Vesting::<T>::translate::<VestingInfo<BalanceOf<T>, T::BlockNumber>, _>(
			|_key, vesting_info| {
				reads_writes += 1;
				let v: Option<
					BoundedVec<VestingInfo<BalanceOf<T>, T::BlockNumber>, T::MaxVestingSchedules>,
				> = vec![vesting_info].try_into().ok();

				v
			},
		);

		T::DbWeight::get().reads_writes(reads_writes, reads_writes)
	}

	#[cfg(feature = "try-runtime")]
	pub(crate) fn post_migrate<T: Config>() -> Result<(), &'static str> {
		assert_eq!(StorageVersion::<T>::get(), Releases::V1);

		for (_key, schedules) in Vesting::<T>::iter() {
			// Assert the new bound vec respects size.
			assert!(schedules.len() > 0, "A bounded vec with no items was created.");
			assert!(
				schedules.len() <= T::MaxVestingSchedules::get() as usize,
				"A bounded vec with too many items was created."
			);

			for s in schedules {
				// Check for infinite schedules.
				assert!(s.per_block() > Zero::zero(), "A schedule with per_block of 0 exists");
				// It is ok if this does not pass, but ideally pre-existing schedules would pass
				// this validation logic so we can be more confident about edge cases.
				debug_assert!(
					s.validate::<T::BlockNumberToBalance, T>().is_ok(),
					"A schedule does not pass new validation logic"
				);
			}
		}

		log::debug!(
			target: LOG_TARGET,
			"Vesting storage version v1 POST migration checks succesful!"
		);
		Ok(())
	}
}
