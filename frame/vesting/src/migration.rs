//! Storage migrations for the vesting pallet.

use super::*;

// Migration from single schedule to multiple schedules.
pub(crate) mod v1 {
	use super::*;

	#[cfg(feature = "try-runtime")]
	pub(crate) fn pre_migrate<T: pallet::Config>() {
		assert!(!StorageVersion::get());
		for (key, schedule) in pallet::Vesting::<T>::iter_values() {
			// Log the key so we can track down a failure below.
			log::debug!(target: LOG_Target, "[pre_migrate] Vesting key {}", key);
			// Check for infinite schedules.
			assert!(schedule.per_block() > 0);
		}
		log::info!(target: LOG_TARGET, "pre migration checks succesful")
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
	pub(crate) fn post_migrate<T: pallet::Config>() {
		assert_eq!(StorageVersion::get(), Release::V1);

		for (key, schedules) in pallet::Vesting::<T>::iter_values() {
			log::debug!(target: LOG_TARGET, "[post_migrate] Vesting key {}", key);
			// Assert the new bound vec respects size.
			assert!(schedules.len() > 0);
			assert!(schedules.len() <= T::MaxVestingSchedules::get() as usize);

			for s in schedules {
				// Check for infinite schedules
				assert!(s.per_block() > 0);
			}
		}
		log::info!(target: LOG_TARGET, "post migration checks succesful")
	}
}
