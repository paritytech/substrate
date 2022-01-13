use super::super::*;
//  use frame_support::traits::Get;

/// Migrate the locks and vote stake on accounts that have more than their free balance locked.
///
/// This migration addresses a bug were a voter could lock up to their reserved balance + free
/// balance. Since locks are only designed to operate on free balance, this put those affected in a
/// situation where they could increase their free balance but still not be able to use there funds
/// because it is less than the lock.
pub fn migrate<T: Config>() -> Weight {
	let mut weight = 0;

	for (who, mut voter) in Voting::<T>::iter() {
		let free_balance = T::Currency::free_balance(&who);
		let locked = voter.stake;

		weight = T::DbWeight::get().reads(2);

		if locked > free_balance {
			voter.stake = free_balance;
			// we have overlocked
			Voting::<T>::insert(&who, voter);

			let pallet_id = T::PalletId::get();
			T::Currency::remove_lock(pallet_id, &who);
			T::Currency::set_lock(pallet_id, &who, free_balance, WithdrawReasons::all());

			weight = weight.saturating_add(T::DbWeight::get().writes(2));
		}
	}

	weight
}

/// Some checks and information prior to migration. This can be linked to
/// [`frame_support::traits::OnRuntimeUpgrade::pre_upgrade`] for further testing.
pub fn pre_migrate<T: Config>() {
	for (who, voter) in Voting::<T>::iter() {
		let free_balance = T::Currency::free_balance(&who);

		if voter.stake > free_balance {
			log::warn!(
				"pre-migration elections-phragmen: voter({:?}) has more voter stake than free balance",
				who,
			)
		}
	}

	log::info!("pre-migrate elections-phragmen complete");
}

/// Some checks for after migration. This can be linked to
/// [`frame_support::traits::OnRuntimeUpgrade::post_upgrade`] for further testing.
///
/// Panics if anything goes wrong.
pub fn post_migrate<T: crate::Config>() {
	for (who, voter) in Voting::<T>::iter() {
		let free_balance = T::Currency::free_balance(&who);

		assert!(voter.stake < free_balance, "migration should have made locked <= free_balance");
		// Ideally we would also check that the locks and AccountData.misc_frozen where correctly
		// updated, but since both of those are generic we can't do that without further bounding T.
	}

	log::info!("post-migrate elections-phragmen complete");
}
