use super::super::*;

/// Migrate the locks and vote stake on accounts (as specified with param `to_migrate`) that have
/// more than their free balance locked.
///
/// This migration addresses a bug were a voter could lock up to their reserved balance + free
/// balance. Since locks are only designed to operate on free balance, this put those affected in a
/// situation where they could increase their free balance but still not be able to use their funds
/// because they were less than the lock.
pub fn migrate<T: Config>(to_migrate: Vec<T::AccountId>) -> Weight {
	let mut weight = 0;

	for who in to_migrate.iter() {
		if let Ok(mut voter) = Voting::<T>::try_get(who) {
			let free_balance = T::Currency::free_balance(&who);

			weight = weight.saturating_add(T::DbWeight::get().reads(2));

			if voter.stake > free_balance {
				voter.stake = free_balance;
				Voting::<T>::insert(&who, voter);

				let pallet_id = T::PalletId::get();
				T::Currency::set_lock(pallet_id, &who, free_balance, WithdrawReasons::all());

				weight = weight.saturating_add(T::DbWeight::get().writes(2));
			}
		}
	}

	weight
}

/// Given the list of voters to migrate return a function that does some checks and information
/// prior to migration. This can be linked to [`frame_support::traits::OnRuntimeUpgrade::
/// pre_upgrade`] for further testing.
pub fn pre_migrate_fn<T: Config>(to_migrate: Vec<T::AccountId>) -> Box<dyn Fn() -> ()> {
	Box::new(move || {
		for who in to_migrate.iter() {
			if let Ok(voter) = Voting::<T>::try_get(who) {
				let free_balance = T::Currency::free_balance(&who);

				if voter.stake > free_balance {
					// all good
				} else {
					log::warn!("pre-migrate elections-phragmen: voter={:?} has less stake then free balance", who);
				}
			} else {
				log::warn!("pre-migrate elections-phragmen: cannot find voter={:?}", who);
			}
		}
		log::info!("pre-migrate elections-phragmen complete");
	})
}

/// Some checks for after migration. This can be linked to
/// [`frame_support::traits::OnRuntimeUpgrade::post_upgrade`] for further testing.
///
/// Panics if anything goes wrong.
pub fn post_migrate<T: crate::Config>() {
	for (who, voter) in Voting::<T>::iter() {
		let free_balance = T::Currency::free_balance(&who);

		assert!(voter.stake <= free_balance, "migration should have made locked <= free_balance");
		// Ideally we would also check that the locks and AccountData.misc_frozen where correctly
		// updated, but since both of those are generic we can't do that without further bounding T.
	}

	log::info!("post-migrate elections-phragmen complete");
}
