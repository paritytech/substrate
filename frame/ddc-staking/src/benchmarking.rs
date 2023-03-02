//! DDCStaking pallet benchmarking.

use super::*;
use crate::Pallet as DDCStaking;
use testing_utils::*;

use frame_support::{
	traits::Currency,
	ensure
};
use sp_runtime::{
	traits::{StaticLookup}
};
use sp_std::prelude::*;

pub use frame_benchmarking::{
	account, benchmarks, impl_benchmark_test_suite, whitelist_account, whitelisted_caller,
};
use frame_system::RawOrigin;

const SEED: u32 = 0;

pub fn clear_storages_with_edges<T: Config>(
  n_storages: u32,
  n_edges: u32,
) -> Result<(Vec<<T::Lookup as StaticLookup>::Source>, Vec<<T::Lookup as StaticLookup>::Source>), &'static str> {
	// Clean up any existing state.
	clear_storages_and_edges::<T>();

  // Create new storages
	let mut storages: Vec<<T::Lookup as StaticLookup>::Source> = Vec::with_capacity(n_storages as usize);
	for i in 0..n_storages {
		let (stash, controller) =
			create_stash_controller::<T>(i + SEED, 100)?;
		let storage_prefs =
			StoragePrefs { foo: true };
		DDCStaking::<T>::store(RawOrigin::Signed(controller).into(), storage_prefs)?;
		let stash_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(stash);
		storages.push(stash_lookup);
	}

  // Create new edges
  let mut edges: Vec<<T::Lookup as StaticLookup>::Source> = Vec::with_capacity(n_edges as usize);
	for i in 0..n_edges {
		let (stash, controller) =
			create_stash_controller::<T>(i + SEED, 100)?;
		let edge_prefs =
			EdgePrefs { foo: true };
		DDCStaking::<T>::serve(RawOrigin::Signed(controller).into(), edge_prefs)?;
		let stash_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(stash);
		edges.push(stash_lookup);
	}

	Ok((storages, edges))
}

struct ListScenario<T: Config> {
	/// Stash that is expected to be moved.
	origin_stash1: T::AccountId,
	/// Controller of the Stash that is expected to be moved.
	origin_controller1: T::AccountId,
	dest_weight: BalanceOf<T>,
}

impl<T: Config> ListScenario<T> {
	fn new(origin_weight: BalanceOf<T>) -> Result<Self, &'static str> {
		ensure!(!origin_weight.is_zero(), "origin weight must be greater than 0");

		// burn the entire issuance.
		let i = T::Currency::burn(T::Currency::total_issuance());
		sp_std::mem::forget(i);

		// create accounts with the origin weight

		let (origin_stash1, origin_controller1) = create_stash_controller_with_balance::<T>(
			USER_SEED + 2,
			origin_weight,
		)?;

		let (_origin_stash2, _origin_controller2) = create_stash_controller_with_balance::<T>(
			USER_SEED + 3,
			origin_weight,
		)?;

		// create an account with the worst case destination weight
		let (_dest_stash1, _dest_controller1) = create_stash_controller_with_balance::<T>(
			USER_SEED + 1,
			origin_weight,
		)?;

		Ok(ListScenario { origin_stash1, origin_controller1, dest_weight: origin_weight })
	}
}

const USER_SEED: u32 = 999666;

benchmarks! {
	bond {
		let stash = create_funded_user::<T>("stash", USER_SEED, 100);
		let controller = create_funded_user::<T>("controller", USER_SEED, 100);
		let controller_lookup: <T::Lookup as StaticLookup>::Source
			= T::Lookup::unlookup(controller.clone());
		let amount = T::Currency::minimum_balance() * 10u32.into();
		whitelist_account!(stash);
	}: _(RawOrigin::Signed(stash.clone()), controller_lookup, amount)
	verify {
		assert!(Bonded::<T>::contains_key(stash));
		assert!(Ledger::<T>::contains_key(controller));
	}

	bond_extra {
		// clean up any existing state.
		clear_storages_and_edges::<T>();

		let origin_weight = MinStorageBond::<T>::get().max(T::Currency::minimum_balance());

		// setup the worst case list scenario.

		// the weight the nominator will start at.
		let scenario = ListScenario::<T>::new(origin_weight)?;

		let max_additional = scenario.dest_weight.clone() - origin_weight;

		let stash = scenario.origin_stash1.clone();
		let controller = scenario.origin_controller1.clone();
		let original_bonded: BalanceOf<T>
			= Ledger::<T>::get(&controller).map(|l| l.active).ok_or("ledger not created after")?;

		T::Currency::deposit_into_existing(&stash, max_additional).unwrap();

		whitelist_account!(stash);
	}: _(RawOrigin::Signed(stash), max_additional)
	verify {
		let ledger = Ledger::<T>::get(&controller).ok_or("ledger not created after")?;
		let new_bonded: BalanceOf<T> = ledger.active;
	}

	unbond {
		// clean up any existing state.
		clear_storages_and_edges::<T>();

		// setup the worst case list scenario.
		let total_issuance = T::Currency::total_issuance();
		// the weight the nominator will start at. The value used here is expected to be
		// significantly higher than the first position in a list (e.g. the first bag threshold).
		let origin_weight = BalanceOf::<T>::try_from(952_994_955_240_703u128)
			.map_err(|_| "balance expected to be a u128")
			.unwrap();
		let scenario = ListScenario::<T>::new(origin_weight)?;

		let stash = scenario.origin_stash1.clone();
		let controller = scenario.origin_controller1.clone();
		let amount = origin_weight - scenario.dest_weight.clone();
		let ledger = Ledger::<T>::get(&controller).ok_or("ledger not created before")?;
		let original_bonded: BalanceOf<T> = ledger.active;

		whitelist_account!(controller);
	}: _(RawOrigin::Signed(controller.clone()), amount)
	verify {
		let ledger = Ledger::<T>::get(&controller).ok_or("ledger not created after")?;
		let new_bonded: BalanceOf<T> = ledger.active;
	}

	withdraw_unbonded {
		let (stash, controller) = create_stash_controller::<T>(0, 100)?;
		let amount = T::Currency::minimum_balance() * 5u32.into(); // Half of total
		DDCStaking::<T>::unbond(RawOrigin::Signed(controller.clone()).into(), amount)?;
		CurrentEra::<T>::put(EraIndex::max_value());
		let ledger = Ledger::<T>::get(&controller).ok_or("ledger not created before")?;
		let original_total: BalanceOf<T> = ledger.total;
		whitelist_account!(controller);
	}: _(RawOrigin::Signed(controller.clone()))
	verify {
		let ledger = Ledger::<T>::get(&controller).ok_or("ledger not created after")?;
		let new_total: BalanceOf<T> = ledger.total;
	}

	store {
		let (stash, controller) = create_stash_controller::<T>(0, 100)?;
		// because it is chilled.

		let prefs = StoragePrefs::default();
		whitelist_account!(controller);
	}: _(RawOrigin::Signed(controller), prefs)
	verify {
	}

  serve {
		let (stash, controller) = create_stash_controller::<T>(0, 100)?;
		// because it is chilled.

		let prefs = EdgePrefs::default();
		whitelist_account!(controller);
	}: _(RawOrigin::Signed(controller), prefs)
	verify {
	}

	chill {
		// clean up any existing state.
		clear_storages_and_edges::<T>();

		let origin_weight = MinStorageBond::<T>::get().max(T::Currency::minimum_balance());

		// setup a worst case list scenario. Note that we don't care about the setup of the
		// destination position because we are doing a removal from the list but no insert.
		let scenario = ListScenario::<T>::new(origin_weight)?;
		let controller = scenario.origin_controller1.clone();
		let stash = scenario.origin_stash1.clone();

		whitelist_account!(controller);
	}: _(RawOrigin::Signed(controller))
	verify {
	}

	set_controller {
		let (stash, _) = create_stash_controller::<T>(USER_SEED, 100)?;
		let new_controller = create_funded_user::<T>("new_controller", USER_SEED, 100);
		let new_controller_lookup = T::Lookup::unlookup(new_controller.clone());
		whitelist_account!(stash);
	}: _(RawOrigin::Signed(stash), new_controller_lookup)
	verify {
	}
}

