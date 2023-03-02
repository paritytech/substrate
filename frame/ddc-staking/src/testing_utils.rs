//! Testing utils for ddc-staking. 

use crate::{Pallet as DDCStaking, *};
use frame_benchmarking::account;
use frame_system::RawOrigin;

use frame_support::traits::Currency;
use sp_runtime::{traits::StaticLookup};
use sp_std::prelude::*;

const SEED: u32 = 0;

/// This function removes all storage and edge nodes from storage.
pub fn clear_storages_and_edges<T: Config>() {
	Storages::<T>::remove_all();
	Edges::<T>::remove_all();
}

/// Grab a funded user.
pub fn create_funded_user<T: Config>(
	string: &'static str,
	n: u32,
	balance_factor: u32,
) -> T::AccountId {
	let user = account(string, n, SEED);
	let balance = T::Currency::minimum_balance() * balance_factor.into();
	let _ = T::Currency::make_free_balance_be(&user, balance);
	user
}

/// Grab a funded user with max Balance.
pub fn create_funded_user_with_balance<T: Config>(
	string: &'static str,
	n: u32,
	balance: BalanceOf<T>,
) -> T::AccountId {
	let user = account(string, n, SEED);
	let _ = T::Currency::make_free_balance_be(&user, balance);
	user
}

/// Create a stash and controller pair.
pub fn create_stash_controller<T: Config>(
	n: u32,
	balance_factor: u32,
) -> Result<(T::AccountId, T::AccountId), &'static str> {
	let stash = create_funded_user::<T>("stash", n, balance_factor);
	let controller = create_funded_user::<T>("controller", n, balance_factor);
	let controller_lookup: <T::Lookup as StaticLookup>::Source =
		T::Lookup::unlookup(controller.clone());
	let amount = T::Currency::minimum_balance() * (balance_factor / 10).max(1).into();
	DDCStaking::<T>::bond(
		RawOrigin::Signed(stash.clone()).into(),
		controller_lookup,
		amount,
	)?;
	return Ok((stash, controller))
}

/// Create a stash and controller pair with fixed balance.
pub fn create_stash_controller_with_balance<T: Config>(
	n: u32,
	balance: crate::BalanceOf<T>,
) -> Result<(T::AccountId, T::AccountId), &'static str> {
	let stash = create_funded_user_with_balance::<T>("stash", n, balance);
	let controller = create_funded_user_with_balance::<T>("controller", n, balance);
	let controller_lookup: <T::Lookup as StaticLookup>::Source =
		T::Lookup::unlookup(controller.clone());

	DDCStaking::<T>::bond(
		RawOrigin::Signed(stash.clone()).into(),
		controller_lookup,
		balance,
	)?;
	Ok((stash, controller))
}

/// Create a stash and controller pair, where the controller is dead, and payouts go to controller.
/// This is used to test worst case payout scenarios.
pub fn create_stash_and_dead_controller<T: Config>(
	n: u32,
	balance_factor: u32,
) -> Result<(T::AccountId, T::AccountId), &'static str> {
	let stash = create_funded_user::<T>("stash", n, balance_factor);
	// controller has no funds
	let controller = create_funded_user::<T>("controller", n, 0);
	let controller_lookup: <T::Lookup as StaticLookup>::Source =
		T::Lookup::unlookup(controller.clone());
	let amount = T::Currency::minimum_balance() * (balance_factor / 10).max(1).into();
	DDCStaking::<T>::bond(
		RawOrigin::Signed(stash.clone()).into(),
		controller_lookup,
		amount,
	)?;
	return Ok((stash, controller))
}

/// create `max` validators.
pub fn create_storages<T: Config>(
	max: u32,
	balance_factor: u32,
) -> Result<Vec<<T::Lookup as StaticLookup>::Source>, &'static str> {
	create_storages_with_seed::<T>(max, balance_factor, 0)
}

/// create `max` storages, with a seed to help unintentional prevent account collisions.
pub fn create_storages_with_seed<T: Config>(
	max: u32,
	balance_factor: u32,
	seed: u32,
) -> Result<Vec<<T::Lookup as StaticLookup>::Source>, &'static str> {
	let mut storages: Vec<<T::Lookup as StaticLookup>::Source> = Vec::with_capacity(max as usize);
	for i in 0..max {
		let (stash, controller) =
			create_stash_controller::<T>(i + seed, balance_factor)?;
		let storage_prefs =
			StoragePrefs { foo: true };
		DDCStaking::<T>::store(RawOrigin::Signed(controller).into(), storage_prefs)?;
		let stash_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(stash);
		storages.push(stash_lookup);
	}
	Ok(storages)
}

/// create `max` validators.
pub fn create_edges<T: Config>(
	max: u32,
	balance_factor: u32,
) -> Result<Vec<<T::Lookup as StaticLookup>::Source>, &'static str> {
	create_edges_with_seed::<T>(max, balance_factor, 0)
}

/// create `max` storages, with a seed to help unintentional prevent account collisions.
pub fn create_edges_with_seed<T: Config>(
	max: u32,
	balance_factor: u32,
	seed: u32,
) -> Result<Vec<<T::Lookup as StaticLookup>::Source>, &'static str> {
	let mut edges: Vec<<T::Lookup as StaticLookup>::Source> = Vec::with_capacity(max as usize);
	for i in 0..max {
		let (stash, controller) =
			create_stash_controller::<T>(i + seed, balance_factor)?;
		let edge_prefs =
			EdgePrefs { foo: true };
		DDCStaking::<T>::serve(RawOrigin::Signed(controller).into(), edge_prefs)?;
		let stash_lookup: <T::Lookup as StaticLookup>::Source = T::Lookup::unlookup(stash);
		edges.push(stash_lookup);
	}
	Ok(edges)
}

/// get the current era.
pub fn current_era<T: Config>() -> EraIndex {
	<Pallet<T>>::current_era().unwrap_or(0)
}
