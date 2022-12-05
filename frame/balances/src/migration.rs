// Copyright 2017-2020 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

use super::*;
use frame_support::{
	pallet_prelude::*,
	traits::{OnRuntimeUpgrade, PalletInfoAccess},
	weights::Weight,
};

fn migrate_v0_to_v1<T: Config<I>, I: 'static>(accounts: &[T::AccountId]) -> Weight {
	let onchain_version = Pallet::<T, I>::on_chain_storage_version();

	if onchain_version == 0 {
		let total = accounts
			.iter()
			.map(|a| Pallet::<T, I>::total_balance(a))
			.fold(T::Balance::zero(), |a, e| a.saturating_add(e));
		Pallet::<T, I>::deactivate(total);

		// Remove the old `StorageVersion` type.
		frame_support::storage::unhashed::kill(&frame_support::storage::storage_prefix(
			Pallet::<T, I>::name().as_bytes(),
			"StorageVersion".as_bytes(),
		));

		// Set storage version to `1`.
		StorageVersion::new(1).put::<Pallet<T, I>>();

		log::info!(target: "runtime::balances", "Storage to version 1");
		T::DbWeight::get().reads_writes(2 + accounts.len() as u64, 3)
	} else {
		log::info!(target: "runtime::balances",  "Migration did not execute. This probably should be removed");
		T::DbWeight::get().reads(1)
	}
}

// NOTE: This must be used alongside the account whose balance is expected to be inactive.
// Generally this will be used for the XCM teleport checking account.
pub struct MigrateToTrackInactive<T, A, I = ()>(PhantomData<(T, A, I)>);
impl<T: Config<I>, A: Get<T::AccountId>, I: 'static> OnRuntimeUpgrade
	for MigrateToTrackInactive<T, A, I>
{
	fn on_runtime_upgrade() -> Weight {
		migrate_v0_to_v1::<T, I>(&[A::get()])
	}
}

// NOTE: This must be used alongside the accounts whose balance is expected to be inactive.
// Generally this will be used for the XCM teleport checking accounts.
pub struct MigrateManyToTrackInactive<T, A, I = ()>(PhantomData<(T, A, I)>);
impl<T: Config<I>, A: Get<Vec<T::AccountId>>, I: 'static> OnRuntimeUpgrade
	for MigrateManyToTrackInactive<T, A, I>
{
	fn on_runtime_upgrade() -> Weight {
		migrate_v0_to_v1::<T, I>(&A::get())
	}
}
