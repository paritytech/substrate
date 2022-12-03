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
use frame_support::{pallet_prelude::*, traits::OnRuntimeUpgrade, weights::Weight};

// NOTE: This must be used alongside the account whose balance is expected to be inactive.
// Generally this will be used for the XCM teleport checking account.
pub struct MigrateToTrackInactive<T, A>(PhantomData<(T, A)>);
impl<T: Config, A: Get<T::AccountId>> OnRuntimeUpgrade for MigrateToTrackInactive<T, A> {
	fn on_runtime_upgrade() -> Weight {
		let current_version = Pallet::<T>::current_storage_version();
		let onchain_version = Pallet::<T>::on_chain_storage_version();

		if onchain_version == 0 && current_version == 1 {
			let b = Pallet::<T>::total_balance(&A::get());
			Pallet::<T>::deactivate(b);
			current_version.put::<Pallet<T>>();
			log::info!(target: "runtime::balances", "Storage to version {:?}", current_version);
			T::DbWeight::get().reads_writes(4, 3)
		} else {
			log::info!(target: "runtime::balances",  "Migration did not execute. This probably should be removed");
			T::DbWeight::get().reads(2)
		}
	}
}

// NOTE: This must be used alongside the account whose balance is expected to be inactive.
// Generally this will be used for the XCM teleport checking account.
pub struct MigrateManyToTrackInactive<T, A>(PhantomData<(T, A)>);
impl<T: Config, A: Get<Vec<T::AccountId>>> OnRuntimeUpgrade for MigrateManyToTrackInactive<T, A> {
	fn on_runtime_upgrade() -> Weight {
		let current_version = Pallet::<T>::current_storage_version();
		let onchain_version = Pallet::<T>::on_chain_storage_version();

		if onchain_version == 0 && current_version == 1 {
			let accounts = A::get();
			let total = accounts
				.iter()
				.map(|a| Pallet::<T>::total_balance(a))
				.fold(T::Balance::zero(), |a, e| a.saturating_add(e));
			Pallet::<T>::deactivate(total);
			current_version.put::<Pallet<T>>();
			log::info!(target: "runtime::balances", "Storage to version {:?}", current_version);
			T::DbWeight::get().reads_writes(3 + accounts.len() as u64, 3)
		} else {
			log::info!(target: "runtime::balances",  "Migration did not execute. This probably should be removed");
			T::DbWeight::get().reads(2)
		}
	}
}
