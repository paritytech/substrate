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

//! Migration code to update storage.

use super::*;
use frame_support::storage::migration::{put_storage_value, take_storage_value, StorageIterator};

pub fn on_runtime_upgrade<T: Trait>() {
	change_name_sudo_to_identity::<T>()
}

// Change the storage name used by this pallet from `Sudo` to `Identity`.
//
// Since the format of the storage items themselves have not changed, we do not
// need to keep track of a storage version. If the runtime does not need to be
// upgraded, nothing here will happen anyway.

fn change_name_sudo_to_identity<T: Trait>() {
	sp_runtime::print("Migrating Identity.");

	for (hash, identity_of) in StorageIterator::<Registration<BalanceOf<T>>>::new(b"Sudo", b"IdentityOf").drain() {
		put_storage_value(b"Identity", b"IdentityOf", &hash, identity_of);
	}

	for (hash, super_of) in StorageIterator::<(T::AccountId, Data)>::new(b"Sudo", b"SuperOf").drain() {
		put_storage_value(b"Identity", b"SuperOf", &hash, super_of);
	}

	for (hash, subs_of) in StorageIterator::<(BalanceOf<T>, Vec<T::AccountId>)>::new(b"Sudo", b"SubsOf").drain() {
		put_storage_value(b"Identity", b"SubsOf", &hash, subs_of);
	}

	if let Some(registrars) = take_storage_value::<Vec<Option<RegistrarInfo<BalanceOf<T>, T::AccountId>>>>(b"Sudo", b"Registrars", &[]) {
		put_storage_value(b"Identity", b"Registrars", &[], registrars);
	}

	sp_runtime::print("Done Identity.");
}
