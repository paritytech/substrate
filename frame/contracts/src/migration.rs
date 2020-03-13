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
	change_name_contract_to_contracts::<T>()
}

// Change the storage name used by this pallet from `Contract` to `Contracts`.
//
// Since the format of the storage items themselves have not changed, we do not
// need to keep track of a storage version. If the runtime does not need to be
// upgraded, nothing here will happen anyway.

fn change_name_contract_to_contracts<T: Trait>() {
	sp_runtime::print("Migrating Contracts.");

	if let Some(gas_spent) = take_storage_value::<Gas>(b"Contract", b"GasSpent", &[]) {
		put_storage_value(b"Contracts", b"GasSpent", &[], gas_spent);
	}

	if let Some(current_schedule) = take_storage_value::<Schedule>(b"Contract", b"CurrentSchedule", &[]) {
		put_storage_value(b"Contracts", b"CurrentSchedule", &[], current_schedule);
	}

	for (hash, pristine_code) in StorageIterator::<Vec<u8>>::new(b"Contract", b"PristineCode").drain() {
		put_storage_value(b"Contracts", b"PristineCode", &hash, pristine_code);
	}

	for (hash, code_storage) in StorageIterator::<wasm::PrefabWasmModule>::new(b"Contract", b"CodeStorage").drain() {
		put_storage_value(b"Contracts", b"CodeStorage", &hash, code_storage);
	}

	if let Some(current_schedule) = take_storage_value::<u64>(b"Contract", b"AccountCounter", &[]) {
		put_storage_value(b"Contracts", b"AccountCounter", &[], current_schedule);
	}

	for (hash, contract_info_of) in StorageIterator::<ContractInfo<T>>::new(b"Contract", b"ContractInfoOf").drain() {
		put_storage_value(b"Contracts", b"ContractInfoOf", &hash, contract_info_of);
	}

	if let Some(get_price) = take_storage_value::<BalanceOf<T>>(b"Contract", b"GetPrice", &[]) {
		put_storage_value(b"Contracts", b"GetPrice", &[], get_price);
	}
}
