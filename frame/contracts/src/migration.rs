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
use frame_support::weights::Weight;

pub fn on_runtime_upgrade<T: Trait>() -> Weight {
	// TODO: removed for now because it's failing
	// change_name_contract_to_contracts::<T>()
	0
}

// Change the storage name used by this pallet from `Contract` to `Contracts`.
//
// Since the format of the storage items themselves have not changed, we do not
// need to keep track of a storage version. If the runtime does not need to be
// upgraded, nothing here will happen anyway.

fn change_name_contract_to_contracts<T: Trait>() -> Weight {
	sp_runtime::print("Migrating Contracts.");

	let mut weight = 0;
	let db = T::DbWeight::get();
	if let Some(gas_spent) = take_storage_value::<Gas>(b"Contract", b"GasSpent", &[]) {
		put_storage_value(b"Contracts", b"GasSpent", &[], gas_spent);
		weight += db.writes(2);
	}
	weight += db.reads(1);

	if let Some(current_schedule) = take_storage_value::<Schedule>(b"Contract", b"CurrentSchedule", &[]) {
		put_storage_value(b"Contracts", b"CurrentSchedule", &[], current_schedule);
		weight += db.writes(2);
	}
	weight += db.reads(1);

	for (hash, pristine_code) in StorageIterator::<Vec<u8>>::new(b"Contract", b"PristineCode").drain() {
		put_storage_value(b"Contracts", b"PristineCode", &hash, pristine_code);
		weight += db.reads_writes(1, 2);
	}

	for (hash, code_storage) in StorageIterator::<wasm::PrefabWasmModule>::new(b"Contract", b"CodeStorage").drain() {
		put_storage_value(b"Contracts", b"CodeStorage", &hash, code_storage);
		weight += db.reads_writes(1, 2);
	}

	if let Some(current_schedule) = take_storage_value::<u64>(b"Contract", b"AccountCounter", &[]) {
		put_storage_value(b"Contracts", b"AccountCounter", &[], current_schedule);
		weight += db.writes(2);
	}
	weight += db.reads(1);

	for (hash, contract_info_of) in StorageIterator::<ContractInfo<T>>::new(b"Contract", b"ContractInfoOf").drain() {
		put_storage_value(b"Contracts", b"ContractInfoOf", &hash, contract_info_of);
		weight += db.reads_writes(1, 2);
	}

	if let Some(get_price) = take_storage_value::<BalanceOf<T>>(b"Contract", b"GetPrice", &[]) {
		put_storage_value(b"Contracts", b"GetPrice", &[], get_price);
		weight += db.writes(2);
	}
	weight += db.reads(1);

	sp_runtime::print("Done Contracts.");
	weight
}
