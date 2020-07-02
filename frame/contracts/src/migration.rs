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
use frame_support::storage::migration::{ remove_storage_prefix, take_storage_value, StorageIterator};
use frame_support::weights::Weight;
use frame_support::runtime_print;

use crate::gas::Gas;

pub fn on_runtime_upgrade<T: Trait>() -> Weight {
	change_name_contract_to_contracts::<T>()
}

mod deprecated {
	use super::*;
	
	#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
	#[derive(Clone, Encode, Decode, PartialEq, Eq, RuntimeDebug)]
	pub struct Schedule {
		/// Version of the schedule.
		pub version: u32,

		/// Cost of putting a byte of code into storage.
		pub put_code_per_byte_cost: Gas,

		/// Gas cost of a growing memory by single page.
		pub grow_mem_cost: Gas,

		/// Gas cost of a regular operation.
		pub regular_op_cost: Gas,

		/// Gas cost per one byte returned.
		pub return_data_per_byte_cost: Gas,

		/// Gas cost to deposit an event; the per-byte portion.
		pub event_data_per_byte_cost: Gas,

		/// Gas cost to deposit an event; the cost per topic.
		pub event_per_topic_cost: Gas,

		/// Gas cost to deposit an event; the base.
		pub event_base_cost: Gas,

		/// Base gas cost to call into a contract.
		pub call_base_cost: Gas,

		/// Base gas cost to instantiate a contract.
		pub instantiate_base_cost: Gas,

		/// Gas cost per one byte read from the sandbox memory.
		pub sandbox_data_read_cost: Gas,

		/// Gas cost per one byte written to the sandbox memory.
		pub sandbox_data_write_cost: Gas,

		/// Cost for a simple balance transfer.
		pub transfer_cost: Gas,

		/// The maximum number of topics supported by an event.
		pub max_event_topics: u32,

		/// Maximum allowed stack height.
		///
		/// See https://wiki.parity.io/WebAssembly-StackHeight to find out
		/// how the stack frame cost is calculated.
		pub max_stack_height: u32,

		/// Maximum number of memory pages allowed for a contract.
		pub max_memory_pages: u32,

		/// Maximum allowed size of a declared table.
		pub max_table_size: u32,

		/// Whether the `ext_println` function is allowed to be used contracts.
		/// MUST only be enabled for `dev` chains, NOT for production chains
		pub enable_println: bool,

		/// The maximum length of a subject used for PRNG generation.
		pub max_subject_len: u32,
	}
}

// Change the storage name used by this pallet from `Contract` to `Contracts`.
//
// Since the format of the storage items themselves have not changed, we do not
// need to keep track of a storage version. If the runtime does not need to be
// upgraded, nothing here will happen anyway.
fn change_name_contract_to_contracts<T: Trait>() -> Weight {
	sp_runtime::print("🕊️  Migrating Contracts.");

	// Remove `GasSpent` because it doesn't exist anymore.
	remove_storage_prefix(b"Contract", b"GasSpent", &[]);

	// Replace the old with the new schedule.
	take_storage_value::<deprecated::Schedule>(b"Contract", b"CurrentSchedule", &[]);
	CurrentSchedule::put(Schedule::default());

	// There are currently no contracts on Edgeware so this should just do nothing.
	// Include logging just in case.
	for (hash, _code) in StorageIterator::<Vec<u8>>::new(b"Contract", b"PristineCode").drain() {
		runtime_print!("Contracts: Discarding PristinceCode at hash {:?}", hash);
	}
	for (hash, _storage) in StorageIterator::<wasm::PrefabWasmModule>::new(b"Contract", b"CodeStorage").drain() {
		runtime_print!("Contracts: Discarding CodeStorage at hash {:?}", hash);
	}
	for (hash, _info) in StorageIterator::<ContractInfo<T>>::new(b"Contract", b"ContractInfoOf").drain() {
		runtime_print!("Contracts: Discarding ContractInfoOf at hash {:?}", hash);
	}

	// (Re-)Set the AccountCounter.
	if let Some(counter) = take_storage_value::<u64>(b"Contract", b"AccountCounter", &[]) {
		AccountCounter::put(counter);
	} else {
		AccountCounter::put(0);
	}

	// Remove `GetPrice` because it doesn't exist anymore.
	remove_storage_prefix(b"Contract", b"GetPrice", &[]);

	sp_runtime::print("🕊️  Done Contracts.");
	T::MaximumBlockWeight::get()
}
