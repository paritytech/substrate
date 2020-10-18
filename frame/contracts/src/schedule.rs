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
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

//! This module contains the cost schedule and supporting code that constructs a
//! sane default schedule from a `WeightInfo` implementation.

use crate::{Trait, WeightInfo};

#[cfg(feature = "std")]
use serde::{Serialize, Deserialize};
use frame_support::weights::Weight;
use sp_std::{marker::PhantomData, fmt};
use codec::{Encode, Decode};

/// How many API calls are executed in a single batch. The reason for increasing the amount
/// of API calls in batches (per benchmark component increase) is so that the linear regression
/// has an easier time determining the contribution of that component.
pub const API_BENCHMARK_BATCH_SIZE: u32 = 100;

/// Definition of the cost schedule and other parameterizations for wasm vm.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Clone, Encode, Decode, PartialEq, Eq)]
pub struct Schedule<T: Trait> {
	/// Version of the schedule.
	pub version: u32,

	/// The weights for individual wasm instructions.
	pub instruction_weights: InstructionWeights,

	/// The weights for each imported function a contract is allowed to call.
	pub host_fn_weights: HostFnWeights,

	/// Whether the `seal_println` function is allowed to be used contracts.
	/// MUST only be enabled for `dev` chains, NOT for production chains
	pub enable_println: bool,

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

	/// The maximum length of a subject used for PRNG generation.
	pub max_subject_len: u32,

	/// The maximum length of a contract code in bytes. This limit applies to the uninstrumented
	/// and pristine form of the code as supplied to `put_code`.
	pub max_code_size: u32,

	/// The type parameter is used in the default implementation.
	pub _phantom: PhantomData<T>,
}

/// Describes the weight for all categories of supported wasm instructions.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Clone, Encode, Decode, PartialEq, Eq)]
pub struct InstructionWeights {
	/// Weight of a growing memory by single page.
	pub grow_mem: Weight,

	/// Weight of a regular operation.
	pub regular: Weight,
}

/// Describes the weight for each imported function that a contract is allowed to call.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Clone, Encode, Decode, PartialEq, Eq)]
pub struct HostFnWeights {
	/// Weight of calling `seal_caller`.
	pub caller: Weight,

	/// Weight of calling `seal_address`.
	pub address: Weight,

	/// Weight of calling `seal_gas_left`.
	pub gas_left: Weight,

	/// Weight of calling `seal_balance`.
	pub balance: Weight,

	/// Weight of calling `seal_value_transferred`.
	pub value_transferred: Weight,

	/// Weight of calling `seal_minimum_balance`.
	pub minimum_balance: Weight,

	/// Weight of calling `seal_tombstone_deposit`.
	pub tombstone_deposit: Weight,

	/// Weight of calling `seal_rent_allowance`.
	pub rent_allowance: Weight,

	/// Weight of calling `seal_block_number`.
	pub block_number: Weight,

	/// Weight of calling `seal_now`.
	pub now: Weight,

	/// Weight of calling `seal_weight_to_fee`.
	pub weight_to_fee: Weight,

	/// Weight of calling `gas`.
	pub gas: Weight,

	/// Weight of calling `seal_input`.
	pub input: Weight,

	/// Weight per input byte copied to contract memory by `seal_input`.
	pub input_per_byte: Weight,

	/// Weight of calling `seal_return`.
	pub r#return: Weight,

	/// Weight per byte returned through `seal_return`.
	pub return_per_byte: Weight,

	/// Weight of calling `seal_terminate`.
	pub terminate: Weight,

	/// Weight of calling `seal_restore_to`.
	pub restore_to: Weight,

	/// Weight per delta key supplied to `seal_restore_to`.
	pub restore_to_per_delta: Weight,

	/// Weight of calling `seal_random`.
	pub random: Weight,

	/// Weight of calling `seal_reposit_event`.
	pub deposit_event: Weight,

	/// Weight per topic supplied to `seal_deposit_event`.
	pub deposit_event_per_topic: Weight,

	/// Weight per byte of an event deposited through `seal_deposit_event`.
	pub deposit_event_per_byte: Weight,

	/// Weight of calling `seal_set_rent_allowance`.
	pub set_rent_allowance: Weight,

	/// Weight of calling `seal_set_storage`.
	pub set_storage: Weight,

	/// Weight per byte of an item stored with `seal_set_storage`.
	pub set_storage_per_byte: Weight,

	/// Weight of calling `seal_clear_storage`.
	pub clear_storage: Weight,

	/// Weight of calling `seal_get_storage`.
	pub get_storage: Weight,

	/// Weight per byte of an item received via `seal_get_storage`.
	pub get_storage_per_byte: Weight,

	/// Weight of calling `seal_transfer`.
	pub transfer: Weight,

	/// Weight of calling `seal_call`.
	pub call: Weight,

	/// Weight surcharge that is claimed if `seal_call` does a balance transfer.
	pub call_transfer_surcharge: Weight,

	/// Weight per input byte supplied to `seal_call`.
	pub call_per_input_byte: Weight,

	/// Weight per output byte received through `seal_call`.
	pub call_per_output_byte: Weight,

	/// Weight of calling `seal_instantiate`.
	pub instantiate: Weight,

	/// Weight per input byte supplied to `seal_instantiate`.
	pub instantiate_per_input_byte: Weight,

	/// Weight per output byte received through `seal_instantiate`.
	pub instantiate_per_output_byte: Weight,

	/// Weight of calling `seal_hash_sha_256`.
	pub hash_sha2_256: Weight,

	/// Weight per byte hashed by `seal_hash_sha_256`.
	pub hash_sha2_256_per_byte: Weight,

	/// Weight of calling `seal_hash_keccak_256`.
	pub hash_keccak_256: Weight,

	/// Weight per byte hashed by `seal_hash_keccak_256`.
	pub hash_keccak_256_per_byte: Weight,

	/// Weight of calling `seal_hash_blake2_256`.
	pub hash_blake2_256: Weight,

	/// Weight per byte hashed by `seal_hash_blake2_256`.
	pub hash_blake2_256_per_byte: Weight,

	/// Weight of calling `seal_hash_blake2_128`.
	pub hash_blake2_128: Weight,

	/// Weight per byte hashed by `seal_hash_blake2_128`.
	pub hash_blake2_128_per_byte: Weight,
}

/// We need to implement Debug manually because the automatic derive enforces T
/// to also implement Debug.
impl<T: Trait> fmt::Debug for Schedule<T> {
	fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
		f.debug_struct("Schedule").finish()
	}
}

/// 500 (2 instructions per nano second on 2GHZ) * 1000x slowdown through wasmi
/// This is a wild guess and should be viewed as a rough estimation.
/// Proper benchmarks are needed before this value and its derivatives can be used in production.
const WASM_INSTRUCTION_COST: Weight = 500_000;

macro_rules! replace_token {
	($_in:tt $replacement:tt) => { $replacement };
}

macro_rules! call_zero {
	($name:ident, $( $arg:expr ),*) => {
		T::WeightInfo::$name($( replace_token!($arg 0) ),*)
	};
}

macro_rules! cost_args {
	($name:ident, $( $arg: expr ),+) => {
		(T::WeightInfo::$name($( $arg ),+).saturating_sub(call_zero!($name, $( $arg ),+)))
	}
}

macro_rules! cost_batched_args {
	($name:ident, $( $arg: expr ),+) => {
		cost_args!($name, $( $arg ),+) / Weight::from(API_BENCHMARK_BATCH_SIZE)
	}
}

macro_rules! cost_byte_args {
	($name:ident, $( $arg: expr ),+) => {
		cost_args!($name, $( $arg ),+) / 1024
	}
}

macro_rules! cost_byte_batched_args {
	($name:ident, $( $arg: expr ),+) => {
		cost_batched_args!($name, $( $arg ),+) / 1024
	}
}

macro_rules! cost {
	($name:ident) => {
		cost_args!($name, 1)
	}
}

macro_rules! cost_batched {
	($name:ident) => {
		cost_batched_args!($name, 1)
	}
}

macro_rules! cost_byte {
	($name:ident) => {
		cost_byte_args!($name, 1)
	}
}

macro_rules! cost_byte_batched {
	($name:ident) => {
		cost_byte_batched_args!($name, 1)
	}
}

impl<T: Trait> Default for Schedule<T> {
	fn default() -> Self {
		let instruction_weights = InstructionWeights {
			grow_mem: WASM_INSTRUCTION_COST,
			regular: WASM_INSTRUCTION_COST,
		};

		let host_fn_weights = HostFnWeights {
			caller: cost_batched!(seal_caller),
			address: cost_batched!(seal_address),
			gas_left: cost_batched!(seal_gas_left),
			balance: cost_batched!(seal_balance),
			value_transferred: cost_batched!(seal_value_transferred),
			minimum_balance: cost_batched!(seal_minimum_balance),
			tombstone_deposit: cost_batched!(seal_tombstone_deposit),
			rent_allowance: cost_batched!(seal_rent_allowance),
			block_number: cost_batched!(seal_block_number),
			now: cost_batched!(seal_now),
			weight_to_fee: cost_batched!(seal_weight_to_fee),
			gas: cost_batched!(seal_gas),
			input: cost!(seal_input),
			input_per_byte: cost_byte!(seal_input_per_kb),
			r#return: cost!(seal_return),
			return_per_byte: cost_byte!(seal_return_per_kb),
			terminate: cost!(seal_terminate),
			restore_to: cost!(seal_restore_to),
			restore_to_per_delta: cost_batched!(seal_restore_to_per_delta),
			random: cost_batched!(seal_random),
			deposit_event: cost_batched!(seal_deposit_event),
			deposit_event_per_topic: cost_batched_args!(seal_deposit_event_per_topic_and_kb, 1, 0),
			deposit_event_per_byte: cost_byte_batched_args!(seal_deposit_event_per_topic_and_kb, 0, 1),
			set_rent_allowance: cost_batched!(seal_set_rent_allowance),
			set_storage: cost_batched!(seal_set_storage),
			set_storage_per_byte: cost_byte_batched!(seal_set_storage_per_kb),
			clear_storage: cost_batched!(seal_clear_storage),
			get_storage: cost_batched!(seal_get_storage),
			get_storage_per_byte: cost_byte_batched!(seal_get_storage_per_kb),
			transfer: cost_batched!(seal_transfer),
			call: cost_batched!(seal_call),
			call_transfer_surcharge: cost_batched_args!(seal_call_per_transfer_input_output_kb, 1, 0, 0),
			call_per_input_byte: cost_byte_batched_args!(seal_call_per_transfer_input_output_kb, 0, 1, 0),
			call_per_output_byte: cost_byte_batched_args!(seal_call_per_transfer_input_output_kb, 0, 0, 1),
			instantiate: cost_batched!(seal_instantiate),
			instantiate_per_input_byte: cost_byte_batched_args!(seal_instantiate_per_input_output_kb, 1, 0),
			instantiate_per_output_byte: cost_byte_batched_args!(seal_instantiate_per_input_output_kb, 0, 1),
			hash_sha2_256: cost_batched!(seal_hash_sha2_256),
			hash_sha2_256_per_byte: cost_byte_batched!(seal_hash_sha2_256_per_kb),
			hash_keccak_256: cost_batched!(seal_hash_keccak_256),
			hash_keccak_256_per_byte: cost_byte_batched!(seal_hash_keccak_256_per_kb),
			hash_blake2_256: cost_batched!(seal_hash_blake2_256),
			hash_blake2_256_per_byte: cost_byte_batched!(seal_hash_blake2_256_per_kb),
			hash_blake2_128: cost_batched!(seal_hash_blake2_128),
			hash_blake2_128_per_byte: cost_byte_batched!(seal_hash_blake2_128_per_kb),
		};

		Self {
			version: 0,
			instruction_weights,
			host_fn_weights,
			enable_println: false,
			max_event_topics: 4,
			max_stack_height: 64 * 1024,
			max_memory_pages: 16,
			max_table_size: 16 * 1024,
			max_subject_len: 32,
			max_code_size: 512 * 1024,
			_phantom: PhantomData,
		}
	}
}
