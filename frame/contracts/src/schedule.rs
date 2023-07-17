// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! This module contains the cost schedule and supporting code that constructs a
//! sane default schedule from a `WeightInfo` implementation.

use crate::{weights::WeightInfo, Config};

use codec::{Decode, Encode};
use frame_support::{weights::Weight, DefaultNoBound};
use pallet_contracts_proc_macro::{ScheduleDebug, WeightDebug};
use scale_info::TypeInfo;
#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};
use sp_runtime::RuntimeDebug;
use sp_std::marker::PhantomData;

/// Definition of the cost schedule and other parameterizations for the wasm vm.
///
/// Its [`Default`] implementation is the designated way to initialize this type. It uses
/// the benchmarked information supplied by [`Config::WeightInfo`]. All of its fields are
/// public and can therefore be modified. For example in order to change some of the limits
/// and set a custom instruction weight version the following code could be used:
/// ```rust
/// use pallet_contracts::{Schedule, Limits, InstructionWeights, Config};
///
/// fn create_schedule<T: Config>() -> Schedule<T> {
///     Schedule {
///         limits: Limits {
/// 		        globals: 3,
/// 		        parameters: 3,
/// 		        memory_pages: 16,
/// 		        table_size: 3,
/// 		        br_table_size: 3,
/// 		        .. Default::default()
/// 	        },
///         instruction_weights: InstructionWeights {
///             .. Default::default()
///         },
/// 	        .. Default::default()
///     }
/// }
/// ```
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "std", serde(bound(serialize = "", deserialize = "")))]
#[derive(Clone, Encode, Decode, PartialEq, Eq, ScheduleDebug, DefaultNoBound, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct Schedule<T: Config> {
	/// Describes the upper limits on various metrics.
	pub limits: Limits,

	/// The weights for individual wasm instructions.
	pub instruction_weights: InstructionWeights<T>,

	/// The weights for each imported function a contract is allowed to call.
	pub host_fn_weights: HostFnWeights<T>,
}

/// Describes the upper limits on various metrics.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Clone, Encode, Decode, PartialEq, Eq, RuntimeDebug, TypeInfo)]
pub struct Limits {
	/// The maximum number of topics supported by an event.
	pub event_topics: u32,

	/// Maximum number of globals a module is allowed to declare.
	///
	/// Globals are not limited through the linear memory limit `memory_pages`.
	pub globals: u32,

	/// Maximum number of locals a function can have.
	///
	/// As wasm engine initializes each of the local, we need to limit their number to confine
	/// execution costs.
	pub locals: u32,

	/// Maximum numbers of parameters a function can have.
	///
	/// Those need to be limited to prevent a potentially exploitable interaction with
	/// the stack height instrumentation: The costs of executing the stack height
	/// instrumentation for an indirectly called function scales linearly with the amount
	/// of parameters of this function. Because the stack height instrumentation itself is
	/// is not weight metered its costs must be static (via this limit) and included in
	/// the costs of the instructions that cause them (call, call_indirect).
	pub parameters: u32,

	/// Maximum number of memory pages allowed for a contract.
	pub memory_pages: u32,

	/// Maximum number of elements allowed in a table.
	///
	/// Currently, the only type of element that is allowed in a table is funcref.
	pub table_size: u32,

	/// Maximum number of elements that can appear as immediate value to the br_table instruction.
	pub br_table_size: u32,

	/// The maximum length of a subject in bytes used for PRNG generation.
	pub subject_len: u32,

	/// The maximum size of a storage value and event payload in bytes.
	pub payload_len: u32,

	/// The maximum node runtime memory. This is for integrity checks only and does not affect the
	/// real setting.
	pub runtime_memory: u32,
}

impl Limits {
	/// The maximum memory size in bytes that a contract can occupy.
	pub fn max_memory_size(&self) -> u32 {
		self.memory_pages * 64 * 1024
	}
}

/// Gas metering of Wasm executed instructions is being done on the engine side.
/// This struct holds a reference value used to gas units scaling between host and engine.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Clone, Encode, Decode, PartialEq, Eq, ScheduleDebug, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct InstructionWeights<T: Config> {
	/// Base instruction `ref_time` Weight.
	/// Should match to wasmi's `1` fuel (see <https://github.com/paritytech/wasmi/issues/701>).
	pub base: u32,
	/// The type parameter is used in the default implementation.
	#[codec(skip)]
	pub _phantom: PhantomData<T>,
}

/// Describes the weight for each imported function that a contract is allowed to call.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Clone, Encode, Decode, PartialEq, Eq, WeightDebug, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct HostFnWeights<T: Config> {
	/// Weight of calling `seal_caller`.
	pub caller: Weight,

	/// Weight of calling `seal_is_contract`.
	pub is_contract: Weight,

	/// Weight of calling `seal_code_hash`.
	pub code_hash: Weight,

	/// Weight of calling `seal_own_code_hash`.
	pub own_code_hash: Weight,

	/// Weight of calling `seal_caller_is_origin`.
	pub caller_is_origin: Weight,

	/// Weight of calling `seal_caller_is_root`.
	pub caller_is_root: Weight,

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

	/// Weight of calling `seal_block_number`.
	pub block_number: Weight,

	/// Weight of calling `seal_now`.
	pub now: Weight,

	/// Weight of calling `seal_weight_to_fee`.
	pub weight_to_fee: Weight,

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

	/// Weight of calling `seal_random`.
	pub random: Weight,

	/// Weight of calling `seal_reposit_event`.
	pub deposit_event: Weight,

	/// Weight per topic supplied to `seal_deposit_event`.
	pub deposit_event_per_topic: Weight,

	/// Weight per byte of an event deposited through `seal_deposit_event`.
	pub deposit_event_per_byte: Weight,

	/// Weight of calling `seal_debug_message`.
	pub debug_message: Weight,

	/// Weight of calling `seal_debug_message` per byte of the message.
	pub debug_message_per_byte: Weight,

	/// Weight of calling `seal_set_storage`.
	pub set_storage: Weight,

	/// Weight per written byten of an item stored with `seal_set_storage`.
	pub set_storage_per_new_byte: Weight,

	/// Weight per overwritten byte of an item stored with `seal_set_storage`.
	pub set_storage_per_old_byte: Weight,

	/// Weight of calling `seal_set_code_hash`.
	pub set_code_hash: Weight,

	/// Weight of calling `seal_clear_storage`.
	pub clear_storage: Weight,

	/// Weight of calling `seal_clear_storage` per byte of the stored item.
	pub clear_storage_per_byte: Weight,

	/// Weight of calling `seal_contains_storage`.
	pub contains_storage: Weight,

	/// Weight of calling `seal_contains_storage` per byte of the stored item.
	pub contains_storage_per_byte: Weight,

	/// Weight of calling `seal_get_storage`.
	pub get_storage: Weight,

	/// Weight per byte of an item received via `seal_get_storage`.
	pub get_storage_per_byte: Weight,

	/// Weight of calling `seal_take_storage`.
	pub take_storage: Weight,

	/// Weight per byte of an item received via `seal_take_storage`.
	pub take_storage_per_byte: Weight,

	/// Weight of calling `seal_transfer`.
	pub transfer: Weight,

	/// Weight of calling `seal_call`.
	pub call: Weight,

	/// Weight of calling `seal_delegate_call`.
	pub delegate_call: Weight,

	/// Weight surcharge that is claimed if `seal_call` does a balance transfer.
	pub call_transfer_surcharge: Weight,

	/// Weight per byte that is cloned by supplying the `CLONE_INPUT` flag.
	pub call_per_cloned_byte: Weight,

	/// Weight of calling `seal_instantiate`.
	pub instantiate: Weight,

	/// Weight surcharge that is claimed if `seal_instantiate` does a balance transfer.
	pub instantiate_transfer_surcharge: Weight,

	/// Weight per input byte supplied to `seal_instantiate`.
	pub instantiate_per_input_byte: Weight,

	/// Weight per salt byte supplied to `seal_instantiate`.
	pub instantiate_per_salt_byte: Weight,

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

	/// Weight of calling `seal_ecdsa_recover`.
	pub ecdsa_recover: Weight,

	/// Weight of calling `seal_ecdsa_to_eth_address`.
	pub ecdsa_to_eth_address: Weight,

	/// Weight of calling `sr25519_verify`.
	pub sr25519_verify: Weight,

	/// Weight per byte of calling `sr25519_verify`.
	pub sr25519_verify_per_byte: Weight,

	/// Weight of calling `reentrance_count`.
	pub reentrance_count: Weight,

	/// Weight of calling `account_reentrance_count`.
	pub account_reentrance_count: Weight,

	/// Weight of calling `instantiation_nonce`.
	pub instantiation_nonce: Weight,

	/// The type parameter is used in the default implementation.
	#[codec(skip)]
	pub _phantom: PhantomData<T>,
}

macro_rules! replace_token {
	($_in:tt $replacement:tt) => {
		$replacement
	};
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

macro_rules! cost_instr_no_params {
	($name:ident) => {
		cost_args!($name, 1).ref_time() as u32
	};
}

macro_rules! cost {
	($name:ident) => {
		cost_args!($name, 1)
	};
}

macro_rules! cost_instr {
	($name:ident, $num_params:expr) => {
		cost_instr_no_params!($name)
			.saturating_sub((cost_instr_no_params!(instr_i64const) / 2).saturating_mul($num_params))
	};
}

impl Default for Limits {
	fn default() -> Self {
		Self {
			event_topics: 4,
			globals: 256,
			locals: 1024,
			parameters: 128,
			memory_pages: 16,
			// 4k function pointers (This is in count not bytes).
			table_size: 4096,
			br_table_size: 256,
			subject_len: 32,
			payload_len: 16 * 1024,
			runtime_memory: 1024 * 1024 * 128,
		}
	}
}

impl<T: Config> Default for InstructionWeights<T> {
	/// We price both `i64.const` and `drop` as `instr_i64const / 2`. The reason
	/// for that is that we cannot benchmark either of them on its own.
	fn default() -> Self {
		Self { base: cost_instr!(instr_i64const, 1), _phantom: PhantomData }
	}
}

impl<T: Config> Default for HostFnWeights<T> {
	fn default() -> Self {
		Self {
			caller: cost!(seal_caller),
			is_contract: cost!(seal_is_contract),
			code_hash: cost!(seal_code_hash),
			own_code_hash: cost!(seal_own_code_hash),
			caller_is_origin: cost!(seal_caller_is_origin),
			caller_is_root: cost!(seal_caller_is_root),
			address: cost!(seal_address),
			gas_left: cost!(seal_gas_left),
			balance: cost!(seal_balance),
			value_transferred: cost!(seal_value_transferred),
			minimum_balance: cost!(seal_minimum_balance),
			block_number: cost!(seal_block_number),
			now: cost!(seal_now),
			weight_to_fee: cost!(seal_weight_to_fee),
			input: cost!(seal_input),
			input_per_byte: cost!(seal_input_per_byte),
			r#return: cost!(seal_return),
			return_per_byte: cost!(seal_return_per_byte),
			terminate: cost!(seal_terminate),
			random: cost!(seal_random),
			deposit_event: cost!(seal_deposit_event),
			deposit_event_per_topic: cost_args!(seal_deposit_event_per_topic_and_byte, 1, 0),
			deposit_event_per_byte: cost_args!(seal_deposit_event_per_topic_and_byte, 0, 1),
			debug_message: cost!(seal_debug_message),
			debug_message_per_byte: cost!(seal_debug_message_per_byte),
			set_storage: cost!(seal_set_storage),
			set_code_hash: cost!(seal_set_code_hash),
			set_storage_per_new_byte: cost!(seal_set_storage_per_new_byte),
			set_storage_per_old_byte: cost!(seal_set_storage_per_old_byte),
			clear_storage: cost!(seal_clear_storage),
			clear_storage_per_byte: cost!(seal_clear_storage_per_byte),
			contains_storage: cost!(seal_contains_storage),
			contains_storage_per_byte: cost!(seal_contains_storage_per_byte),
			get_storage: cost!(seal_get_storage),
			get_storage_per_byte: cost!(seal_get_storage_per_byte),
			take_storage: cost!(seal_take_storage),
			take_storage_per_byte: cost!(seal_take_storage_per_byte),
			transfer: cost!(seal_transfer),
			call: cost!(seal_call),
			delegate_call: cost!(seal_delegate_call),
			call_transfer_surcharge: cost_args!(seal_call_per_transfer_clone_byte, 1, 0),
			call_per_cloned_byte: cost_args!(seal_call_per_transfer_clone_byte, 0, 1),
			instantiate: cost!(seal_instantiate),
			instantiate_transfer_surcharge: cost_args!(
				seal_instantiate_per_transfer_input_salt_byte,
				1,
				0,
				0
			),
			instantiate_per_input_byte: cost_args!(
				seal_instantiate_per_transfer_input_salt_byte,
				0,
				1,
				0
			),
			instantiate_per_salt_byte: cost_args!(
				seal_instantiate_per_transfer_input_salt_byte,
				0,
				0,
				1
			),
			hash_sha2_256: cost!(seal_hash_sha2_256),
			hash_sha2_256_per_byte: cost!(seal_hash_sha2_256_per_byte),
			hash_keccak_256: cost!(seal_hash_keccak_256),
			hash_keccak_256_per_byte: cost!(seal_hash_keccak_256_per_byte),
			hash_blake2_256: cost!(seal_hash_blake2_256),
			hash_blake2_256_per_byte: cost!(seal_hash_blake2_256_per_byte),
			hash_blake2_128: cost!(seal_hash_blake2_128),
			hash_blake2_128_per_byte: cost!(seal_hash_blake2_128_per_byte),
			ecdsa_recover: cost!(seal_ecdsa_recover),
			sr25519_verify: cost!(seal_sr25519_verify),
			sr25519_verify_per_byte: cost!(seal_sr25519_verify_per_byte),
			ecdsa_to_eth_address: cost!(seal_ecdsa_to_eth_address),
			reentrance_count: cost!(seal_reentrance_count),
			account_reentrance_count: cost!(seal_account_reentrance_count),
			instantiation_nonce: cost!(seal_instantiation_nonce),
			_phantom: PhantomData,
		}
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::tests::Test;

	#[test]
	fn print_test_schedule() {
		let schedule = Schedule::<Test>::default();
		println!("{:#?}", schedule);
	}
}
