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

use crate::{wasm::Determinism, weights::WeightInfo, Config};

use codec::{Decode, Encode};
use frame_support::{weights::Weight, DefaultNoBound};
use pallet_contracts_proc_macro::{ScheduleDebug, WeightDebug};
use scale_info::TypeInfo;
#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};
use sp_runtime::RuntimeDebug;
use sp_std::marker::PhantomData;
use wasm_instrument::{gas_metering, parity_wasm::elements};

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
/// 	            version: 5,
///             .. Default::default()
///         },
/// 	        .. Default::default()
///     }
/// }
/// ```
///
/// # Note
///
/// Please make sure to bump the [`InstructionWeights::version`] whenever substantial
/// changes are made to its values.
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
///
/// # Note
///
/// The values in this struct should never be decreased. The reason is that decreasing those
/// values will break existing contracts which are above the new limits when a
/// re-instrumentation is triggered.
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

/// Describes the weight for all categories of supported wasm instructions.
///
/// There there is one field for each wasm instruction that describes the weight to
/// execute one instruction of that name. There are a few exceptions:
///
/// 1. If there is a i64 and a i32 variant of an instruction we use the weight
///    of the former for both.
/// 2. The following instructions are free of charge because they merely structure the
///    wasm module and cannot be spammed without making the module invalid (and rejected):
///    End, Unreachable, Return, Else
/// 3. The following instructions cannot be benchmarked because they are removed by any
///    real world execution engine as a preprocessing step and therefore don't yield a
///    meaningful benchmark result. However, in contrast to the instructions mentioned
///    in 2. they can be spammed. We price them with the same weight as the "default"
///    instruction (i64.const): Block, Loop, Nop
/// 4. We price both i64.const and drop as InstructionWeights.i64const / 2. The reason
///    for that is that we cannot benchmark either of them on its own but we need their
///    individual values to derive (by subtraction) the weight of all other instructions
///    that use them as supporting instructions. Supporting means mainly pushing arguments
///    and dropping return values in order to maintain a valid module.
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
#[derive(Clone, Encode, Decode, PartialEq, Eq, ScheduleDebug, TypeInfo)]
#[scale_info(skip_type_params(T))]
pub struct InstructionWeights<T: Config> {
	/// Version of the instruction weights.
	///
	/// # Note
	///
	/// Should be incremented whenever any instruction weight is changed. The
	/// reason is that changes to instruction weights require a re-instrumentation
	/// in order to apply the changes to an already deployed code. The re-instrumentation
	/// is triggered by comparing the version of the current schedule with the version the code was
	/// instrumented with. Changes usually happen when pallet_contracts is re-benchmarked.
	///
	/// Changes to other parts of the schedule should not increment the version in
	/// order to avoid unnecessary re-instrumentations.
	pub version: u32,
	/// Weight to be used for instructions which don't have benchmarks assigned.
	///
	/// This weight is used whenever a code is uploaded with [`Determinism::Relaxed`]
	/// and an instruction (usually a float instruction) is encountered. This weight is **not**
	/// used if a contract is uploaded with [`Determinism::Enforced`]. If this field is set to
	/// `0` (the default) only deterministic codes are allowed to be uploaded.
	pub fallback: u32,
	pub i64const: u32,
	pub i64load: u32,
	pub i64store: u32,
	pub select: u32,
	pub r#if: u32,
	pub br: u32,
	pub br_if: u32,
	pub br_table: u32,
	pub br_table_per_entry: u32,
	pub call: u32,
	pub call_indirect: u32,
	pub call_per_local: u32,
	pub local_get: u32,
	pub local_set: u32,
	pub local_tee: u32,
	pub global_get: u32,
	pub global_set: u32,
	pub memory_current: u32,
	pub memory_grow: u32,
	pub i64clz: u32,
	pub i64ctz: u32,
	pub i64popcnt: u32,
	pub i64eqz: u32,
	pub i64extendsi32: u32,
	pub i64extendui32: u32,
	pub i32wrapi64: u32,
	pub i64eq: u32,
	pub i64ne: u32,
	pub i64lts: u32,
	pub i64ltu: u32,
	pub i64gts: u32,
	pub i64gtu: u32,
	pub i64les: u32,
	pub i64leu: u32,
	pub i64ges: u32,
	pub i64geu: u32,
	pub i64add: u32,
	pub i64sub: u32,
	pub i64mul: u32,
	pub i64divs: u32,
	pub i64divu: u32,
	pub i64rems: u32,
	pub i64remu: u32,
	pub i64and: u32,
	pub i64or: u32,
	pub i64xor: u32,
	pub i64shl: u32,
	pub i64shrs: u32,
	pub i64shru: u32,
	pub i64rotl: u32,
	pub i64rotr: u32,
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
	fn default() -> Self {
		Self {
			version: 4,
			fallback: 0,
			i64const: cost_instr!(instr_i64const, 1),
			i64load: cost_instr!(instr_i64load, 2),
			i64store: cost_instr!(instr_i64store, 2),
			select: cost_instr!(instr_select, 4),
			r#if: cost_instr!(instr_if, 3),
			br: cost_instr!(instr_br, 2),
			br_if: cost_instr!(instr_br_if, 3),
			br_table: cost_instr!(instr_br_table, 3),
			br_table_per_entry: cost_instr!(instr_br_table_per_entry, 0),
			call: cost_instr!(instr_call, 2),
			call_indirect: cost_instr!(instr_call_indirect, 3),
			call_per_local: cost_instr!(instr_call_per_local, 0),
			local_get: cost_instr!(instr_local_get, 1),
			local_set: cost_instr!(instr_local_set, 1),
			local_tee: cost_instr!(instr_local_tee, 2),
			global_get: cost_instr!(instr_global_get, 1),
			global_set: cost_instr!(instr_global_set, 1),
			memory_current: cost_instr!(instr_memory_current, 1),
			memory_grow: cost_instr!(instr_memory_grow, 1),
			i64clz: cost_instr!(instr_i64clz, 2),
			i64ctz: cost_instr!(instr_i64ctz, 2),
			i64popcnt: cost_instr!(instr_i64popcnt, 2),
			i64eqz: cost_instr!(instr_i64eqz, 2),
			i64extendsi32: cost_instr!(instr_i64extendsi32, 2),
			i64extendui32: cost_instr!(instr_i64extendui32, 2),
			i32wrapi64: cost_instr!(instr_i32wrapi64, 2),
			i64eq: cost_instr!(instr_i64eq, 3),
			i64ne: cost_instr!(instr_i64ne, 3),
			i64lts: cost_instr!(instr_i64lts, 3),
			i64ltu: cost_instr!(instr_i64ltu, 3),
			i64gts: cost_instr!(instr_i64gts, 3),
			i64gtu: cost_instr!(instr_i64gtu, 3),
			i64les: cost_instr!(instr_i64les, 3),
			i64leu: cost_instr!(instr_i64leu, 3),
			i64ges: cost_instr!(instr_i64ges, 3),
			i64geu: cost_instr!(instr_i64geu, 3),
			i64add: cost_instr!(instr_i64add, 3),
			i64sub: cost_instr!(instr_i64sub, 3),
			i64mul: cost_instr!(instr_i64mul, 3),
			i64divs: cost_instr!(instr_i64divs, 3),
			i64divu: cost_instr!(instr_i64divu, 3),
			i64rems: cost_instr!(instr_i64rems, 3),
			i64remu: cost_instr!(instr_i64remu, 3),
			i64and: cost_instr!(instr_i64and, 3),
			i64or: cost_instr!(instr_i64or, 3),
			i64xor: cost_instr!(instr_i64xor, 3),
			i64shl: cost_instr!(instr_i64shl, 3),
			i64shrs: cost_instr!(instr_i64shrs, 3),
			i64shru: cost_instr!(instr_i64shru, 3),
			i64rotl: cost_instr!(instr_i64rotl, 3),
			i64rotr: cost_instr!(instr_i64rotr, 3),
			_phantom: PhantomData,
		}
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
			address: cost!(seal_address),
			gas_left: cost!(seal_gas_left),
			balance: cost!(seal_balance),
			value_transferred: cost!(seal_value_transferred),
			minimum_balance: cost!(seal_minimum_balance),
			block_number: cost!(seal_block_number),
			now: cost!(seal_now),
			weight_to_fee: cost!(seal_weight_to_fee),
			// Manually remove proof size from basic block cost.
			//
			// Due to imperfect benchmarking some host functions incur a small
			// amount of proof size. Usually this is ok. However, charging a basic block is such
			// a frequent operation that this would be a vast overestimation.
			gas: cost!(seal_gas).set_proof_size(0),
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

struct ScheduleRules<'a, T: Config> {
	schedule: &'a Schedule<T>,
	determinism: Determinism,
}

impl<T: Config> Schedule<T> {
	pub(crate) fn rules(&self, determinism: Determinism) -> impl gas_metering::Rules + '_ {
		ScheduleRules { schedule: self, determinism }
	}
}

impl<'a, T: Config> gas_metering::Rules for ScheduleRules<'a, T> {
	fn instruction_cost(&self, instruction: &elements::Instruction) -> Option<u32> {
		use self::elements::Instruction::*;
		let w = &self.schedule.instruction_weights;

		let weight = match *instruction {
			End | Unreachable | Return | Else => 0,
			I32Const(_) | I64Const(_) | Block(_) | Loop(_) | Nop | Drop => w.i64const,
			I32Load(_, _) |
			I32Load8S(_, _) |
			I32Load8U(_, _) |
			I32Load16S(_, _) |
			I32Load16U(_, _) |
			I64Load(_, _) |
			I64Load8S(_, _) |
			I64Load8U(_, _) |
			I64Load16S(_, _) |
			I64Load16U(_, _) |
			I64Load32S(_, _) |
			I64Load32U(_, _) => w.i64load,
			I32Store(_, _) |
			I32Store8(_, _) |
			I32Store16(_, _) |
			I64Store(_, _) |
			I64Store8(_, _) |
			I64Store16(_, _) |
			I64Store32(_, _) => w.i64store,
			Select => w.select,
			If(_) => w.r#if,
			Br(_) => w.br,
			BrIf(_) => w.br_if,
			Call(_) => w.call,
			GetLocal(_) => w.local_get,
			SetLocal(_) => w.local_set,
			TeeLocal(_) => w.local_tee,
			GetGlobal(_) => w.global_get,
			SetGlobal(_) => w.global_set,
			CurrentMemory(_) => w.memory_current,
			GrowMemory(_) => w.memory_grow,
			CallIndirect(_, _) => w.call_indirect,
			BrTable(ref data) => w
				.br_table
				.saturating_add(w.br_table_per_entry.saturating_mul(data.table.len() as u32)),
			I32Clz | I64Clz => w.i64clz,
			I32Ctz | I64Ctz => w.i64ctz,
			I32Popcnt | I64Popcnt => w.i64popcnt,
			I32Eqz | I64Eqz => w.i64eqz,
			I64ExtendSI32 => w.i64extendsi32,
			I64ExtendUI32 => w.i64extendui32,
			I32WrapI64 => w.i32wrapi64,
			I32Eq | I64Eq => w.i64eq,
			I32Ne | I64Ne => w.i64ne,
			I32LtS | I64LtS => w.i64lts,
			I32LtU | I64LtU => w.i64ltu,
			I32GtS | I64GtS => w.i64gts,
			I32GtU | I64GtU => w.i64gtu,
			I32LeS | I64LeS => w.i64les,
			I32LeU | I64LeU => w.i64leu,
			I32GeS | I64GeS => w.i64ges,
			I32GeU | I64GeU => w.i64geu,
			I32Add | I64Add => w.i64add,
			I32Sub | I64Sub => w.i64sub,
			I32Mul | I64Mul => w.i64mul,
			I32DivS | I64DivS => w.i64divs,
			I32DivU | I64DivU => w.i64divu,
			I32RemS | I64RemS => w.i64rems,
			I32RemU | I64RemU => w.i64remu,
			I32And | I64And => w.i64and,
			I32Or | I64Or => w.i64or,
			I32Xor | I64Xor => w.i64xor,
			I32Shl | I64Shl => w.i64shl,
			I32ShrS | I64ShrS => w.i64shrs,
			I32ShrU | I64ShrU => w.i64shru,
			I32Rotl | I64Rotl => w.i64rotl,
			I32Rotr | I64Rotr => w.i64rotr,

			// Returning None makes the gas instrumentation fail which we intend for
			// unsupported or unknown instructions. Offchain we might allow indeterminism and hence
			// use the fallback weight for those instructions.
			_ if matches!(self.determinism, Determinism::Relaxed) && w.fallback > 0 => w.fallback,
			_ => return None,
		};
		Some(weight)
	}

	fn memory_grow_cost(&self) -> gas_metering::MemoryGrowCost {
		// We benchmarked the memory.grow instruction with the maximum allowed pages.
		// The cost for growing is therefore already included in the instruction cost.
		gas_metering::MemoryGrowCost::Free
	}

	fn call_per_local_cost(&self) -> u32 {
		self.schedule.instruction_weights.call_per_local
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
