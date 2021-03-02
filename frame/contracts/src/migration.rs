// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

use crate::{Config, Weight, CurrentSchedule, Pallet, Schedule};
use codec::{Encode, Decode};
use frame_support::traits::{GetPalletVersion, PalletVersion, Get};
use sp_std::marker::PhantomData;

pub fn migrate<T: Config>() -> Weight {
	let mut weight: Weight = 0;

	match <Pallet<T>>::storage_version() {
		Some(version) if version == PalletVersion::new(3, 0, 0) => {
			weight = weight.saturating_add(T::DbWeight::get().reads_writes(1, 1));
			let _ = <CurrentSchedule<T>>::translate::<v3_0::Schedule<T>, _>(|old| {
				if let Some(old) = old {
					Some(Schedule {
						version: old.version.saturating_add(1),
						// Default limits were not decreased. Therefore it is OK to overwrite
						// the schedule with the new defaults.
						.. Default::default()
					})
				} else {
					None
				}
			});
		}
		_ => (),
	}

	weight
}

mod v3_0 {
	use super::*;

	#[derive(Clone, Encode, Decode, PartialEq, Eq)]
	pub struct Schedule<T: Config> {
		pub version: u32,
		pub enable_println: bool,
		pub limits: Limits,
		pub instruction_weights: InstructionWeights<T>,
		pub host_fn_weights: HostFnWeights<T>,
	}

	#[derive(Clone, Encode, Decode, PartialEq, Eq)]
	pub struct Limits {
		pub event_topics: u32,
		pub stack_height: u32,
		pub globals: u32,
		pub parameters: u32,
		pub memory_pages: u32,
		pub table_size: u32,
		pub br_table_size: u32,
		pub subject_len: u32,
	}

	#[derive(Clone, Encode, Decode, PartialEq, Eq)]
	pub struct InstructionWeights<T: Config> {
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
		pub call_indirect_per_param: u32,
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
		pub _phantom: PhantomData<T>,
	}

	#[derive(Clone, Encode, Decode, PartialEq, Eq)]
	pub struct HostFnWeights<T: Config> {
		pub caller: Weight,
		pub address: Weight,
		pub gas_left: Weight,
		pub balance: Weight,
		pub value_transferred: Weight,
		pub minimum_balance: Weight,
		pub tombstone_deposit: Weight,
		pub rent_allowance: Weight,
		pub block_number: Weight,
		pub now: Weight,
		pub weight_to_fee: Weight,
		pub gas: Weight,
		pub input: Weight,
		pub input_per_byte: Weight,
		pub r#return: Weight,
		pub return_per_byte: Weight,
		pub terminate: Weight,
		pub terminate_per_code_byte: Weight,
		pub restore_to: Weight,
		pub restore_to_per_caller_code_byte: Weight,
		pub restore_to_per_tombstone_code_byte: Weight,
		pub restore_to_per_delta: Weight,
		pub random: Weight,
		pub deposit_event: Weight,
		pub deposit_event_per_topic: Weight,
		pub deposit_event_per_byte: Weight,
		pub set_rent_allowance: Weight,
		pub set_storage: Weight,
		pub set_storage_per_byte: Weight,
		pub clear_storage: Weight,
		pub get_storage: Weight,
		pub get_storage_per_byte: Weight,
		pub transfer: Weight,
		pub call: Weight,
		pub call_per_code_byte: Weight,
		pub call_transfer_surcharge: Weight,
		pub call_per_input_byte: Weight,
		pub call_per_output_byte: Weight,
		pub instantiate: Weight,
		pub instantiate_per_code_byte: Weight,
		pub instantiate_per_input_byte: Weight,
		pub instantiate_per_output_byte: Weight,
		pub instantiate_per_salt_byte: Weight,
		pub hash_sha2_256: Weight,
		pub hash_sha2_256_per_byte: Weight,
		pub hash_keccak_256: Weight,
		pub hash_keccak_256_per_byte: Weight,
		pub hash_blake2_256: Weight,
		pub hash_blake2_256_per_byte: Weight,
		pub hash_blake2_128: Weight,
		pub hash_blake2_128_per_byte: Weight,
		pub _phantom: PhantomData<T>
	}
}
