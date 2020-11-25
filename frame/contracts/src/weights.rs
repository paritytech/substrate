// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Weights for pallet_contracts
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0
//! DATE: 2020-11-10, STEPS: [50, ], REPEAT: 20, LOW RANGE: [], HIGH RANGE: []
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128

// Executed Command:
// target/release/substrate
// benchmark
// --chain=dev
// --steps=50
// --repeat=20
// --pallet=pallet_contracts
// --extrinsic=*
// --execution=wasm
// --wasm-execution=compiled
// --heap-pages=4096
// --output=./frame/contracts/src/weights.rs
// --template=./.maintain/frame-weight-template.hbs


#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::{Weight, constants::RocksDbWeight}};
use sp_std::marker::PhantomData;

/// Weight functions needed for pallet_contracts.
pub trait WeightInfo {
	fn update_schedule() -> Weight;
	fn put_code(n: u32, ) -> Weight;
	fn instantiate(n: u32, s: u32, ) -> Weight;
	fn call() -> Weight;
	fn claim_surcharge() -> Weight;
	fn seal_caller(r: u32, ) -> Weight;
	fn seal_address(r: u32, ) -> Weight;
	fn seal_gas_left(r: u32, ) -> Weight;
	fn seal_balance(r: u32, ) -> Weight;
	fn seal_value_transferred(r: u32, ) -> Weight;
	fn seal_minimum_balance(r: u32, ) -> Weight;
	fn seal_tombstone_deposit(r: u32, ) -> Weight;
	fn seal_rent_allowance(r: u32, ) -> Weight;
	fn seal_block_number(r: u32, ) -> Weight;
	fn seal_now(r: u32, ) -> Weight;
	fn seal_weight_to_fee(r: u32, ) -> Weight;
	fn seal_gas(r: u32, ) -> Weight;
	fn seal_input(r: u32, ) -> Weight;
	fn seal_input_per_kb(n: u32, ) -> Weight;
	fn seal_return(r: u32, ) -> Weight;
	fn seal_return_per_kb(n: u32, ) -> Weight;
	fn seal_terminate(r: u32, ) -> Weight;
	fn seal_restore_to(r: u32, ) -> Weight;
	fn seal_restore_to_per_delta(d: u32, ) -> Weight;
	fn seal_random(r: u32, ) -> Weight;
	fn seal_deposit_event(r: u32, ) -> Weight;
	fn seal_deposit_event_per_topic_and_kb(t: u32, n: u32, ) -> Weight;
	fn seal_set_rent_allowance(r: u32, ) -> Weight;
	fn seal_set_storage(r: u32, ) -> Weight;
	fn seal_set_storage_per_kb(n: u32, ) -> Weight;
	fn seal_clear_storage(r: u32, ) -> Weight;
	fn seal_get_storage(r: u32, ) -> Weight;
	fn seal_get_storage_per_kb(n: u32, ) -> Weight;
	fn seal_transfer(r: u32, ) -> Weight;
	fn seal_call(r: u32, ) -> Weight;
	fn seal_call_per_transfer_input_output_kb(t: u32, i: u32, o: u32, ) -> Weight;
	fn seal_instantiate(r: u32, ) -> Weight;
	fn seal_instantiate_per_input_output_salt_kb(i: u32, o: u32, s: u32, ) -> Weight;
	fn seal_hash_sha2_256(r: u32, ) -> Weight;
	fn seal_hash_sha2_256_per_kb(n: u32, ) -> Weight;
	fn seal_hash_keccak_256(r: u32, ) -> Weight;
	fn seal_hash_keccak_256_per_kb(n: u32, ) -> Weight;
	fn seal_hash_blake2_256(r: u32, ) -> Weight;
	fn seal_hash_blake2_256_per_kb(n: u32, ) -> Weight;
	fn seal_hash_blake2_128(r: u32, ) -> Weight;
	fn seal_hash_blake2_128_per_kb(n: u32, ) -> Weight;
	fn instr_i64const(r: u32, ) -> Weight;
	fn instr_i64load(r: u32, ) -> Weight;
	fn instr_i64store(r: u32, ) -> Weight;
	fn instr_select(r: u32, ) -> Weight;
	fn instr_if(r: u32, ) -> Weight;
	fn instr_br(r: u32, ) -> Weight;
	fn instr_br_if(r: u32, ) -> Weight;
	fn instr_br_table(r: u32, ) -> Weight;
	fn instr_br_table_per_entry(e: u32, ) -> Weight;
	fn instr_call(r: u32, ) -> Weight;
	fn instr_call_indirect(r: u32, ) -> Weight;
	fn instr_call_indirect_per_param(p: u32, ) -> Weight;
	fn instr_local_get(r: u32, ) -> Weight;
	fn instr_local_set(r: u32, ) -> Weight;
	fn instr_local_tee(r: u32, ) -> Weight;
	fn instr_global_get(r: u32, ) -> Weight;
	fn instr_global_set(r: u32, ) -> Weight;
	fn instr_memory_current(r: u32, ) -> Weight;
	fn instr_memory_grow(r: u32, ) -> Weight;
	fn instr_i64clz(r: u32, ) -> Weight;
	fn instr_i64ctz(r: u32, ) -> Weight;
	fn instr_i64popcnt(r: u32, ) -> Weight;
	fn instr_i64eqz(r: u32, ) -> Weight;
	fn instr_i64extendsi32(r: u32, ) -> Weight;
	fn instr_i64extendui32(r: u32, ) -> Weight;
	fn instr_i32wrapi64(r: u32, ) -> Weight;
	fn instr_i64eq(r: u32, ) -> Weight;
	fn instr_i64ne(r: u32, ) -> Weight;
	fn instr_i64lts(r: u32, ) -> Weight;
	fn instr_i64ltu(r: u32, ) -> Weight;
	fn instr_i64gts(r: u32, ) -> Weight;
	fn instr_i64gtu(r: u32, ) -> Weight;
	fn instr_i64les(r: u32, ) -> Weight;
	fn instr_i64leu(r: u32, ) -> Weight;
	fn instr_i64ges(r: u32, ) -> Weight;
	fn instr_i64geu(r: u32, ) -> Weight;
	fn instr_i64add(r: u32, ) -> Weight;
	fn instr_i64sub(r: u32, ) -> Weight;
	fn instr_i64mul(r: u32, ) -> Weight;
	fn instr_i64divs(r: u32, ) -> Weight;
	fn instr_i64divu(r: u32, ) -> Weight;
	fn instr_i64rems(r: u32, ) -> Weight;
	fn instr_i64remu(r: u32, ) -> Weight;
	fn instr_i64and(r: u32, ) -> Weight;
	fn instr_i64or(r: u32, ) -> Weight;
	fn instr_i64xor(r: u32, ) -> Weight;
	fn instr_i64shl(r: u32, ) -> Weight;
	fn instr_i64shrs(r: u32, ) -> Weight;
	fn instr_i64shru(r: u32, ) -> Weight;
	fn instr_i64rotl(r: u32, ) -> Weight;
	fn instr_i64rotr(r: u32, ) -> Weight;
}

/// Weights for pallet_contracts using the Substrate node and recommended hardware.
pub struct SubstrateWeight<T>(PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	fn update_schedule() -> Weight {
		(35_214_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	fn put_code(n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((109_242_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn instantiate(n: u32, s: u32, ) -> Weight {
		(195_276_000 as Weight)
			.saturating_add((35_000 as Weight).saturating_mul(n as Weight))
			.saturating_add((2_244_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	fn call() -> Weight {
		(207_142_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn claim_surcharge() -> Weight {
		(489_633_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn seal_caller(r: u32, ) -> Weight {
		(136_550_000 as Weight)
			.saturating_add((373_182_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_address(r: u32, ) -> Weight {
		(136_329_000 as Weight)
			.saturating_add((373_392_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_gas_left(r: u32, ) -> Weight {
		(111_577_000 as Weight)
			.saturating_add((373_536_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_balance(r: u32, ) -> Weight {
		(157_531_000 as Weight)
			.saturating_add((810_382_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
	}
	fn seal_value_transferred(r: u32, ) -> Weight {
		(143_801_000 as Weight)
			.saturating_add((369_769_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_minimum_balance(r: u32, ) -> Weight {
		(133_546_000 as Weight)
			.saturating_add((370_036_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_tombstone_deposit(r: u32, ) -> Weight {
		(138_568_000 as Weight)
			.saturating_add((370_322_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_rent_allowance(r: u32, ) -> Weight {
		(144_431_000 as Weight)
			.saturating_add((851_810_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_block_number(r: u32, ) -> Weight {
		(133_237_000 as Weight)
			.saturating_add((369_156_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_now(r: u32, ) -> Weight {
		(139_700_000 as Weight)
			.saturating_add((368_961_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_weight_to_fee(r: u32, ) -> Weight {
		(149_395_000 as Weight)
			.saturating_add((625_812_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
	}
	fn seal_gas(r: u32, ) -> Weight {
		(125_777_000 as Weight)
			.saturating_add((187_585_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_input(r: u32, ) -> Weight {
		(132_584_000 as Weight)
			.saturating_add((7_661_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_input_per_kb(n: u32, ) -> Weight {
		(143_408_000 as Weight)
			.saturating_add((274_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_return(r: u32, ) -> Weight {
		(126_257_000 as Weight)
			.saturating_add((5_455_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_return_per_kb(n: u32, ) -> Weight {
		(133_286_000 as Weight)
			.saturating_add((698_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_terminate(r: u32, ) -> Weight {
		(130_607_000 as Weight)
			.saturating_add((358_370_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((2 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes((3 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_restore_to(r: u32, ) -> Weight {
		(233_645_000 as Weight)
			.saturating_add((135_355_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().reads((3 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes((4 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_restore_to_per_delta(d: u32, ) -> Weight {
		(74_573_000 as Weight)
			.saturating_add((3_768_682_000 as Weight).saturating_mul(d as Weight))
			.saturating_add(T::DbWeight::get().reads(7 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(d as Weight)))
			.saturating_add(T::DbWeight::get().writes(5 as Weight))
			.saturating_add(T::DbWeight::get().writes((100 as Weight).saturating_mul(d as Weight)))
	}
	fn seal_random(r: u32, ) -> Weight {
		(140_286_000 as Weight)
			.saturating_add((950_890_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
	}
	fn seal_deposit_event(r: u32, ) -> Weight {
		(167_735_000 as Weight)
			.saturating_add((1_375_429_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_deposit_event_per_topic_and_kb(t: u32, n: u32, ) -> Weight {
		(1_715_857_000 as Weight)
			.saturating_add((760_777_000 as Weight).saturating_mul(t as Weight))
			.saturating_add((241_853_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(t as Weight)))
			.saturating_add(T::DbWeight::get().writes((100 as Weight).saturating_mul(t as Weight)))
	}
	fn seal_set_rent_allowance(r: u32, ) -> Weight {
		(156_911_000 as Weight)
			.saturating_add((1_006_139_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	fn seal_set_storage(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((14_938_793_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			.saturating_add(T::DbWeight::get().writes((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_set_storage_per_kb(n: u32, ) -> Weight {
		(2_300_169_000 as Weight)
			.saturating_add((204_543_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn seal_clear_storage(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((5_140_241_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			.saturating_add(T::DbWeight::get().writes((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_get_storage(r: u32, ) -> Weight {
		(45_212_000 as Weight)
			.saturating_add((1_131_504_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_get_storage_per_kb(n: u32, ) -> Weight {
		(885_531_000 as Weight)
			.saturating_add((148_986_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
	}
	fn seal_transfer(r: u32, ) -> Weight {
		(92_276_000 as Weight)
			.saturating_add((6_216_852_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			.saturating_add(T::DbWeight::get().writes((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_call(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((10_734_719_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_call_per_transfer_input_output_kb(t: u32, i: u32, o: u32, ) -> Weight {
		(12_735_614_000 as Weight)
			.saturating_add((2_870_730_000 as Weight).saturating_mul(t as Weight))
			.saturating_add((52_569_000 as Weight).saturating_mul(i as Weight))
			.saturating_add((73_956_000 as Weight).saturating_mul(o as Weight))
			.saturating_add(T::DbWeight::get().reads(105 as Weight))
			.saturating_add(T::DbWeight::get().reads((101 as Weight).saturating_mul(t as Weight)))
			.saturating_add(T::DbWeight::get().writes((101 as Weight).saturating_mul(t as Weight)))
	}
	fn seal_instantiate(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((22_365_908_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().reads((300 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			.saturating_add(T::DbWeight::get().writes((200 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_instantiate_per_input_output_salt_kb(i: u32, o: u32, s: u32, ) -> Weight {
		(18_899_296_000 as Weight)
			.saturating_add((53_289_000 as Weight).saturating_mul(i as Weight))
			.saturating_add((76_026_000 as Weight).saturating_mul(o as Weight))
			.saturating_add((281_097_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(207 as Weight))
			.saturating_add(T::DbWeight::get().writes(202 as Weight))
	}
	fn seal_hash_sha2_256(r: u32, ) -> Weight {
		(136_601_000 as Weight)
			.saturating_add((323_373_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_sha2_256_per_kb(n: u32, ) -> Weight {
		(777_563_000 as Weight)
			.saturating_add((423_353_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_keccak_256(r: u32, ) -> Weight {
		(136_771_000 as Weight)
			.saturating_add((337_881_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_keccak_256_per_kb(n: u32, ) -> Weight {
		(337_906_000 as Weight)
			.saturating_add((336_778_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_blake2_256(r: u32, ) -> Weight {
		(131_040_000 as Weight)
			.saturating_add((312_992_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_blake2_256_per_kb(n: u32, ) -> Weight {
		(693_415_000 as Weight)
			.saturating_add((152_745_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_blake2_128(r: u32, ) -> Weight {
		(135_654_000 as Weight)
			.saturating_add((311_271_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_blake2_128_per_kb(n: u32, ) -> Weight {
		(839_521_000 as Weight)
			.saturating_add((153_146_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn instr_i64const(r: u32, ) -> Weight {
		(26_679_000 as Weight)
			.saturating_add((3_155_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64load(r: u32, ) -> Weight {
		(28_920_000 as Weight)
			.saturating_add((159_343_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64store(r: u32, ) -> Weight {
		(28_928_000 as Weight)
			.saturating_add((227_286_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_select(r: u32, ) -> Weight {
		(26_591_000 as Weight)
			.saturating_add((12_591_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_if(r: u32, ) -> Weight {
		(26_597_000 as Weight)
			.saturating_add((12_258_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_br(r: u32, ) -> Weight {
		(26_586_000 as Weight)
			.saturating_add((5_811_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_br_if(r: u32, ) -> Weight {
		(26_581_000 as Weight)
			.saturating_add((14_058_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_br_table(r: u32, ) -> Weight {
		(26_615_000 as Weight)
			.saturating_add((15_687_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_br_table_per_entry(e: u32, ) -> Weight {
		(40_963_000 as Weight)
			.saturating_add((92_000 as Weight).saturating_mul(e as Weight))
	}
	fn instr_call(r: u32, ) -> Weight {
		(26_880_000 as Weight)
			.saturating_add((97_523_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_call_indirect(r: u32, ) -> Weight {
		(34_628_000 as Weight)
			.saturating_add((201_913_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_call_indirect_per_param(p: u32, ) -> Weight {
		(255_763_000 as Weight)
			.saturating_add((3_612_000 as Weight).saturating_mul(p as Weight))
	}
	fn instr_local_get(r: u32, ) -> Weight {
		(45_954_000 as Weight)
			.saturating_add((3_439_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_local_set(r: u32, ) -> Weight {
		(45_952_000 as Weight)
			.saturating_add((3_601_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_local_tee(r: u32, ) -> Weight {
		(45_883_000 as Weight)
			.saturating_add((5_203_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_global_get(r: u32, ) -> Weight {
		(29_895_000 as Weight)
			.saturating_add((8_221_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_global_set(r: u32, ) -> Weight {
		(29_916_000 as Weight)
			.saturating_add((12_036_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_memory_current(r: u32, ) -> Weight {
		(28_878_000 as Weight)
			.saturating_add((3_794_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_memory_grow(r: u32, ) -> Weight {
		(27_351_000 as Weight)
			.saturating_add((2_302_301_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64clz(r: u32, ) -> Weight {
		(26_535_000 as Weight)
			.saturating_add((5_450_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64ctz(r: u32, ) -> Weight {
		(26_489_000 as Weight)
			.saturating_add((5_410_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64popcnt(r: u32, ) -> Weight {
		(26_576_000 as Weight)
			.saturating_add((5_976_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64eqz(r: u32, ) -> Weight {
		(26_521_000 as Weight)
			.saturating_add((5_465_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64extendsi32(r: u32, ) -> Weight {
		(26_534_000 as Weight)
			.saturating_add((5_375_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64extendui32(r: u32, ) -> Weight {
		(26_560_000 as Weight)
			.saturating_add((5_284_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i32wrapi64(r: u32, ) -> Weight {
		(26_554_000 as Weight)
			.saturating_add((5_358_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64eq(r: u32, ) -> Weight {
		(26_549_000 as Weight)
			.saturating_add((7_402_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64ne(r: u32, ) -> Weight {
		(26_582_000 as Weight)
			.saturating_add((7_266_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64lts(r: u32, ) -> Weight {
		(26_558_000 as Weight)
			.saturating_add((7_293_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64ltu(r: u32, ) -> Weight {
		(26_569_000 as Weight)
			.saturating_add((7_278_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64gts(r: u32, ) -> Weight {
		(26_516_000 as Weight)
			.saturating_add((7_334_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64gtu(r: u32, ) -> Weight {
		(26_561_000 as Weight)
			.saturating_add((7_283_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64les(r: u32, ) -> Weight {
		(26_589_000 as Weight)
			.saturating_add((7_244_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64leu(r: u32, ) -> Weight {
		(26_593_000 as Weight)
			.saturating_add((7_318_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64ges(r: u32, ) -> Weight {
		(26_626_000 as Weight)
			.saturating_add((7_348_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64geu(r: u32, ) -> Weight {
		(26_595_000 as Weight)
			.saturating_add((7_330_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64add(r: u32, ) -> Weight {
		(26_568_000 as Weight)
			.saturating_add((8_657_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64sub(r: u32, ) -> Weight {
		(27_393_000 as Weight)
			.saturating_add((6_743_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64mul(r: u32, ) -> Weight {
		(26_571_000 as Weight)
			.saturating_add((7_329_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64divs(r: u32, ) -> Weight {
		(26_585_000 as Weight)
			.saturating_add((12_977_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64divu(r: u32, ) -> Weight {
		(26_554_000 as Weight)
			.saturating_add((11_955_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64rems(r: u32, ) -> Weight {
		(26_570_000 as Weight)
			.saturating_add((12_903_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64remu(r: u32, ) -> Weight {
		(26_561_000 as Weight)
			.saturating_add((12_112_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64and(r: u32, ) -> Weight {
		(26_587_000 as Weight)
			.saturating_add((7_411_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64or(r: u32, ) -> Weight {
		(26_588_000 as Weight)
			.saturating_add((7_479_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64xor(r: u32, ) -> Weight {
		(26_541_000 as Weight)
			.saturating_add((7_386_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64shl(r: u32, ) -> Weight {
		(26_562_000 as Weight)
			.saturating_add((7_263_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64shrs(r: u32, ) -> Weight {
		(26_569_000 as Weight)
			.saturating_add((7_353_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64shru(r: u32, ) -> Weight {
		(26_533_000 as Weight)
			.saturating_add((7_342_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64rotl(r: u32, ) -> Weight {
		(26_545_000 as Weight)
			.saturating_add((7_362_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64rotr(r: u32, ) -> Weight {
		(26_535_000 as Weight)
			.saturating_add((7_330_000 as Weight).saturating_mul(r as Weight))
	}
}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn update_schedule() -> Weight {
		(35_214_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	fn put_code(n: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((109_242_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	fn instantiate(n: u32, s: u32, ) -> Weight {
		(195_276_000 as Weight)
			.saturating_add((35_000 as Weight).saturating_mul(n as Weight))
			.saturating_add((2_244_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
	}
	fn call() -> Weight {
		(207_142_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	fn claim_surcharge() -> Weight {
		(489_633_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	fn seal_caller(r: u32, ) -> Weight {
		(136_550_000 as Weight)
			.saturating_add((373_182_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_address(r: u32, ) -> Weight {
		(136_329_000 as Weight)
			.saturating_add((373_392_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_gas_left(r: u32, ) -> Weight {
		(111_577_000 as Weight)
			.saturating_add((373_536_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_balance(r: u32, ) -> Weight {
		(157_531_000 as Weight)
			.saturating_add((810_382_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
	}
	fn seal_value_transferred(r: u32, ) -> Weight {
		(143_801_000 as Weight)
			.saturating_add((369_769_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_minimum_balance(r: u32, ) -> Weight {
		(133_546_000 as Weight)
			.saturating_add((370_036_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_tombstone_deposit(r: u32, ) -> Weight {
		(138_568_000 as Weight)
			.saturating_add((370_322_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_rent_allowance(r: u32, ) -> Weight {
		(144_431_000 as Weight)
			.saturating_add((851_810_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_block_number(r: u32, ) -> Weight {
		(133_237_000 as Weight)
			.saturating_add((369_156_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_now(r: u32, ) -> Weight {
		(139_700_000 as Weight)
			.saturating_add((368_961_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_weight_to_fee(r: u32, ) -> Weight {
		(149_395_000 as Weight)
			.saturating_add((625_812_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
	}
	fn seal_gas(r: u32, ) -> Weight {
		(125_777_000 as Weight)
			.saturating_add((187_585_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_input(r: u32, ) -> Weight {
		(132_584_000 as Weight)
			.saturating_add((7_661_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_input_per_kb(n: u32, ) -> Weight {
		(143_408_000 as Weight)
			.saturating_add((274_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_return(r: u32, ) -> Weight {
		(126_257_000 as Weight)
			.saturating_add((5_455_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_return_per_kb(n: u32, ) -> Weight {
		(133_286_000 as Weight)
			.saturating_add((698_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_terminate(r: u32, ) -> Weight {
		(130_607_000 as Weight)
			.saturating_add((358_370_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((2 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes((3 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_restore_to(r: u32, ) -> Weight {
		(233_645_000 as Weight)
			.saturating_add((135_355_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().reads((3 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes((4 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_restore_to_per_delta(d: u32, ) -> Weight {
		(74_573_000 as Weight)
			.saturating_add((3_768_682_000 as Weight).saturating_mul(d as Weight))
			.saturating_add(RocksDbWeight::get().reads(7 as Weight))
			.saturating_add(RocksDbWeight::get().reads((100 as Weight).saturating_mul(d as Weight)))
			.saturating_add(RocksDbWeight::get().writes(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes((100 as Weight).saturating_mul(d as Weight)))
	}
	fn seal_random(r: u32, ) -> Weight {
		(140_286_000 as Weight)
			.saturating_add((950_890_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
	}
	fn seal_deposit_event(r: u32, ) -> Weight {
		(167_735_000 as Weight)
			.saturating_add((1_375_429_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_deposit_event_per_topic_and_kb(t: u32, n: u32, ) -> Weight {
		(1_715_857_000 as Weight)
			.saturating_add((760_777_000 as Weight).saturating_mul(t as Weight))
			.saturating_add((241_853_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((100 as Weight).saturating_mul(t as Weight)))
			.saturating_add(RocksDbWeight::get().writes((100 as Weight).saturating_mul(t as Weight)))
	}
	fn seal_set_rent_allowance(r: u32, ) -> Weight {
		(156_911_000 as Weight)
			.saturating_add((1_006_139_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
	}
	fn seal_set_storage(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((14_938_793_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_set_storage_per_kb(n: u32, ) -> Weight {
		(2_300_169_000 as Weight)
			.saturating_add((204_543_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
	}
	fn seal_clear_storage(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((5_140_241_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_get_storage(r: u32, ) -> Weight {
		(45_212_000 as Weight)
			.saturating_add((1_131_504_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_get_storage_per_kb(n: u32, ) -> Weight {
		(885_531_000 as Weight)
			.saturating_add((148_986_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
	}
	fn seal_transfer(r: u32, ) -> Weight {
		(92_276_000 as Weight)
			.saturating_add((6_216_852_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_call(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((10_734_719_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_call_per_transfer_input_output_kb(t: u32, i: u32, o: u32, ) -> Weight {
		(12_735_614_000 as Weight)
			.saturating_add((2_870_730_000 as Weight).saturating_mul(t as Weight))
			.saturating_add((52_569_000 as Weight).saturating_mul(i as Weight))
			.saturating_add((73_956_000 as Weight).saturating_mul(o as Weight))
			.saturating_add(RocksDbWeight::get().reads(105 as Weight))
			.saturating_add(RocksDbWeight::get().reads((101 as Weight).saturating_mul(t as Weight)))
			.saturating_add(RocksDbWeight::get().writes((101 as Weight).saturating_mul(t as Weight)))
	}
	fn seal_instantiate(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((22_365_908_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().reads((300 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((200 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_instantiate_per_input_output_salt_kb(i: u32, o: u32, s: u32, ) -> Weight {
		(18_899_296_000 as Weight)
			.saturating_add((53_289_000 as Weight).saturating_mul(i as Weight))
			.saturating_add((76_026_000 as Weight).saturating_mul(o as Weight))
			.saturating_add((281_097_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(RocksDbWeight::get().reads(207 as Weight))
			.saturating_add(RocksDbWeight::get().writes(202 as Weight))
	}
	fn seal_hash_sha2_256(r: u32, ) -> Weight {
		(136_601_000 as Weight)
			.saturating_add((323_373_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_sha2_256_per_kb(n: u32, ) -> Weight {
		(777_563_000 as Weight)
			.saturating_add((423_353_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_keccak_256(r: u32, ) -> Weight {
		(136_771_000 as Weight)
			.saturating_add((337_881_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_keccak_256_per_kb(n: u32, ) -> Weight {
		(337_906_000 as Weight)
			.saturating_add((336_778_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_blake2_256(r: u32, ) -> Weight {
		(131_040_000 as Weight)
			.saturating_add((312_992_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_blake2_256_per_kb(n: u32, ) -> Weight {
		(693_415_000 as Weight)
			.saturating_add((152_745_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_blake2_128(r: u32, ) -> Weight {
		(135_654_000 as Weight)
			.saturating_add((311_271_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_blake2_128_per_kb(n: u32, ) -> Weight {
		(839_521_000 as Weight)
			.saturating_add((153_146_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
	}
	fn instr_i64const(r: u32, ) -> Weight {
		(26_679_000 as Weight)
			.saturating_add((3_155_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64load(r: u32, ) -> Weight {
		(28_920_000 as Weight)
			.saturating_add((159_343_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64store(r: u32, ) -> Weight {
		(28_928_000 as Weight)
			.saturating_add((227_286_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_select(r: u32, ) -> Weight {
		(26_591_000 as Weight)
			.saturating_add((12_591_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_if(r: u32, ) -> Weight {
		(26_597_000 as Weight)
			.saturating_add((12_258_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_br(r: u32, ) -> Weight {
		(26_586_000 as Weight)
			.saturating_add((5_811_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_br_if(r: u32, ) -> Weight {
		(26_581_000 as Weight)
			.saturating_add((14_058_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_br_table(r: u32, ) -> Weight {
		(26_615_000 as Weight)
			.saturating_add((15_687_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_br_table_per_entry(e: u32, ) -> Weight {
		(40_963_000 as Weight)
			.saturating_add((92_000 as Weight).saturating_mul(e as Weight))
	}
	fn instr_call(r: u32, ) -> Weight {
		(26_880_000 as Weight)
			.saturating_add((97_523_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_call_indirect(r: u32, ) -> Weight {
		(34_628_000 as Weight)
			.saturating_add((201_913_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_call_indirect_per_param(p: u32, ) -> Weight {
		(255_763_000 as Weight)
			.saturating_add((3_612_000 as Weight).saturating_mul(p as Weight))
	}
	fn instr_local_get(r: u32, ) -> Weight {
		(45_954_000 as Weight)
			.saturating_add((3_439_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_local_set(r: u32, ) -> Weight {
		(45_952_000 as Weight)
			.saturating_add((3_601_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_local_tee(r: u32, ) -> Weight {
		(45_883_000 as Weight)
			.saturating_add((5_203_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_global_get(r: u32, ) -> Weight {
		(29_895_000 as Weight)
			.saturating_add((8_221_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_global_set(r: u32, ) -> Weight {
		(29_916_000 as Weight)
			.saturating_add((12_036_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_memory_current(r: u32, ) -> Weight {
		(28_878_000 as Weight)
			.saturating_add((3_794_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_memory_grow(r: u32, ) -> Weight {
		(27_351_000 as Weight)
			.saturating_add((2_302_301_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64clz(r: u32, ) -> Weight {
		(26_535_000 as Weight)
			.saturating_add((5_450_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64ctz(r: u32, ) -> Weight {
		(26_489_000 as Weight)
			.saturating_add((5_410_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64popcnt(r: u32, ) -> Weight {
		(26_576_000 as Weight)
			.saturating_add((5_976_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64eqz(r: u32, ) -> Weight {
		(26_521_000 as Weight)
			.saturating_add((5_465_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64extendsi32(r: u32, ) -> Weight {
		(26_534_000 as Weight)
			.saturating_add((5_375_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64extendui32(r: u32, ) -> Weight {
		(26_560_000 as Weight)
			.saturating_add((5_284_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i32wrapi64(r: u32, ) -> Weight {
		(26_554_000 as Weight)
			.saturating_add((5_358_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64eq(r: u32, ) -> Weight {
		(26_549_000 as Weight)
			.saturating_add((7_402_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64ne(r: u32, ) -> Weight {
		(26_582_000 as Weight)
			.saturating_add((7_266_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64lts(r: u32, ) -> Weight {
		(26_558_000 as Weight)
			.saturating_add((7_293_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64ltu(r: u32, ) -> Weight {
		(26_569_000 as Weight)
			.saturating_add((7_278_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64gts(r: u32, ) -> Weight {
		(26_516_000 as Weight)
			.saturating_add((7_334_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64gtu(r: u32, ) -> Weight {
		(26_561_000 as Weight)
			.saturating_add((7_283_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64les(r: u32, ) -> Weight {
		(26_589_000 as Weight)
			.saturating_add((7_244_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64leu(r: u32, ) -> Weight {
		(26_593_000 as Weight)
			.saturating_add((7_318_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64ges(r: u32, ) -> Weight {
		(26_626_000 as Weight)
			.saturating_add((7_348_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64geu(r: u32, ) -> Weight {
		(26_595_000 as Weight)
			.saturating_add((7_330_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64add(r: u32, ) -> Weight {
		(26_568_000 as Weight)
			.saturating_add((8_657_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64sub(r: u32, ) -> Weight {
		(27_393_000 as Weight)
			.saturating_add((6_743_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64mul(r: u32, ) -> Weight {
		(26_571_000 as Weight)
			.saturating_add((7_329_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64divs(r: u32, ) -> Weight {
		(26_585_000 as Weight)
			.saturating_add((12_977_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64divu(r: u32, ) -> Weight {
		(26_554_000 as Weight)
			.saturating_add((11_955_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64rems(r: u32, ) -> Weight {
		(26_570_000 as Weight)
			.saturating_add((12_903_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64remu(r: u32, ) -> Weight {
		(26_561_000 as Weight)
			.saturating_add((12_112_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64and(r: u32, ) -> Weight {
		(26_587_000 as Weight)
			.saturating_add((7_411_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64or(r: u32, ) -> Weight {
		(26_588_000 as Weight)
			.saturating_add((7_479_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64xor(r: u32, ) -> Weight {
		(26_541_000 as Weight)
			.saturating_add((7_386_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64shl(r: u32, ) -> Weight {
		(26_562_000 as Weight)
			.saturating_add((7_263_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64shrs(r: u32, ) -> Weight {
		(26_569_000 as Weight)
			.saturating_add((7_353_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64shru(r: u32, ) -> Weight {
		(26_533_000 as Weight)
			.saturating_add((7_342_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64rotl(r: u32, ) -> Weight {
		(26_545_000 as Weight)
			.saturating_add((7_362_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64rotr(r: u32, ) -> Weight {
		(26_535_000 as Weight)
			.saturating_add((7_330_000 as Weight).saturating_mul(r as Weight))
	}
}
