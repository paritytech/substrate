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
//! DATE: 2020-10-27, STEPS: [50, ], REPEAT: 20, LOW RANGE: [], HIGH RANGE: []
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
	fn instantiate(n: u32, ) -> Weight;
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
	fn seal_instantiate_per_input_output_kb(i: u32, o: u32, ) -> Weight;
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
impl<T: frame_system::Trait> WeightInfo for SubstrateWeight<T> {
	fn update_schedule() -> Weight {
		(33_160_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn put_code(n: u32, ) -> Weight {
		(5_975_000 as Weight)
			.saturating_add((108_953_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn instantiate(n: u32, ) -> Weight {
		(218_223_000 as Weight)
			.saturating_add((1_007_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
			
	}
	fn call() -> Weight {
		(201_492_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn claim_surcharge() -> Weight {
		(449_203_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn seal_caller(r: u32, ) -> Weight {
		(136_650_000 as Weight)
			.saturating_add((364_640_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_address(r: u32, ) -> Weight {
		(144_167_000 as Weight)
			.saturating_add((365_328_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_gas_left(r: u32, ) -> Weight {
		(138_458_000 as Weight)
			.saturating_add((361_076_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_balance(r: u32, ) -> Weight {
		(147_909_000 as Weight)
			.saturating_add((792_169_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			
	}
	fn seal_value_transferred(r: u32, ) -> Weight {
		(148_524_000 as Weight)
			.saturating_add((361_842_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_minimum_balance(r: u32, ) -> Weight {
		(139_795_000 as Weight)
			.saturating_add((366_013_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_tombstone_deposit(r: u32, ) -> Weight {
		(140_557_000 as Weight)
			.saturating_add((362_687_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_rent_allowance(r: u32, ) -> Weight {
		(152_989_000 as Weight)
			.saturating_add((836_876_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_block_number(r: u32, ) -> Weight {
		(140_228_000 as Weight)
			.saturating_add((360_561_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_now(r: u32, ) -> Weight {
		(148_776_000 as Weight)
			.saturating_add((361_712_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_weight_to_fee(r: u32, ) -> Weight {
		(126_903_000 as Weight)
			.saturating_add((603_100_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			
	}
	fn seal_gas(r: u32, ) -> Weight {
		(125_712_000 as Weight)
			.saturating_add((184_450_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_input(r: u32, ) -> Weight {
		(136_175_000 as Weight)
			.saturating_add((7_489_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_input_per_kb(n: u32, ) -> Weight {
		(145_434_000 as Weight)
			.saturating_add((276_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_return(r: u32, ) -> Weight {
		(124_788_000 as Weight)
			.saturating_add((5_696_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_return_per_kb(n: u32, ) -> Weight {
		(133_483_000 as Weight)
			.saturating_add((675_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_terminate(r: u32, ) -> Weight {
		(135_387_000 as Weight)
			.saturating_add((338_395_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((2 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes((3 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_restore_to(r: u32, ) -> Weight {
		(227_617_000 as Weight)
			.saturating_add((132_493_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().reads((3 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes((4 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_restore_to_per_delta(d: u32, ) -> Weight {
		(15_263_000 as Weight)
			.saturating_add((3_732_219_000 as Weight).saturating_mul(d as Weight))
			.saturating_add(T::DbWeight::get().reads(7 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(d as Weight)))
			.saturating_add(T::DbWeight::get().writes(5 as Weight))
			.saturating_add(T::DbWeight::get().writes((100 as Weight).saturating_mul(d as Weight)))
	}
	fn seal_random(r: u32, ) -> Weight {
		(236_391_000 as Weight)
			.saturating_add((913_452_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			
	}
	fn seal_deposit_event(r: u32, ) -> Weight {
		(140_845_000 as Weight)
			.saturating_add((1_322_796_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_deposit_event_per_topic_and_kb(t: u32, n: u32, ) -> Weight {
		(1_651_556_000 as Weight)
			.saturating_add((737_421_000 as Weight).saturating_mul(t as Weight))
			.saturating_add((244_183_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(t as Weight)))
			.saturating_add(T::DbWeight::get().writes((100 as Weight).saturating_mul(t as Weight)))
	}
	fn seal_set_rent_allowance(r: u32, ) -> Weight {
		(151_091_000 as Weight)
			.saturating_add((983_375_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			
	}
	fn seal_set_storage(r: u32, ) -> Weight {
		(460_478_000 as Weight)
			.saturating_add((14_824_033_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			.saturating_add(T::DbWeight::get().writes((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_set_storage_per_kb(n: u32, ) -> Weight {
		(2_255_458_000 as Weight)
			.saturating_add((204_470_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			
	}
	fn seal_clear_storage(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((5_052_125_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			.saturating_add(T::DbWeight::get().writes((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_get_storage(r: u32, ) -> Weight {
		(95_473_000 as Weight)
			.saturating_add((1_044_784_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			
	}
	fn seal_get_storage_per_kb(n: u32, ) -> Weight {
		(860_080_000 as Weight)
			.saturating_add((146_913_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			
	}
	fn seal_transfer(r: u32, ) -> Weight {
		(107_119_000 as Weight)
			.saturating_add((5_993_434_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			.saturating_add(T::DbWeight::get().writes((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_call(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((10_533_320_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			
	}
	fn seal_call_per_transfer_input_output_kb(t: u32, i: u32, o: u32, ) -> Weight {
		(9_839_633_000 as Weight)
			.saturating_add((5_580_035_000 as Weight).saturating_mul(t as Weight))
			.saturating_add((53_716_000 as Weight).saturating_mul(i as Weight))
			.saturating_add((73_668_000 as Weight).saturating_mul(o as Weight))
			.saturating_add(T::DbWeight::get().reads(105 as Weight))
			.saturating_add(T::DbWeight::get().reads((101 as Weight).saturating_mul(t as Weight)))
			.saturating_add(T::DbWeight::get().writes((101 as Weight).saturating_mul(t as Weight)))
	}
	fn seal_instantiate(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((21_856_497_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().reads((300 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			.saturating_add(T::DbWeight::get().writes((200 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_instantiate_per_input_output_kb(i: u32, o: u32, ) -> Weight {
		(18_796_671_000 as Weight)
			.saturating_add((156_269_000 as Weight).saturating_mul(i as Weight))
			.saturating_add((74_645_000 as Weight).saturating_mul(o as Weight))
			.saturating_add(T::DbWeight::get().reads(207 as Weight))
			.saturating_add(T::DbWeight::get().writes(202 as Weight))
			
	}
	fn seal_hash_sha2_256(r: u32, ) -> Weight {
		(132_190_000 as Weight)
			.saturating_add((319_943_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_hash_sha2_256_per_kb(n: u32, ) -> Weight {
		(747_208_000 as Weight)
			.saturating_add((421_808_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_hash_keccak_256(r: u32, ) -> Weight {
		(139_235_000 as Weight)
			.saturating_add((333_792_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_hash_keccak_256_per_kb(n: u32, ) -> Weight {
		(543_256_000 as Weight)
			.saturating_add((334_383_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_hash_blake2_256(r: u32, ) -> Weight {
		(142_704_000 as Weight)
			.saturating_add((305_513_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_hash_blake2_256_per_kb(n: u32, ) -> Weight {
		(592_813_000 as Weight)
			.saturating_add((151_270_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_hash_blake2_128(r: u32, ) -> Weight {
		(139_921_000 as Weight)
			.saturating_add((304_746_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn seal_hash_blake2_128_per_kb(n: u32, ) -> Weight {
		(544_524_000 as Weight)
			.saturating_add((151_549_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			
	}
	fn instr_i64const(r: u32, ) -> Weight {
		(24_652_000 as Weight)
			.saturating_add((3_306_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64load(r: u32, ) -> Weight {
		(27_131_000 as Weight)
			.saturating_add((162_220_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64store(r: u32, ) -> Weight {
		(27_086_000 as Weight)
			.saturating_add((230_977_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_select(r: u32, ) -> Weight {
		(24_656_000 as Weight)
			.saturating_add((12_570_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_if(r: u32, ) -> Weight {
		(24_643_000 as Weight)
			.saturating_add((12_442_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_br(r: u32, ) -> Weight {
		(24_589_000 as Weight)
			.saturating_add((6_237_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_br_if(r: u32, ) -> Weight {
		(24_650_000 as Weight)
			.saturating_add((14_393_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_br_table(r: u32, ) -> Weight {
		(24_689_000 as Weight)
			.saturating_add((15_706_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_br_table_per_entry(e: u32, ) -> Weight {
		(40_129_000 as Weight)
			.saturating_add((83_000 as Weight).saturating_mul(e as Weight))
			
	}
	fn instr_call(r: u32, ) -> Weight {
		(24_904_000 as Weight)
			.saturating_add((96_429_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_call_indirect(r: u32, ) -> Weight {
		(32_540_000 as Weight)
			.saturating_add((201_773_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_call_indirect_per_param(p: u32, ) -> Weight {
		(248_700_000 as Weight)
			.saturating_add((3_705_000 as Weight).saturating_mul(p as Weight))
			
	}
	fn instr_local_get(r: u32, ) -> Weight {
		(42_081_000 as Weight)
			.saturating_add((3_548_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_local_set(r: u32, ) -> Weight {
		(42_128_000 as Weight)
			.saturating_add((3_678_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_local_tee(r: u32, ) -> Weight {
		(42_073_000 as Weight)
			.saturating_add((5_212_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_global_get(r: u32, ) -> Weight {
		(28_182_000 as Weight)
			.saturating_add((8_180_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_global_set(r: u32, ) -> Weight {
		(28_060_000 as Weight)
			.saturating_add((12_081_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_memory_current(r: u32, ) -> Weight {
		(27_113_000 as Weight)
			.saturating_add((3_802_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_memory_grow(r: u32, ) -> Weight {
		(25_521_000 as Weight)
			.saturating_add((2_288_295_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64clz(r: u32, ) -> Weight {
		(24_662_000 as Weight)
			.saturating_add((5_497_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64ctz(r: u32, ) -> Weight {
		(24_647_000 as Weight)
			.saturating_add((5_556_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64popcnt(r: u32, ) -> Weight {
		(24_646_000 as Weight)
			.saturating_add((6_138_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64eqz(r: u32, ) -> Weight {
		(24_649_000 as Weight)
			.saturating_add((5_477_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64extendsi32(r: u32, ) -> Weight {
		(24_655_000 as Weight)
			.saturating_add((5_414_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64extendui32(r: u32, ) -> Weight {
		(24_619_000 as Weight)
			.saturating_add((5_434_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i32wrapi64(r: u32, ) -> Weight {
		(24_654_000 as Weight)
			.saturating_add((5_483_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64eq(r: u32, ) -> Weight {
		(24_690_000 as Weight)
			.saturating_add((7_485_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64ne(r: u32, ) -> Weight {
		(24_652_000 as Weight)
			.saturating_add((7_468_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64lts(r: u32, ) -> Weight {
		(24_667_000 as Weight)
			.saturating_add((7_426_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64ltu(r: u32, ) -> Weight {
		(24_693_000 as Weight)
			.saturating_add((7_393_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64gts(r: u32, ) -> Weight {
		(24_675_000 as Weight)
			.saturating_add((7_407_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64gtu(r: u32, ) -> Weight {
		(24_697_000 as Weight)
			.saturating_add((7_392_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64les(r: u32, ) -> Weight {
		(24_646_000 as Weight)
			.saturating_add((7_420_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64leu(r: u32, ) -> Weight {
		(24_683_000 as Weight)
			.saturating_add((7_404_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64ges(r: u32, ) -> Weight {
		(24_685_000 as Weight)
			.saturating_add((7_461_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64geu(r: u32, ) -> Weight {
		(25_147_000 as Weight)
			.saturating_add((7_003_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64add(r: u32, ) -> Weight {
		(24_705_000 as Weight)
			.saturating_add((7_483_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64sub(r: u32, ) -> Weight {
		(24_675_000 as Weight)
			.saturating_add((7_377_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64mul(r: u32, ) -> Weight {
		(24_680_000 as Weight)
			.saturating_add((7_376_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64divs(r: u32, ) -> Weight {
		(24_660_000 as Weight)
			.saturating_add((13_091_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64divu(r: u32, ) -> Weight {
		(24_643_000 as Weight)
			.saturating_add((12_109_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64rems(r: u32, ) -> Weight {
		(24_615_000 as Weight)
			.saturating_add((13_049_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64remu(r: u32, ) -> Weight {
		(24_696_000 as Weight)
			.saturating_add((12_039_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64and(r: u32, ) -> Weight {
		(24_683_000 as Weight)
			.saturating_add((7_314_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64or(r: u32, ) -> Weight {
		(24_657_000 as Weight)
			.saturating_add((7_401_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64xor(r: u32, ) -> Weight {
		(24_661_000 as Weight)
			.saturating_add((7_347_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64shl(r: u32, ) -> Weight {
		(24_644_000 as Weight)
			.saturating_add((7_389_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64shrs(r: u32, ) -> Weight {
		(24_643_000 as Weight)
			.saturating_add((7_416_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64shru(r: u32, ) -> Weight {
		(24_634_000 as Weight)
			.saturating_add((7_392_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64rotl(r: u32, ) -> Weight {
		(24_618_000 as Weight)
			.saturating_add((7_452_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64rotr(r: u32, ) -> Weight {
		(24_618_000 as Weight)
			.saturating_add((7_447_000 as Weight).saturating_mul(r as Weight))
			
	}
	
}

// For backwards compatibility and tests
impl WeightInfo for () {
	fn update_schedule() -> Weight {
		(33_160_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn put_code(n: u32, ) -> Weight {
		(5_975_000 as Weight)
			.saturating_add((108_953_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn instantiate(n: u32, ) -> Weight {
		(218_223_000 as Weight)
			.saturating_add((1_007_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().writes(3 as Weight))
			
	}
	fn call() -> Weight {
		(201_492_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn claim_surcharge() -> Weight {
		(449_203_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(3 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn seal_caller(r: u32, ) -> Weight {
		(136_650_000 as Weight)
			.saturating_add((364_640_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_address(r: u32, ) -> Weight {
		(144_167_000 as Weight)
			.saturating_add((365_328_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_gas_left(r: u32, ) -> Weight {
		(138_458_000 as Weight)
			.saturating_add((361_076_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_balance(r: u32, ) -> Weight {
		(147_909_000 as Weight)
			.saturating_add((792_169_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			
	}
	fn seal_value_transferred(r: u32, ) -> Weight {
		(148_524_000 as Weight)
			.saturating_add((361_842_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_minimum_balance(r: u32, ) -> Weight {
		(139_795_000 as Weight)
			.saturating_add((366_013_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_tombstone_deposit(r: u32, ) -> Weight {
		(140_557_000 as Weight)
			.saturating_add((362_687_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_rent_allowance(r: u32, ) -> Weight {
		(152_989_000 as Weight)
			.saturating_add((836_876_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_block_number(r: u32, ) -> Weight {
		(140_228_000 as Weight)
			.saturating_add((360_561_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_now(r: u32, ) -> Weight {
		(148_776_000 as Weight)
			.saturating_add((361_712_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_weight_to_fee(r: u32, ) -> Weight {
		(126_903_000 as Weight)
			.saturating_add((603_100_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			
	}
	fn seal_gas(r: u32, ) -> Weight {
		(125_712_000 as Weight)
			.saturating_add((184_450_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_input(r: u32, ) -> Weight {
		(136_175_000 as Weight)
			.saturating_add((7_489_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_input_per_kb(n: u32, ) -> Weight {
		(145_434_000 as Weight)
			.saturating_add((276_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_return(r: u32, ) -> Weight {
		(124_788_000 as Weight)
			.saturating_add((5_696_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_return_per_kb(n: u32, ) -> Weight {
		(133_483_000 as Weight)
			.saturating_add((675_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_terminate(r: u32, ) -> Weight {
		(135_387_000 as Weight)
			.saturating_add((338_395_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((2 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes((3 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_restore_to(r: u32, ) -> Weight {
		(227_617_000 as Weight)
			.saturating_add((132_493_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().reads((3 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes((4 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_restore_to_per_delta(d: u32, ) -> Weight {
		(15_263_000 as Weight)
			.saturating_add((3_732_219_000 as Weight).saturating_mul(d as Weight))
			.saturating_add(RocksDbWeight::get().reads(7 as Weight))
			.saturating_add(RocksDbWeight::get().reads((100 as Weight).saturating_mul(d as Weight)))
			.saturating_add(RocksDbWeight::get().writes(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes((100 as Weight).saturating_mul(d as Weight)))
	}
	fn seal_random(r: u32, ) -> Weight {
		(236_391_000 as Weight)
			.saturating_add((913_452_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			
	}
	fn seal_deposit_event(r: u32, ) -> Weight {
		(140_845_000 as Weight)
			.saturating_add((1_322_796_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_deposit_event_per_topic_and_kb(t: u32, n: u32, ) -> Weight {
		(1_651_556_000 as Weight)
			.saturating_add((737_421_000 as Weight).saturating_mul(t as Weight))
			.saturating_add((244_183_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((100 as Weight).saturating_mul(t as Weight)))
			.saturating_add(RocksDbWeight::get().writes((100 as Weight).saturating_mul(t as Weight)))
	}
	fn seal_set_rent_allowance(r: u32, ) -> Weight {
		(151_091_000 as Weight)
			.saturating_add((983_375_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			
	}
	fn seal_set_storage(r: u32, ) -> Weight {
		(460_478_000 as Weight)
			.saturating_add((14_824_033_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_set_storage_per_kb(n: u32, ) -> Weight {
		(2_255_458_000 as Weight)
			.saturating_add((204_470_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			
	}
	fn seal_clear_storage(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((5_052_125_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_get_storage(r: u32, ) -> Weight {
		(95_473_000 as Weight)
			.saturating_add((1_044_784_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			.saturating_add(RocksDbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			
	}
	fn seal_get_storage_per_kb(n: u32, ) -> Weight {
		(860_080_000 as Weight)
			.saturating_add((146_913_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			
	}
	fn seal_transfer(r: u32, ) -> Weight {
		(107_119_000 as Weight)
			.saturating_add((5_993_434_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(1 as Weight))
			.saturating_add(RocksDbWeight::get().writes((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_call(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((10_533_320_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(5 as Weight))
			.saturating_add(RocksDbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			
	}
	fn seal_call_per_transfer_input_output_kb(t: u32, i: u32, o: u32, ) -> Weight {
		(9_839_633_000 as Weight)
			.saturating_add((5_580_035_000 as Weight).saturating_mul(t as Weight))
			.saturating_add((53_716_000 as Weight).saturating_mul(i as Weight))
			.saturating_add((73_668_000 as Weight).saturating_mul(o as Weight))
			.saturating_add(RocksDbWeight::get().reads(105 as Weight))
			.saturating_add(RocksDbWeight::get().reads((101 as Weight).saturating_mul(t as Weight)))
			.saturating_add(RocksDbWeight::get().writes((101 as Weight).saturating_mul(t as Weight)))
	}
	fn seal_instantiate(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((21_856_497_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(6 as Weight))
			.saturating_add(RocksDbWeight::get().reads((300 as Weight).saturating_mul(r as Weight)))
			.saturating_add(RocksDbWeight::get().writes(2 as Weight))
			.saturating_add(RocksDbWeight::get().writes((200 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_instantiate_per_input_output_kb(i: u32, o: u32, ) -> Weight {
		(18_796_671_000 as Weight)
			.saturating_add((156_269_000 as Weight).saturating_mul(i as Weight))
			.saturating_add((74_645_000 as Weight).saturating_mul(o as Weight))
			.saturating_add(RocksDbWeight::get().reads(207 as Weight))
			.saturating_add(RocksDbWeight::get().writes(202 as Weight))
			
	}
	fn seal_hash_sha2_256(r: u32, ) -> Weight {
		(132_190_000 as Weight)
			.saturating_add((319_943_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_hash_sha2_256_per_kb(n: u32, ) -> Weight {
		(747_208_000 as Weight)
			.saturating_add((421_808_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_hash_keccak_256(r: u32, ) -> Weight {
		(139_235_000 as Weight)
			.saturating_add((333_792_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_hash_keccak_256_per_kb(n: u32, ) -> Weight {
		(543_256_000 as Weight)
			.saturating_add((334_383_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_hash_blake2_256(r: u32, ) -> Weight {
		(142_704_000 as Weight)
			.saturating_add((305_513_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_hash_blake2_256_per_kb(n: u32, ) -> Weight {
		(592_813_000 as Weight)
			.saturating_add((151_270_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_hash_blake2_128(r: u32, ) -> Weight {
		(139_921_000 as Weight)
			.saturating_add((304_746_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn seal_hash_blake2_128_per_kb(n: u32, ) -> Weight {
		(544_524_000 as Weight)
			.saturating_add((151_549_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(RocksDbWeight::get().reads(4 as Weight))
			
	}
	fn instr_i64const(r: u32, ) -> Weight {
		(24_652_000 as Weight)
			.saturating_add((3_306_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64load(r: u32, ) -> Weight {
		(27_131_000 as Weight)
			.saturating_add((162_220_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64store(r: u32, ) -> Weight {
		(27_086_000 as Weight)
			.saturating_add((230_977_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_select(r: u32, ) -> Weight {
		(24_656_000 as Weight)
			.saturating_add((12_570_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_if(r: u32, ) -> Weight {
		(24_643_000 as Weight)
			.saturating_add((12_442_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_br(r: u32, ) -> Weight {
		(24_589_000 as Weight)
			.saturating_add((6_237_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_br_if(r: u32, ) -> Weight {
		(24_650_000 as Weight)
			.saturating_add((14_393_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_br_table(r: u32, ) -> Weight {
		(24_689_000 as Weight)
			.saturating_add((15_706_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_br_table_per_entry(e: u32, ) -> Weight {
		(40_129_000 as Weight)
			.saturating_add((83_000 as Weight).saturating_mul(e as Weight))
			
	}
	fn instr_call(r: u32, ) -> Weight {
		(24_904_000 as Weight)
			.saturating_add((96_429_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_call_indirect(r: u32, ) -> Weight {
		(32_540_000 as Weight)
			.saturating_add((201_773_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_call_indirect_per_param(p: u32, ) -> Weight {
		(248_700_000 as Weight)
			.saturating_add((3_705_000 as Weight).saturating_mul(p as Weight))
			
	}
	fn instr_local_get(r: u32, ) -> Weight {
		(42_081_000 as Weight)
			.saturating_add((3_548_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_local_set(r: u32, ) -> Weight {
		(42_128_000 as Weight)
			.saturating_add((3_678_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_local_tee(r: u32, ) -> Weight {
		(42_073_000 as Weight)
			.saturating_add((5_212_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_global_get(r: u32, ) -> Weight {
		(28_182_000 as Weight)
			.saturating_add((8_180_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_global_set(r: u32, ) -> Weight {
		(28_060_000 as Weight)
			.saturating_add((12_081_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_memory_current(r: u32, ) -> Weight {
		(27_113_000 as Weight)
			.saturating_add((3_802_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_memory_grow(r: u32, ) -> Weight {
		(25_521_000 as Weight)
			.saturating_add((2_288_295_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64clz(r: u32, ) -> Weight {
		(24_662_000 as Weight)
			.saturating_add((5_497_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64ctz(r: u32, ) -> Weight {
		(24_647_000 as Weight)
			.saturating_add((5_556_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64popcnt(r: u32, ) -> Weight {
		(24_646_000 as Weight)
			.saturating_add((6_138_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64eqz(r: u32, ) -> Weight {
		(24_649_000 as Weight)
			.saturating_add((5_477_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64extendsi32(r: u32, ) -> Weight {
		(24_655_000 as Weight)
			.saturating_add((5_414_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64extendui32(r: u32, ) -> Weight {
		(24_619_000 as Weight)
			.saturating_add((5_434_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i32wrapi64(r: u32, ) -> Weight {
		(24_654_000 as Weight)
			.saturating_add((5_483_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64eq(r: u32, ) -> Weight {
		(24_690_000 as Weight)
			.saturating_add((7_485_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64ne(r: u32, ) -> Weight {
		(24_652_000 as Weight)
			.saturating_add((7_468_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64lts(r: u32, ) -> Weight {
		(24_667_000 as Weight)
			.saturating_add((7_426_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64ltu(r: u32, ) -> Weight {
		(24_693_000 as Weight)
			.saturating_add((7_393_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64gts(r: u32, ) -> Weight {
		(24_675_000 as Weight)
			.saturating_add((7_407_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64gtu(r: u32, ) -> Weight {
		(24_697_000 as Weight)
			.saturating_add((7_392_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64les(r: u32, ) -> Weight {
		(24_646_000 as Weight)
			.saturating_add((7_420_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64leu(r: u32, ) -> Weight {
		(24_683_000 as Weight)
			.saturating_add((7_404_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64ges(r: u32, ) -> Weight {
		(24_685_000 as Weight)
			.saturating_add((7_461_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64geu(r: u32, ) -> Weight {
		(25_147_000 as Weight)
			.saturating_add((7_003_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64add(r: u32, ) -> Weight {
		(24_705_000 as Weight)
			.saturating_add((7_483_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64sub(r: u32, ) -> Weight {
		(24_675_000 as Weight)
			.saturating_add((7_377_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64mul(r: u32, ) -> Weight {
		(24_680_000 as Weight)
			.saturating_add((7_376_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64divs(r: u32, ) -> Weight {
		(24_660_000 as Weight)
			.saturating_add((13_091_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64divu(r: u32, ) -> Weight {
		(24_643_000 as Weight)
			.saturating_add((12_109_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64rems(r: u32, ) -> Weight {
		(24_615_000 as Weight)
			.saturating_add((13_049_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64remu(r: u32, ) -> Weight {
		(24_696_000 as Weight)
			.saturating_add((12_039_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64and(r: u32, ) -> Weight {
		(24_683_000 as Weight)
			.saturating_add((7_314_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64or(r: u32, ) -> Weight {
		(24_657_000 as Weight)
			.saturating_add((7_401_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64xor(r: u32, ) -> Weight {
		(24_661_000 as Weight)
			.saturating_add((7_347_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64shl(r: u32, ) -> Weight {
		(24_644_000 as Weight)
			.saturating_add((7_389_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64shrs(r: u32, ) -> Weight {
		(24_643_000 as Weight)
			.saturating_add((7_416_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64shru(r: u32, ) -> Weight {
		(24_634_000 as Weight)
			.saturating_add((7_392_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64rotl(r: u32, ) -> Weight {
		(24_618_000 as Weight)
			.saturating_add((7_452_000 as Weight).saturating_mul(r as Weight))
			
	}
	fn instr_i64rotr(r: u32, ) -> Weight {
		(24_618_000 as Weight)
			.saturating_add((7_447_000 as Weight).saturating_mul(r as Weight))
			
	}
	
}
