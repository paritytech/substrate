// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

//! Weights for pallet_contracts
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 2.0.0
//! DATE: 2020-10-22, STEPS: [50], REPEAT: 20, LOW RANGE: [], HIGH RANGE: []
//! EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN: Some("dev"), DB CACHE: 128
#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::Weight};
use sp_std::marker::PhantomData;

pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Trait> pallet_contracts::WeightInfo for WeightInfo<T> {
	fn update_schedule() -> Weight {
		(33_232_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	fn put_code(n: u32, ) -> Weight {
		(6_844_000 as Weight)
			.saturating_add((109_155_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn instantiate(n: u32, ) -> Weight {
		(219_061_000 as Weight)
			.saturating_add((1_007_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}
	fn call() -> Weight {
		(204_896_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn claim_surcharge() -> Weight {
		(477_902_000 as Weight)
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn seal_caller(r: u32, ) -> Weight {
		(143_631_000 as Weight)
			.saturating_add((365_636_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_address(r: u32, ) -> Weight {
		(118_492_000 as Weight)
			.saturating_add((369_221_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_gas_left(r: u32, ) -> Weight {
		(141_709_000 as Weight)
			.saturating_add((360_741_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_balance(r: u32, ) -> Weight {
		(140_527_000 as Weight)
			.saturating_add((812_428_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
	}
	fn seal_value_transferred(r: u32, ) -> Weight {
		(133_751_000 as Weight)
			.saturating_add((360_556_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_minimum_balance(r: u32, ) -> Weight {
		(142_084_000 as Weight)
			.saturating_add((360_827_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_tombstone_deposit(r: u32, ) -> Weight {
		(138_032_000 as Weight)
			.saturating_add((364_074_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_rent_allowance(r: u32, ) -> Weight {
		(134_335_000 as Weight)
			.saturating_add((847_362_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_block_number(r: u32, ) -> Weight {
		(143_470_000 as Weight)
			.saturating_add((359_234_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_now(r: u32, ) -> Weight {
		(110_683_000 as Weight)
			.saturating_add((366_837_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_weight_to_fee(r: u32, ) -> Weight {
		(139_859_000 as Weight)
			.saturating_add((607_635_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
	}
	fn seal_gas(r: u32, ) -> Weight {
		(126_750_000 as Weight)
			.saturating_add((186_677_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_input(r: u32, ) -> Weight {
		(130_342_000 as Weight)
			.saturating_add((7_817_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_input_per_kb(n: u32, ) -> Weight {
		(141_872_000 as Weight)
			.saturating_add((273_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_return(r: u32, ) -> Weight {
		(124_243_000 as Weight)
			.saturating_add((6_146_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_return_per_kb(n: u32, ) -> Weight {
		(135_913_000 as Weight)
			.saturating_add((693_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_terminate(r: u32, ) -> Weight {
		(131_065_000 as Weight)
			.saturating_add((328_649_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((2 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes((3 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_restore_to(r: u32, ) -> Weight {
		(229_433_000 as Weight)
			.saturating_add((131_743_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().reads((3 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes((4 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_restore_to_per_delta(d: u32, ) -> Weight {
		(34_315_000 as Weight)
			.saturating_add((3_736_418_000 as Weight).saturating_mul(d as Weight))
			.saturating_add(T::DbWeight::get().reads(7 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(d as Weight)))
			.saturating_add(T::DbWeight::get().writes(5 as Weight))
			.saturating_add(T::DbWeight::get().writes((100 as Weight).saturating_mul(d as Weight)))
	}
	fn seal_random(r: u32, ) -> Weight {
		(121_843_000 as Weight)
			.saturating_add((943_685_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
	}
	fn seal_deposit_event(r: u32, ) -> Weight {
		(179_024_000 as Weight)
			.saturating_add((1_339_390_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_deposit_event_per_topic_and_kb(t: u32, n: u32, ) -> Weight {
		(1_762_812_000 as Weight)
			.saturating_add((738_723_000 as Weight).saturating_mul(t as Weight))
			.saturating_add((239_832_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(t as Weight)))
			.saturating_add(T::DbWeight::get().writes((100 as Weight).saturating_mul(t as Weight)))
	}
	fn seal_set_rent_allowance(r: u32, ) -> Weight {
		(142_367_000 as Weight)
			.saturating_add((1_000_341_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}
	fn seal_set_storage(r: u32, ) -> Weight {
		(495_765_000 as Weight)
			.saturating_add((14_190_715_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			.saturating_add(T::DbWeight::get().writes((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_set_storage_per_kb(n: u32, ) -> Weight {
		(2_253_854_000 as Weight)
			.saturating_add((206_868_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
	fn seal_clear_storage(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((5_101_459_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			.saturating_add(T::DbWeight::get().writes((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_get_storage(r: u32, ) -> Weight {
		(96_455_000 as Weight)
			.saturating_add((1_070_483_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_get_storage_per_kb(n: u32, ) -> Weight {
		(864_043_000 as Weight)
			.saturating_add((149_047_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
	}
	fn seal_transfer(r: u32, ) -> Weight {
		(109_398_000 as Weight)
			.saturating_add((6_088_268_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
			.saturating_add(T::DbWeight::get().writes((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_call(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((10_518_616_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(5 as Weight))
			.saturating_add(T::DbWeight::get().reads((100 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_call_per_transfer_input_output_kb(t: u32, i: u32, o: u32, ) -> Weight {
		(10_999_892_000 as Weight)
			.saturating_add((4_878_859_000 as Weight).saturating_mul(t as Weight))
			.saturating_add((51_726_000 as Weight).saturating_mul(i as Weight))
			.saturating_add((74_930_000 as Weight).saturating_mul(o as Weight))
			.saturating_add(T::DbWeight::get().reads(105 as Weight))
			.saturating_add(T::DbWeight::get().reads((101 as Weight).saturating_mul(t as Weight)))
			.saturating_add(T::DbWeight::get().writes((101 as Weight).saturating_mul(t as Weight)))
	}
	fn seal_instantiate(r: u32, ) -> Weight {
		(0 as Weight)
			.saturating_add((22_005_757_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(6 as Weight))
			.saturating_add(T::DbWeight::get().reads((300 as Weight).saturating_mul(r as Weight)))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
			.saturating_add(T::DbWeight::get().writes((200 as Weight).saturating_mul(r as Weight)))
	}
	fn seal_instantiate_per_input_output_kb(i: u32, o: u32, ) -> Weight {
		(20_244_979_000 as Weight)
			.saturating_add((154_285_000 as Weight).saturating_mul(i as Weight))
			.saturating_add((75_529_000 as Weight).saturating_mul(o as Weight))
			.saturating_add(T::DbWeight::get().reads(207 as Weight))
			.saturating_add(T::DbWeight::get().writes(202 as Weight))
	}
	fn seal_hash_sha2_256(r: u32, ) -> Weight {
		(136_190_000 as Weight)
			.saturating_add((331_020_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_sha2_256_per_kb(n: u32, ) -> Weight {
		(979_956_000 as Weight)
			.saturating_add((421_408_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_keccak_256(r: u32, ) -> Weight {
		(137_429_000 as Weight)
			.saturating_add((334_065_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_keccak_256_per_kb(n: u32, ) -> Weight {
		(831_410_000 as Weight)
			.saturating_add((334_867_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_blake2_256(r: u32, ) -> Weight {
		(135_454_000 as Weight)
			.saturating_add((306_249_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_blake2_256_per_kb(n: u32, ) -> Weight {
		(743_003_000 as Weight)
			.saturating_add((153_589_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_blake2_128(r: u32, ) -> Weight {
		(135_316_000 as Weight)
			.saturating_add((307_428_000 as Weight).saturating_mul(r as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn seal_hash_blake2_128_per_kb(n: u32, ) -> Weight {
		(801_458_000 as Weight)
			.saturating_add((154_346_000 as Weight).saturating_mul(n as Weight))
			.saturating_add(T::DbWeight::get().reads(4 as Weight))
	}
	fn instr_i64const(r: u32, ) -> Weight {
		(24_554_000 as Weight)
			.saturating_add((3_207_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64load(r: u32, ) -> Weight {
		(26_923_000 as Weight)
			.saturating_add((160_523_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64store(r: u32, ) -> Weight {
		(26_837_000 as Weight)
			.saturating_add((229_496_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_select(r: u32, ) -> Weight {
		(24_429_000 as Weight)
			.saturating_add((12_508_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_if(r: u32, ) -> Weight {
		(24_394_000 as Weight)
			.saturating_add((12_692_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_br(r: u32, ) -> Weight {
		(24_350_000 as Weight)
			.saturating_add((6_185_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_br_if(r: u32, ) -> Weight {
		(24_482_000 as Weight)
			.saturating_add((14_324_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_br_table(r: u32, ) -> Weight {
		(24_422_000 as Weight)
			.saturating_add((19_447_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_br_table_per_entry(e: u32, ) -> Weight {
		(39_781_000 as Weight)
			.saturating_add((103_000 as Weight).saturating_mul(e as Weight))
	}
	fn instr_call(r: u32, ) -> Weight {
		(24_769_000 as Weight)
			.saturating_add((98_329_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_call_indirect(r: u32, ) -> Weight {
		(32_521_000 as Weight)
			.saturating_add((204_339_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_call_indirect_per_param(p: u32, ) -> Weight {
		(255_978_000 as Weight)
			.saturating_add((3_713_000 as Weight).saturating_mul(p as Weight))
	}
	fn instr_local_get(r: u32, ) -> Weight {
		(41_995_000 as Weight)
			.saturating_add((3_379_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_local_set(r: u32, ) -> Weight {
		(41_935_000 as Weight)
			.saturating_add((3_690_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_local_tee(r: u32, ) -> Weight {
		(41_850_000 as Weight)
			.saturating_add((5_320_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_global_get(r: u32, ) -> Weight {
		(28_040_000 as Weight)
			.saturating_add((8_228_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_global_set(r: u32, ) -> Weight {
		(27_998_000 as Weight)
			.saturating_add((12_253_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_memory_current(r: u32, ) -> Weight {
		(26_864_000 as Weight)
			.saturating_add((3_908_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_memory_grow(r: u32, ) -> Weight {
		(25_329_000 as Weight)
			.saturating_add((2_297_594_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64clz(r: u32, ) -> Weight {
		(24_381_000 as Weight)
			.saturating_add((5_498_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64ctz(r: u32, ) -> Weight {
		(24_399_000 as Weight)
			.saturating_add((5_483_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64popcnt(r: u32, ) -> Weight {
		(24_365_000 as Weight)
			.saturating_add((6_133_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64eqz(r: u32, ) -> Weight {
		(24_407_000 as Weight)
			.saturating_add((5_560_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64extendsi32(r: u32, ) -> Weight {
		(24_456_000 as Weight)
			.saturating_add((5_432_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64extendui32(r: u32, ) -> Weight {
		(24_429_000 as Weight)
			.saturating_add((5_380_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i32wrapi64(r: u32, ) -> Weight {
		(24_379_000 as Weight)
			.saturating_add((5_484_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64eq(r: u32, ) -> Weight {
		(24_400_000 as Weight)
			.saturating_add((7_413_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64ne(r: u32, ) -> Weight {
		(24_445_000 as Weight)
			.saturating_add((7_276_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64lts(r: u32, ) -> Weight {
		(24_451_000 as Weight)
			.saturating_add((7_356_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64ltu(r: u32, ) -> Weight {
		(24_400_000 as Weight)
			.saturating_add((7_367_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64gts(r: u32, ) -> Weight {
		(24_423_000 as Weight)
			.saturating_add((7_327_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64gtu(r: u32, ) -> Weight {
		(24_452_000 as Weight)
			.saturating_add((7_298_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64les(r: u32, ) -> Weight {
		(24_432_000 as Weight)
			.saturating_add((7_305_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64leu(r: u32, ) -> Weight {
		(24_425_000 as Weight)
			.saturating_add((7_365_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64ges(r: u32, ) -> Weight {
		(24_359_000 as Weight)
			.saturating_add((7_428_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64geu(r: u32, ) -> Weight {
		(24_425_000 as Weight)
			.saturating_add((7_335_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64add(r: u32, ) -> Weight {
		(24_426_000 as Weight)
			.saturating_add((7_352_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64sub(r: u32, ) -> Weight {
		(24_374_000 as Weight)
			.saturating_add((7_422_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64mul(r: u32, ) -> Weight {
		(24_430_000 as Weight)
			.saturating_add((7_328_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64divs(r: u32, ) -> Weight {
		(24_419_000 as Weight)
			.saturating_add((13_039_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64divu(r: u32, ) -> Weight {
		(24_397_000 as Weight)
			.saturating_add((11_990_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64rems(r: u32, ) -> Weight {
		(24_443_000 as Weight)
			.saturating_add((12_930_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64remu(r: u32, ) -> Weight {
		(24_361_000 as Weight)
			.saturating_add((12_062_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64and(r: u32, ) -> Weight {
		(24_434_000 as Weight)
			.saturating_add((7_303_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64or(r: u32, ) -> Weight {
		(24_370_000 as Weight)
			.saturating_add((7_327_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64xor(r: u32, ) -> Weight {
		(24_359_000 as Weight)
			.saturating_add((7_402_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64shl(r: u32, ) -> Weight {
		(24_450_000 as Weight)
			.saturating_add((7_325_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64shrs(r: u32, ) -> Weight {
		(24_406_000 as Weight)
			.saturating_add((7_378_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64shru(r: u32, ) -> Weight {
		(24_407_000 as Weight)
			.saturating_add((7_366_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64rotl(r: u32, ) -> Weight {
		(24_418_000 as Weight)
			.saturating_add((7_350_000 as Weight).saturating_mul(r as Weight))
	}
	fn instr_i64rotr(r: u32, ) -> Weight {
		(24_418_000 as Weight)
			.saturating_add((7_379_000 as Weight).saturating_mul(r as Weight))
	}
}
